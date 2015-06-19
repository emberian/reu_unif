use std;
use std::collections::BTreeMap;
use std::cell::{RefCell, Cell};
use std::rc::Rc;

const P_FUNC: u32 = 0;
const E_FUNC: u32 = 1;
#[allow(dead_code)]
const MAGIC_FUNC: u32 = 2;

const PX_VAR: u32 = 0;
const PY_VAR: u32 = 1;
const EM_VAR: u32 = 2;
const EK_VAR: u32 = 3;

// TODO:
//
// Add destructors for pairing: p(x, y) |- x, y
// and encryption: e(x, y), y |- x, y
//
// Handle destructor decomposition by looking at each rule, then start pulling subsets out of the
// cap, matching (it's syntactic matching?) against the destructor hypothesis...
#[derive(Eq, PartialEq, Hash, Clone, Debug, PartialOrd, Ord)]
pub enum SigmaTerm {
    Var(u32),
    Func(u32, Vec<SigmaTerm>),
}

impl SigmaTerm {
    pub fn subst(&self, s: &Subst) -> Option<CapTerm> {
        match *self {
            SigmaTerm::Var(x) => {
                let mut res = s.get(&x).map(|x| x.clone());
                if res.is_none() {
                    error!("No substitution for {} in {:?}", x, s);
                }
                match res {
                    Some(CapTerm::Intersection(ref mut ts)) if ts.len() == 1 => {
                        Some(ts.swap_remove(0))
                    },
                    other => other
                }
            }
            SigmaTerm::Func(x, ref ts) => {
                let mut res = Vec::with_capacity(ts.len());
                for t in ts {
                    match t.subst(s) {
                        Some(t) => res.push(t),
                        None => return None,
                    }
                }
                Some(CapTerm::Func(x, res))
            }
        }
    }

    pub fn to_cap(&self) -> Option<CapTerm> {
        match *self {
            SigmaTerm::Var(_) => None,
            SigmaTerm::Func(x, ref ts) => {
                let mut res = Vec::with_capacity(ts.len());
                for t in ts {
                    match t.to_cap() {
                        Some(t) => res.push(t),
                        None => return None,
                    }
                }
                Some(CapTerm::Func(x, res))
            }
        }
    }
}

impl std::fmt::Display for SigmaTerm {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match *self {
            SigmaTerm::Var(x) => write!(f, "'{}", x),
            SigmaTerm::Func(x, ref args) =>
                if args.len() > 0 {
                    write!(f, "{}({})", x, args.iter().map(|x| format!("{}", x)).collect::<Vec<_>>().connect(", "))
                } else {
                    write!(f, "{}", x)
                }
        }
    }
}

#[derive(Eq, PartialEq, Hash, Clone, Debug, PartialOrd, Ord)]
pub enum CapTerm {
    Union(Vec<CapTerm>),
    Intersection(Vec<CapTerm>),
    Func(u32, Vec<CapTerm>),
    Cap(Box<CapTerm>),
}

impl std::fmt::Display for CapTerm {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match *self {
            CapTerm::Union(ref args) => f.write_str(&args.iter().map(|x| format!("{}", x)).collect::<Vec<_>>().connect(" | ")),
            CapTerm::Intersection(ref args) => f.write_str(&args.iter().map(|x| format!("{}", x)).collect::<Vec<_>>().connect(" & ")),
            CapTerm::Func(x, ref args) =>
                if args.len() > 0 {
                    write!(f, "{}({})", x, args.iter().map(|x| format!("{}", x)).collect::<Vec<_>>().connect(", "))
                } else {
                    write!(f, "{}", x)
                },
            CapTerm::Cap(ref arg) => write!(f, "Cap({})", arg),
        }
    }
}

impl CapTerm {
    fn push(&mut self, t: CapTerm) {
        match *self {
            CapTerm::Union(ref mut ts) => ts.push(t),
            CapTerm::Intersection(ref mut ts) => ts.push(t),
            CapTerm::Cap(..) => panic!("Tried to push into a CapTerm::Cap"),
            CapTerm::Func(..) => panic!("Tried to push into a CapTerm::Func"),
        }
    }

    pub fn un(&mut self) -> &mut Vec<CapTerm> {
        match *self {
            CapTerm::Union(ref mut ts) => ts,
            CapTerm::Intersection(..) => panic!("Tried to un a CapTerm::Intersection"),
            CapTerm::Cap(..) => panic!("Tried to un a CapTerm::Cap"),
            CapTerm::Func(..) => panic!("Tried to un a CapTerm::Func"),
        }
    }

    fn contains_function(&self, fs: u32) -> bool {
        match *self {
            CapTerm::Union(ref ts) => ts.iter().any(|t| t.contains_function(fs)),
            CapTerm::Intersection(ref ts) => ts.iter().any(|t| t.contains_function(fs)),
            CapTerm::Cap(ref t) => t.contains_function(fs),
            CapTerm::Func(fx, _) => fx == fs,
        }
    }
}

pub type Subst = BTreeMap<u32, CapTerm>;
type Sub = Rc<RefCell<Option<Subst>>>;
pub struct Context {
    // "interpreted" constructors - of the form:
    // func name => Conclusions |- Hypothesis.
    // If we don't have an entry here, we assume that we can infer the arguments.
    // TODO: Why do we only consider the case where there is a single conclusion?
    constructors: BTreeMap<u32, (SigmaTerm, Vec<SigmaTerm>)>,
    level: Cell<u32>,
    // max_func: u32,
    // "interpreted" destructors. List of rules eqv. to the form "Hypotheses |- Conclusions"
    destructors: Vec<(Vec<SigmaTerm>, Vec<SigmaTerm>)>,
    substs: RefCell<Vec<Sub>>,
}

// FIXME: backtracking like this is ultra inefficient. Consider using a HAMT-backed persistent map,
// or having capmatch push into a (possibly empty) list of "insert these things for me please",
// but we probably want a HAMT as backtracking can go quite deep.

impl Context {
    pub fn new() -> Context {
        Context {
            constructors: BTreeMap::new(),
            destructors: vec![
                (vec![SigmaTerm::Func(P_FUNC, vec![SigmaTerm::Var(PX_VAR), SigmaTerm::Var(PY_VAR)])],
                 vec![SigmaTerm::Var(PX_VAR), SigmaTerm::Var(PY_VAR)]),
                (vec![SigmaTerm::Func(E_FUNC, vec![SigmaTerm::Var(EM_VAR), SigmaTerm::Var(EK_VAR)]),
                      SigmaTerm::Var(EK_VAR)],
                 vec![SigmaTerm::Var(EM_VAR), SigmaTerm::Var(EK_VAR)]),
            ],
            level: Cell::new(0),
            substs: RefCell::new(Vec::new()),
        }
    }

    fn log(&self, msg: &str) {
        info!("{}{}", std::iter::repeat("  ").take(self.level.get() as usize).collect::<Vec<_>>().concat(), msg);
    }

    fn enter(&self) {
        self.level.set(self.level.get() + 1)
    }

    fn leave(&self) {
        self.level.set(self.level.get() - 1)
    }

    fn copy(&self, s: Sub) -> Sub {
        let save = Rc::new(RefCell::new(s.borrow().clone()));
        self.substs.borrow_mut().push(save.clone());
        save
    }

    pub fn match_(&self, s: &SigmaTerm, t: &CapTerm) -> Vec<Subst> {
        let into = Rc::new(RefCell::new(Some(BTreeMap::new())));
        *self.substs.borrow_mut() = vec![into.clone()];
        self.capmatch(s, t, into);
        let mut x = Vec::new();
        std::mem::swap(&mut *self.substs.borrow_mut(), &mut x);
        let mut res = Vec::new();
        for s in x {
            match *s.borrow() {
                Some(ref x) => res.push((&*x).clone()),
                None => { }
            }
        }
        res
    }

    fn capmatch(&self, s: &SigmaTerm, t: &CapTerm, into: Sub) -> bool {
        self.log(&format!("Matching {} against {}", s, t));
        self.enter();
        let res = match (s, t) {
            (&SigmaTerm::Func(sf, _), &CapTerm::Func(cf, _)) if sf != cf => {
                self.log("Clash");
                *into.borrow_mut() = None;
                // clash
                false
            },
            (&SigmaTerm::Func(_, ref sargs), &CapTerm::Func(_, ref cargs)) => {
                self.log("Decomposing...");
                self.enter();
                // decomp
                let save = into.borrow().clone();
                for (sarg, carg) in sargs.iter().zip(cargs) {
                    if !self.capmatch(sarg, carg, into.clone()) {
                        *into.borrow_mut() = save; // backtrack
                        self.leave();
                        return false;
                    }
                }
                self.leave();
                true
            },
            (_, &CapTerm::Union(ref stuffs)) => {
                self.log("Splitting...");
                self.enter();
                // split
                let mut any = false;
                for un in stuffs {
                    if self.capmatch(s, un, self.copy(into.clone())) {
                        any = true;
                    }
                }
                *into.borrow_mut() = None; // Toss the original substitution out, we've split.
                self.leave();
                any
            },
            (&SigmaTerm::Var(x), _) => {
                self.log("Solved for a variable");
                // No rule for this, but we've solved for x.
                into.borrow_mut().as_mut().unwrap().entry(x).or_insert(CapTerm::Intersection(Vec::with_capacity(2))).push(t.clone());
                true
            }
            (_, &CapTerm::Cap(ref capset)) => {
                let a = if let &SigmaTerm::Func(sf, ref sargs) = s {
                    self.log("Constructor decomposing...");
                    self.enter();
                    // constr decomp
                    // The sigma in C\sigma here is not important; this looks just like a normal
                    // function construction. If we add "interpreted constructors" (whatever that
                    // might mean), we should handle this more carefully.
                    let mut all = true;
                    let a = if self.constructors.contains_key(&sf) {
                        // TODO
                        error!("Interpreted constructor unhandled");
                        false
                    } else {
                        let save = self.copy(into.clone());
                        for arg in sargs {
                           if !self.capmatch(arg, t, save.clone()) {
                               all = false;
                               break
                           }
                        }
                        // We split, but later we want to still use into later in destructor
                        // decomp.
                        let res = self.capmatch(s, capset, self.copy(into.clone()));
                        all || res
                    };
                    self.leave();
                    a
                } else {
                    false
                };
                // destr decomp
                let mut b = false;
                if let &CapTerm::Union(ref terms) = &**capset {
                    self.enter();
                    // try to find a destructor instantiation in the capset.
                    'outer: for dtor in &self.destructors {
                        // We need to make sure the hypotheses unify with the same substitution.
                        // Implementation strategy: designate particular element (first, here) as
                        // "strongest". Do matching with that element. Apply resulting substitution
                        // to the other conclusions, then check if they are also members of the
                        // capset. If all are, then we select this substitution as valid.

                        let strongest = &dtor.0[0];

                        // Early reject: if the strongest is a function application, and that
                        // function symbol does not appear explicitly, then we can skip this one.
                        if let &SigmaTerm::Func(fsym, _) = strongest {
                            if !capset.contains_function(fsym) {
                                continue;
                            }
                        }

                        self.log(&format!("Destructor decomposing against {:?}", dtor));

                        let res = self.match_(strongest, capset);
                        if res.len() > 0 {
                            self.log("Found something that works for this dtor!");
                            let mut splits = Vec::new(); // all the subproblems we will need to solve.
                            'inner: for subst in res {
                                // apply the subst to everything in the hypotheses and remove it
                                // from leftovers. if it's not in leftovers, bail.
                                //
                                // TODO: determine if each clause in the hypothesis MUST appear
                                // uniquely in the capset, or whether duplicates are legal. Not
                                // relevant in our current ruleset.
                                let mut leftovers = terms.clone();
                                for hyp in &dtor.0 {
                                    match leftovers.iter().position(|x| x == &hyp.subst(&subst).expect("substitution was partial!")) {
                                        Some(idx) => { leftovers.swap_remove(idx); },
                                        None => { warn!("Couldn't find {:?} in {:?}", hyp.subst(&subst), leftovers); continue 'inner; }
                                    }
                                }
                                // now apply to the subst to the conclusions and add to the
                                // leftovers
                                for conc in &dtor.1 {
                                    leftovers.push(conc.subst(&subst).expect("substitution was partial 2!"));
                                }
                                // done! solve this later.
                                splits.push(CapTerm::Cap(Box::new(CapTerm::Union(leftovers))));
                            }
                            if splits.len() > 0 {
                                // I suspect this is rarely if ever applicable!
                                splits.sort();
                                let prelen = splits.len();
                                splits.dedup();
                                if prelen != splits.len() {
                                    info!("Was able to deduplicate the splits in destr decomp");
                                }
                                for split in splits {
                                    b |= self.capmatch(s, &split, self.copy(into.clone()));
                                }
                            }
                        }
                    }
                    self.leave();
                }
                if a || b {
                    *into.borrow_mut() = None; // Toss the original substitution out, we've split somewhere.
                }
                a || b
            }

            crap => panic!("The ruleset is not complete! capmatch saw {:?} but didn't handle it", crap),
        };
        if res {
            self.log("This branch success!")
        } else {
            self.log("This branch fail!")
        }
        self.leave();
        res
    }
}
