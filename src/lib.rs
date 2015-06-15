#[macro_use]
extern crate log;

use std::collections::BTreeMap;
use std::cell::{RefCell, Cell};
use std::rc::Rc;

pub mod parse;

const P_FUNC: u32 = 0;
const E_FUNC: u32 = 1;

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
    fn subst(&self, s: &Subst) -> Option<CapTerm> {
        match *self {
            SigmaTerm::Var(x) => {
                let res = s.get(&x).map(|x| x.clone());
                if res.is_none() {
                    error!("No substitution for {} in {:?}", x, s);
                }
                res
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

    #[allow(dead_code)]
    fn un(&mut self) -> &mut Vec<CapTerm> {
        match *self {
            CapTerm::Union(ref mut ts) => ts,
            CapTerm::Intersection(..) => panic!("Tried to un a CapTerm::Intersection"),
            CapTerm::Cap(..) => panic!("Tried to un a CapTerm::Cap"),
            CapTerm::Func(..) => panic!("Tried to un a CapTerm::Func"),
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
                    let save = Rc::new(RefCell::new(into.borrow().clone()));
                    self.substs.borrow_mut().push(save.clone());
                    if self.capmatch(s, un, save) {
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
                    // I'm not sure if the "sigma" in "C sigma" is important. What it means is that we
                    // have an instantiation of one of the rules, which... looks a lot like a normal
                    // function application! One thing to note is that the sigma may not be complete,
                    // and thus `sargs` could have unbound variables that came from the rule, but I
                    // also think that's not an important detail.
                    let mut all = true;
                    if self.constructors.contains_key(&sf) {
                        // TODO
                        error!("Interpreted constructor unhandled");
                        false
                    } else {
                        let save = Rc::new(RefCell::new(into.borrow().clone()));
                        self.substs.borrow_mut().push(save.clone());
                        for arg in sargs {
                           if !self.capmatch(arg, t, save.clone()) {
                               all = false;
                               break
                           }
                        }
                        let res = self.capmatch(s, capset, into.clone());
                        self.leave();
                        all || res
                    }
                } else {
                    false
                };
                // destr decomp
                // See above comments about sigma. Additionally, I'm not *quite* sure why each
                // sigma isn't unique... In this case, we care a lot about what sigma actually is
                // because that determines how we substitute back into the hypothesis!
                //
                // This sucks a lot :(.
                let mut b = false;
                if false /*let &CapTerm::Union(ref terms) = &**capset*/ {
                    // DISABLED UNTIL PROBLEMS WORKED OUT.
                    let terms = &Vec::new();
                    self.log("Destructor decomposing...");
                    self.enter();
                    // try to find a constructor instantiation in the capset.
                    let mut any_overall = false;
                    'outer: for dtor in &self.destructors {
                        // TODO: Make sure they unify with the same substitution?
                        // Yes, we definitely need to make sure they unify with the same
                        // substitution. This is completely incorrect until then. Implementation
                        // strategy: designate particular element as "strongest". Do matching with
                        // that element. Apply resulting substitution to the other conclusions,
                        // then check if they are also members of the capset. If all are, then we
                        // select this substitution as valid.
                        //
                        // Open questions: substitution will result in a Cap-term. How to check if
                        // a Cap term is a subset of another Cap term? Must it be a subset, or do
                        // merely some elements work? Do we need to do Cap unification, or merely
                        // solve the word problem?
                        //
                        // I'm still a bit confused about this, but it's too late for me to think
                        // straight...
                        let mut leftovers = terms.clone();
                        let mut substs = Vec::new();
                        let mut any = false;
                        for conc in &dtor.0 {
                            self.log(&format!("Looking at constructor {}", conc));
                            let res = self.match_(conc, capset);
                            if res.len() > 0 {
                                any = true;
                                if res.len() != 1 {
                                    error!("When matching {:?} against {:?} in destr decomp, we got multiple substitutions: {:?}",
                                        conc, terms, res);
                                }
                                match leftovers.iter().position(|x| x == &conc.subst(&res[0]).expect("substitution was partial!")) {
                                    Some(idx) => { leftovers.swap_remove(idx); },
                                    None => { }
                                }
                                substs.extend(res); // ??? Do we need to pick?
                            }
                        }
                        if any {
                            any_overall = true;
                            // TODO: do we need to pick a particular substitution? I think we need
                            // to try all of them...
                            substs.sort();
                            substs.dedup();
                            for subst in substs {
                                let save = Rc::new(RefCell::new(into.borrow().clone()));
                                self.substs.borrow_mut().push(save.clone());
                                let mut new = leftovers.clone();
                                for hypoth in &dtor.1 {
                                    new.push(hypoth.subst(&subst).expect("substitution was partial!"));
                                }
                                b |= self.capmatch(s, &CapTerm::Cap(Box::new(CapTerm::Union(new))), save.clone());
                            }
                        }
                    }
                    if any_overall {
                        *into.borrow_mut() = None; // Toss the original substitution out, we've split.
                    }
                    self.leave();
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
