use std::collections::HashMap;
use std::iter::IntoIterator;

#[derive(Eq, PartialEq, Hash, Clone, Debug)]
enum SigmaTerm {
    Var(u32),
    Func(u32, Vec<SigmaTerm>),
}

#[derive(Eq, PartialEq, Hash, Clone, Debug)]
enum CapTerm {
    Union(Vec<CapTerm>),
    Intersection(Vec<CapTerm>),
    Func(u32, Vec<CapTerm>),
    Cap(Box<CapTerm>),
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
}

type Subst = HashMap<u32, CapTerm>;

struct Context {
    // Functions we can introduce, and their arity.
    constructors: HashMap<u32, usize>,
    // max_func: u32,
    // List of rules eqv. to the form "Hypothesis |- Conclusion"
    // destructors: Vec<(Vec<SigmaTerm>, Vec<SigmaTerm>)>,
}

// FIXME: backtracking like this is ultra inefficient. Consider using a HAMT-backed persistent map,
// or having capmatch push into a (possibly empty) list of "insert these things for me please",
// but we probably want a HAMT as backtracking can go quite deep.

impl Context {
    fn capmatch(&self, s: &SigmaTerm, t: &CapTerm, into: &mut Subst) -> bool {
        match (s, t) {
            (&SigmaTerm::Func(sf, _), &CapTerm::Func(cf, _)) if sf != cf => {
                // clash
                false
            },
            (&SigmaTerm::Func(_, ref sargs), &CapTerm::Func(_, ref cargs)) => {
                // decomp
                for (sarg, carg) in sargs.iter().zip(cargs) {
                    let save = into.clone();
                    if !self.capmatch(sarg, carg, into) {
                        *into = save; // backtrack
                        return false;
                    }
                }
                true
            },
            (&SigmaTerm::Func(sf, ref sargs), &CapTerm::Cap(ref capset)) if self.constructors.contains_key(&sf) => {
                // constr decomp
                // I'm not sure if the "sigma" in "C sigma" is important. What it means is that we
                // have an instantiation of one of the rules, which... looks a lot like a normal
                // function application! One thing to note is that the sigma may not be complete,
                // and thus `sargs` could have unbound variables that came from the rule, but I
                // also think that's not an important detail.
                let mut all = true;
                let save = into.clone();
                for arg in sargs {
                   if !self.capmatch(arg, t, into) {
                       *into = save; // backtrack
                       all = false;
                       break
                   }
                }
                let save = into.clone();
                if !self.capmatch(s, capset, into) {
                    *into = save; // backtrack
                    false
                } else {
                    all
                }
            },
            (_, &CapTerm::Union(ref stuffs)) => {
                // split
                let mut any = false;
                for un in stuffs {
                    let save = into.clone();
                    if !self.capmatch(s, un, into) {
                        *into = save;
                    } else {
                        any = true;
                    }
                }
                any
            },
            (&SigmaTerm::Var(x), _) => {
                // No rule for this, but we've solved for x.
                into.entry(x).or_insert(CapTerm::Intersection(Vec::with_capacity(2))).push(t.clone());
                true
            }
            (&SigmaTerm::Func(_, ref fargs), &CapTerm::Cap(ref capset)) => {
                // Cap decomp
                // This isn't a rule anymore, to handle destructors, but the actual destructor rule
                // is SO AWFUL that I can't bear to implement it yet.
                let save = into.clone();
                let mut a = true;
                for arg in fargs {
                    if !self.capmatch(arg, t, into) {
                        a = false;
                        *into = save;
                        break;
                    }
                }
                let save = into.clone();
                let mut b = true;
                if !self.capmatch(s, capset, into) {
                    *into = save;
                    b = true;
                }
                a || b
            }
            /*
            (_, &CapTerm::Cap(ref capset)) => {
                // destr decomp
                // See above comments about sigma. Additionally, I'm not *quite* sure why each
                // sigma isn't unique... In this case, we care a lot about what sigma actually is
                // because that determines how we substitute back into the hypothesis!
                //
                // We implement this right now by checking, for each rule, whether it's possible to
                // match some selection of terms from the Cap set against the conclusion.
                //
                // This sucks a lot.
                let mut relevant_rules = self.destructors.iter().filter(|(h, c)| c.len() <= capset.len());
                for term in capset {
                    if let &CapTerm::Func(fc, args) = term {

                    }
                }
            }
            */

            crap => panic!("The ruleset is not complete! capmatch saw {:?} but didn't handle it", crap),
        }
    }
}

fn main() {
    let c = Context {
        constructors: vec![(0, 0), (1, 0), (2, 1), (3, 1), (4, 2), (5, 3)].into_iter().collect()
    };
    let mut final_subst = HashMap::new();
    // f(a, x) c? Cap(f(a, f(a, a)) u b)
    c.capmatch(&SigmaTerm::Func(2, vec![SigmaTerm::Func(0, vec![]), SigmaTerm::Var(0)]),
               &CapTerm::Cap(Box::new(CapTerm::Union(vec![CapTerm::Func(2, vec![CapTerm::Func(0, vec![]), CapTerm::Func(2, vec![CapTerm::Func(0, vec![]), CapTerm::Func(0, vec![])])]), CapTerm::Func(1, vec![])]))),
               &mut final_subst);
    println!("Substitution is: {:?}", final_subst);
    // x -> f(a, a) ??? Should be x -> Cap(b u f(a, a)) I think...
}
