use std::collections::HashMap;
//use std::collections::hash_map::{Entry, OccupiedEntry};
use std::iter::IntoIterator;
use Term::*;

//mod parse;

#[derive(Eq, PartialEq, Hash, Clone, Debug)]
enum Term {
    Var(u32),
    Func(u32, Vec<Term>),
}

impl Term {
    fn occurs_in(&self, other: &Term) -> bool {
        if self == other {
            true
        } else {
            if let &Func(_, ref args) = other {
                args.iter().any(|arg| self.occurs_in(arg))
            } else {
                false
            }
        }
    }
}

#[derive(Eq, PartialEq, Clone, Debug)]
struct Subst {
    substs: HashMap<Term, Term>,
}

impl Subst {
    fn dom(&self) -> Vec<Term> {
        self.substs.keys().cloned().collect()
    }

    fn ran(&self) -> Vec<Term> {
        self.substs.values().cloned().collect()
    }

    fn apply(&self, term: &Term) -> Term {
        match term {
            c @ &Var(_) => self.substs.get(&c).map(|x| x.clone()).unwrap_or(c.clone()),
            &Func(f, ref terms) => { Func(f, terms.iter().map(|x| self.apply(x)).collect()) }
        }
    }

    fn remove_trivial(&mut self) {
        let mut to_remove = Vec::new();
        for (k, v) in &self.substs {
            if k == v {
                to_remove.push(k.clone());
            }
        }
        for k in to_remove {
            self.substs.remove(&k);
        }
    }

    fn compose(mut self, mut other: Subst) -> Subst {
        for (_, v) in &mut self.substs {
            *v = other.apply(v)
        }

        for t in self.substs.keys() {
            other.substs.remove(t);
        }

        self.remove_trivial();

        for (k, v) in other.substs {
            self.substs.insert(k, v);
        }

        self
    }

    fn map(&mut self, t: Term, u: Term) {
        self.substs.insert(t, u);
    }
}

fn syntactic_unify(s: Term, t: Term) -> Option<Subst> {
    fn unify(mut s: Term, mut t: Term, subst: &mut Subst) -> bool {
        if let Var(_) = s {
            s = subst.apply(&s);
        }
        if let Var(_) = t {
            t = subst.apply(&t);
        }

        if let Var(_) = s {
            std::mem::swap(&mut s, &mut t);
        }

        match (s, t) {
            (Var(sv), Var(tv)) if sv == tv => { }
            (Func(sf, sargs), Func(tf, targs)) => {
                if sf == tf {
                    for (a, b) in sargs.into_iter().zip(targs) {
                        if !unify(a, b, subst) {
                            return false;
                        }
                    }
                } else {
                    return false;
                }
            },
            (s, t) => {
                if s.occurs_in(&t) {
                    return false;
                } else {
                    subst.map(s, t);
                }
            }
        }

        true
    }

    let mut subst = Subst { substs: HashMap::new() };
    if unify(s, t, &mut subst) {
        return Some(subst)
    } else {
        return None
    }
}

fn main() {
    use Term::*;
    let s = Func(0, vec![Func(1, vec![Var(0), Var(1)]), Var(0)]);
    let t = Func(0, vec![Var(2)]);
    println!("{:?}", syntactic_unify(s, t));
}
