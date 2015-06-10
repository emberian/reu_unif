use std::collections::HashMap;

pub struct Parser {
    vars: HashMap<String, u32>,
    syms: HashMap<String, u32>,
    funcs: HashMap<String, u32>,
}

enum State {
    Initial,
    EatingVar,
    EatingSym,
    EatingFunc,
}

impl Parser {
    pub fn new() -> Parser {
        Parser { vars: HashMap::new(), syms: HashMap::new(), funcs: HashMap::new() }
    }

    pub fn parse(&mut self, x: &str) -> ::Term {
        //let mut term;
        let mut state = State::Initial;

        let mut it = x.char_indices();

        while let Some((idx, c)) = it.next() {
            match c {
                c if c.is_uppercase() => {
                    let var_id = self.vars.len() as u32;
                    let mut last = it.by_ref().skip_while(|&(i, c)| c.is_alphanumeric());
                    let name = String::from(&x[idx..]last.next().map(|(x, c)| x).unwrap_or(x.len()));
                    self.vars.insert(name, var_id);
                },
                c if c.is_lowercase() => {
                    let var_id = self.syms.len() as u32;
                    let mut last = it.by_ref().skip_while(|&(i, c)| c.is_alphanumeric());
                    let name = String::from(&x[idx..last.next().map(|(x, c)| x).unwrap_or(x.len()));
                    self.syms.insert(String::from(&x[idx..last.next().map(|(x, c)| x).unwrap_or(x.len())]), var_id);
                },
                _ => { }
            }
        }

        ::Term::Var(0)
    }
}
