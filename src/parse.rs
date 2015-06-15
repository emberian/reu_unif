use std::collections::HashMap;
use std::iter::Peekable;

use self::Token::*;

#[derive(Debug, PartialEq, Eq)]
pub enum Token {
    Word(String, bool),
    LParen,
    RParen,
    Dot,
    Comma,
    Cap,
}

impl Token {
    fn is_word(&self, s: &str) -> bool {
        match *self {
            Word(ref t, _) => s == t,
            _ => false
        }
    }
}

pub struct Lexer<I: Iterator<Item=char>> {
    it: Peekable<I>,
}

fn is_toksep(c: char) -> bool {
    c == '(' || c == ')' || c == ',' || c == '.' || c.is_whitespace()
}

impl<I: Iterator<Item=char>> Lexer<I> {
    pub fn new(i: I) -> Lexer<I> {
        Lexer {
            it: i.peekable()
        }
    }

    fn eat_word(&mut self) -> Token {
        let mut acc = String::new();
        while !is_toksep(*self.it.peek().unwrap_or(&'.')) {
            acc.push(self.it.next().unwrap());
        }
        let c = !acc.chars().next().unwrap().is_lowercase();
        if "Cap" == acc {
            Cap
        } else {
            Word(acc, c)
        }
    }
}

impl<I: Iterator<Item=char>> Iterator for Lexer<I> {
    type Item = Token;

    fn next(&mut self) -> Option<Token> {
        while let Some(&c) = self.it.peek() {
            if c.is_whitespace() { self.it.next(); continue }
            if !is_toksep(c) {
                return Some(self.eat_word());
            } else {
                match self.it.next().unwrap() {
                    '(' => return Some(LParen),
                    ')' => return Some(RParen),
                    '.' => return Some(Dot),
                    ',' => return Some(Comma),
                    _ => unreachable!()
                }
            }
        }
        None
    }
}


pub struct Parser<I: Iterator<Item=char>> {
    pub vars: Vec<String>,
    pub funcs: Vec<String>,
    vars_inverse: HashMap<String, u32>,
    funcs_inverse: HashMap<String, u32>,
    arities: Vec<u32>,
    l: Peekable<Lexer<I>>,
}

#[derive(Debug, PartialEq, Eq)]
pub enum ParseError {
    ArityMismatch(String),
    Done,
    BadSyntax(Token, String),
    WantedMore,
}

// A -> B A'
// A' -> ∪ A | epsilon
// B -> C B'
// B' -> ∩ B | epsilon
// C -> Word | Word ( Args ) | Cap ( A )
// Args -> A Args'
// Args' -> ',' Args | epsilon

impl<I: Iterator<Item=char>> Parser<I> {
    fn intern(&mut self, n: String, is_const: bool) -> u32 {
        if is_const {
            let mut new = false;
            let l = match self.funcs_inverse.get(&n) {
                Some(n) => *n,
                None => { new = true; self.funcs.push(n.clone()); self.arities.push(0); self.funcs.len() as u32 - 1 }
            };
            if new {
                self.funcs_inverse.insert(n, l);
            }
            l
        } else {
            let mut new = false;
            let l = match self.vars_inverse.get(&n) {
                Some(n) => *n,
                None => { new = true; self.vars.push(n.clone()); self.vars.len() as u32 - 1 }
            };
            if new {
                self.funcs_inverse.insert(n, l);
            }
            l
        }
    }

    pub fn eat(&mut self, t: Token) -> Result<(), ParseError> {
        if self.l.peek() == Some(&t) {
            self.l.next();
            Ok(())
        } else {
            Err(ParseError::BadSyntax(self.l.next().unwrap_or(Dot), format!("Expected {:?}", t)))
        }
    }

    pub fn new(i: I) -> Parser<I> {
        let mut p = Parser {
            vars: Vec::new(),
            funcs: Vec::new(),
            vars_inverse: HashMap::new(),
            funcs_inverse: HashMap::new(),
            arities: Vec::new(),
            l: Lexer::new(i).peekable(),
        };
        p.intern("p".into(), true);
        p.arities.push(2);
        p.intern(".px.".into(), false);
        p.intern(".py.".into(), false);
        p.intern("e".into(), true);
        p.arities.push(2);
        p.intern(".em.".into(), false);
        p.intern(".ek.".into(), false);
        p
    }

    pub fn parse_cap_term(&mut self) -> Result<::CapTerm, ParseError> {
        let mut un = vec![try!(self.parse_cap_b())];
        while self.l.peek().map_or(false, |t| t.is_word("|")) {
            self.l.next();
            un.push(try!(self.parse_cap_b()));
        }
        if un.len() == 1 {
            Ok(un.swap_remove(0))
        } else {
            Ok(::CapTerm::Union(un))
        }
    }

    fn parse_cap_b(&mut self) -> Result<::CapTerm, ParseError> {
        let mut un = vec![try!(self.parse_cap_c())];
        while self.l.peek().map_or(false, |t| t.is_word("&")) {
            self.l.next();
            un.push(try!(self.parse_cap_c()));
        }
        if un.len() == 1 {
            Ok(un.swap_remove(0))
        } else {
            Ok(::CapTerm::Union(un))
        }
    }

    fn parse_cap_c(&mut self) -> Result<::CapTerm, ParseError> {
        match self.l.next() {
            Some(Word(name, _)) => {
                if self.l.peek() == Some(&LParen) {
                    try!(self.eat(LParen));
                    let fs = self.intern(name, true);
                    let mut args = Vec::new();
                    while self.l.peek() != Some(&RParen) {
                        args.push(try!(self.parse_cap_term()));
                        if self.l.peek() != Some(&RParen) {
                            try!(self.eat(Comma));
                        }
                    }
                    if self.arities[fs as usize] == 0 {
                        self.arities[fs as usize] = args.len() as u32;
                    } else if self.arities[fs as usize] != args.len() as u32 {
                        return Err(ParseError::ArityMismatch(format!("in call to {}, expected {} arguments by earlier usage, got {}",
                                                                     self.funcs[fs as usize], self.arities[fs as usize], args.len())));
                    }
                    try!(self.eat(RParen));
                    Ok(::CapTerm::Func(fs, args))
                } else {
                    Ok(::CapTerm::Func(self.intern(name, true), vec![]))
                }
            },
            Some(Dot) => return Err(ParseError::Done),
            Some(Cap) => {
                try!(self.eat(LParen));
                let t = ::CapTerm::Cap(Box::new(try!(self.parse_cap_term())));
                try!(self.eat(RParen));
                Ok(t)
            },
            Some(t) => Err(ParseError::BadSyntax(t, "expected a function, variable, or .".into())),
            None => Err(ParseError::WantedMore),
        }
    }

    pub fn parse_sigma_term(&mut self) -> Result<::SigmaTerm, ParseError> {
        match self.l.next() {
            Some(Word(name, is_const)) => {
                if self.l.peek() == Some(&LParen) {
                    try!(self.eat(LParen));
                    let fs = self.intern(name, true);
                    let mut args = Vec::new();
                    while self.l.peek() != Some(&RParen) {
                        args.push(try!(self.parse_sigma_term()));
                        if self.l.peek() != Some(&RParen) {
                            try!(self.eat(Comma));
                        }
                    }
                    if self.arities[fs as usize] == 0 {
                        self.arities[fs as usize] = args.len() as u32;
                    } else if self.arities[fs as usize] != args.len() as u32 {
                        return Err(ParseError::ArityMismatch(format!("expected {} arguments to {} by earlier usage, got {}", self.funcs[fs as usize], self.arities[fs as usize], args.len())));
                    }
                    try!(self.eat(RParen));
                    Ok(::SigmaTerm::Func(fs, args))
                } else {
                    Ok(::SigmaTerm::Var(self.intern(name, is_const)))
                }
            },
            Some(Dot) => return Err(ParseError::Done),
            Some(t) => Err(ParseError::BadSyntax(t, "expected a function, variable, or .".into())),
            None => Err(ParseError::WantedMore),
        }
    }

    pub fn print_cap_term(&self, t: &::CapTerm) {
        match *t {
            ::CapTerm::Union(ref args) => {
                for arg in args.iter().take(args.len()-1) {
                    self.print_cap_term(arg);
                    print!(" | ");
                }
                self.print_cap_term(args.last().unwrap());
            }
            ::CapTerm::Intersection(ref args) => {
                for arg in args.iter().take(args.len()-1) {
                    self.print_cap_term(arg);
                    print!(" & ");
                }
                self.print_cap_term(args.last().unwrap());
            }
            ::CapTerm::Func(x, ref args) => {
                print!("{}", &self.funcs[x as usize]);
                if args.len() > 0 {
                    print!("(");
                    for arg in args.iter().take(args.len()-1) {
                        self.print_cap_term(arg);
                        print!(", ");
                    }
                    self.print_cap_term(args.last().unwrap());
                    print!(")");
                }
            }
            ::CapTerm::Cap(ref arg) => {
                print!("Cap(");
                self.print_cap_term(arg);
                print!(")");
            }
        }
    }

    pub fn print_sigma_term(&self, t: &::SigmaTerm) {
        match *t {
            ::SigmaTerm::Func(x, ref args) => {
                print!("{}", &self.funcs[x as usize]);
                if args.len() > 0 {
                    print!("(");
                    for arg in args.iter().take(args.len()-1) {
                        self.print_sigma_term(arg);
                        print!(", ");
                    }
                    self.print_sigma_term(args.last().unwrap());
                    print!(")");
                }
            }
            ::SigmaTerm::Var(x) => {
                print!("{}", &self.vars[x as usize]);
            }
        }
    }
}
