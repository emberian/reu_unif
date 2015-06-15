#![feature(io)]
extern crate unif;
extern crate env_logger;

use std::io::prelude::*;

fn single_match<I: Iterator<Item=char>>(p: &mut unif::parse::Parser<I>, c: &unif::Context) -> Result<(), unif::parse::ParseError> {
    let from = try!(p.parse_sigma_term());
    try!(p.eat(unif::parse::Token::Word("=".into(), true)));
    let to = try!(p.parse_cap_term());
    let substs = c.match_(&from, &to);
    if substs.len() > 0 {
        for subst in substs {
            println!("Solution:");
            for (k, v) in subst {
                p.print_sigma_term(&unif::SigmaTerm::Var(k));
                print!(" |-> ");
                p.print_cap_term(&v);
                println!("");
            }
        }
    } else {
        println!("No solution.");
    }
    try!(p.eat(unif::parse::Token::Dot));
    Ok(())
}

fn main() {
    env_logger::init().unwrap();
    println!("Enter terms to unify! Like so: f(x) = Cap(a | f(b)).");
    let mut p = unif::parse::Parser::new(std::io::stdin().chars().map(|a| a.unwrap()));
    let c = unif::Context::new();
    loop {
        match single_match(&mut p, &c) {
            Ok(..) => { },
            Err(e) => println!("Error: {:?}", e),
        }
    }
}
