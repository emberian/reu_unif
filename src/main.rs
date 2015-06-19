#![allow(bad_style, dead_code)]
#![feature(io)]
extern crate unif;
extern crate env_logger;

use unif::*;
use std::io::prelude::*;

fn single_match<I: Iterator<Item=char>>(p: &mut Parser<I>, c: &Context) -> Result<(), ParseError> {
    let from = try!(p.parse_sigma_term());
    try!(p.eat(Token::Word("=".into(), true)));
    let to = try!(p.parse_cap_term());
    let substs = c.match_(&from, &to);
    if substs.len() > 0 {
        for subst in substs {
            println!("Solution:");
            for (k, v) in subst {
                p.print_sigma_term(&SigmaTerm::Var(k));
                print!(" |-> ");
                p.print_cap_term(&v);
                println!("");
            }
        }
    } else {
        println!("No solution.");
    }
    try!(p.eat(Token::Dot));
    Ok(())
}

fn main() {
    env_logger::init().unwrap();
    //println!("Enter terms to unify! Like so: f(x) = Cap(a | f(b)).");
    let mut p = Parser::new(std::io::stdin().chars().map(|a| a.unwrap()));
    let c = Context::new();
    let A = SigmaTerm::Func(p.intern("A".into(), true), vec![]);
    let B = SigmaTerm::Func(p.intern("B".into(), true), vec![]);
    let NA = SigmaTerm::Func(p.intern("N_A".into(), true), vec![]);
    let NB = SigmaTerm::Func(p.intern("N_B".into(), true), vec![]);
    let KAB = SigmaTerm::Func(p.intern("K_AB".into(), true), vec![]);
    let KAS = SigmaTerm::Func(p.intern("K_AS".into(), true), vec![]);
    let KBS =  SigmaTerm::Func(p.intern("K_BS".into(), true), vec![]);
    let one = ProtocolRule {
        left: vec![B.clone(), NB.clone()],
        right: SigmaTerm::Func(0, vec![A.clone(), SigmaTerm::Func(0, vec![B.clone(), SigmaTerm::Func(0, vec![NA.clone(), NB.clone()])])]),
    };
    let M1 = SigmaTerm::Func(0, vec![KAB.clone(), SigmaTerm::Func(0, vec![B.clone(), NA.clone()])]);
    let M2 = SigmaTerm::Func(0, vec![KAB.clone(), SigmaTerm::Func(0, vec![A.clone(), NB.clone()])]);
    let two = ProtocolRule {
        left: vec![A.clone(), B.clone(), NA.clone(), NB.clone()],
        right: SigmaTerm::Func(0, vec![SigmaTerm::Func(1, vec![M1, KAS.clone()]), SigmaTerm::Func(1, vec![M2, KBS.clone()])]),
    };

    let proto = Protocol::new(vec![A, B, NA, NB], vec![one, two]);

    let (success, mut knowledge) = proto.forward_search(&c, KAB);
    if success {
        println!(":-) We were able to snoop the key!");
    } else {
        println!(":-( We were not able to snoop the key.");
    }
    println!("The intruder was able to learn:");
    for val in knowledge.un() {
        p.print_cap_term(val);
        println!("");
    }

    /*
    loop {
        match single_match(&mut p, &c) {
            Ok(..) => { },
            Err(e) => println!("Error: {:?}", e),
        }
    }
    */
}
