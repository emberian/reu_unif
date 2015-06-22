#![feature(io)]
extern crate unif;
extern crate env_logger;

use unif::*;
use std::io::prelude::*;

#[allow(dead_code)] // for the interactive system later, testing CAP-matching alone.
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
    let mut p = Parser::new(std::io::stdin().chars().map(|a| a.unwrap()));
    let c = Context::new();

    // TODO: Use the same knowledge set, but for efficiency and succinctness of output.
    println!("Enter a protocol.");
    let (proto, goals) = p.parse_protocol().unwrap();
    for goal in goals {
        let (success, mut knowledge) = proto.forward_search(&c, &goal);
        if success {
            print!("Attacker was able to deduce ");
        } else {
            print!("Attacker NOT able to deduce ");
        }
        p.print_sigma_term(&goal);
        println!("");
        println!("The intruder was able to learn:");
        for val in knowledge.un() {
            p.print_cap_term(val);
            println!("");
        }
    }
    println!("Enter more goals? (TODO)");
}
