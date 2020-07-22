use kgscript::parser::{Rule, Parser as KgParser};
use pest::Parser;
use std::io;


fn read_line() -> io::Result<String> {
    let mut line = String::new();
    io::stdin().read_line(&mut line)?;
    Ok(line)
}


fn main() {
    let line = read_line().expect("Failed to read line from stdin");
    let parsed = KgParser::parse(Rule::topcode, &line);

    match parsed {
        Ok(p) => println!("Success: {:?}", p),
        Err(e) => println!("Error: {:?}", e),
    }
}
