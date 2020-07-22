extern crate pest;

#[derive(Parser)]
#[grammar = "kgscript.pest"]
pub struct Parser;
