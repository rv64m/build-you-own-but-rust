use std::io::{stdin, stdout};

mod ast;
mod lexer;
mod parser;
mod repl;

fn main() {
    let input = stdin();
    let output = stdout();

    repl::start(input.lock(), output.lock());
}
