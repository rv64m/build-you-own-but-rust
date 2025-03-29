use std::io::{BufRead, BufReader, BufWriter, Read, Write};

use crate::lexer::Lexer;

const PROMPT: &'static str = ">> ";

pub fn start<R: Read, W: Write>(input: R, output: W) {
    let mut br = BufReader::new(input);
    let mut wr = BufWriter::new(output);

    let mut buf = String::new();

    loop {
        wr.write(PROMPT.as_bytes()).unwrap();
        wr.flush().unwrap();

        _ = br.read_line(&mut buf).unwrap();
        let mut lexer = Lexer::new(&buf);
        loop {
            let tok = lexer.next_token();
            if tok.is_eof() {
                break;
            }

            wr.write(format!("{}\n", tok).as_bytes()).unwrap();
        }
        wr.flush().unwrap();
    }
}
