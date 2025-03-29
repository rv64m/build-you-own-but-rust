use std::collections::HashMap;

use crate::{
    ast::{
        Expression, ExpressionStatement, Identifier, InfixExpression, IntegerLiteral, LetStatement,
        OperatorPrecedence, PrefixExpression, Program, ReturnStatement, Statement,
    },
    lexer::{Lexer, Token, TokenType},
};

pub struct Parser {
    l: Lexer,
    errors: Vec<String>,

    cur_token: Token,
    peek_token: Token,

    precedences: HashMap<TokenType, OperatorPrecedence>,
    trace_level: usize,
}

impl Parser {
    pub fn new(mut l: Lexer) -> Self {
        let cur_token = l.next_token();
        let peek_token = l.next_token();
        let precedences = HashMap::from([
            (TokenType::Eq, OperatorPrecedence::Equals),
            (TokenType::Ne, OperatorPrecedence::Equals),
            (TokenType::Lt, OperatorPrecedence::LessGreater),
            (TokenType::Gt, OperatorPrecedence::LessGreater),
            (TokenType::Plus, OperatorPrecedence::Sum),
            (TokenType::Minus, OperatorPrecedence::Sum),
            (TokenType::Asterisk, OperatorPrecedence::Product),
            (TokenType::Slash, OperatorPrecedence::Product),
        ]);

        Self {
            l,
            cur_token,
            peek_token,
            errors: Vec::new(),
            precedences,
            trace_level: 0,
        }
    }

    fn trace_begin(&mut self, msg: &str) {
        let mut indent = String::new();
        for _ in 0..self.trace_level {
            indent.push_str("  ");
        }
        println!("{}BEGIN {}", indent, msg);
        self.trace_level += 1;
    }

    fn trace_end(&mut self, msg: &str) {
        self.trace_level -= 1;
        let mut indent = String::new();
        for _ in 0..self.trace_level {
            indent.push_str("  ");
        }
        println!("{}END {}", indent, msg);
    }

    pub fn parse_program(&mut self) -> Option<Program> {
        self.trace_begin("parse_program");
        let mut stmts: Vec<Box<dyn Statement>> = Vec::new();
        while !self.peek_token.is_eof() {
            if let Some(stmt) = self.parse_statement() {
                stmts.push(stmt);
            }

            self.next_token()
        }

        return Some(Program { stmts });
        self.trace_end("parse_program");
    }

    fn next_token(&mut self) {
        self.cur_token = self.peek_token.clone();
        self.peek_token = self.l.next_token();
    }

    fn expect_peek(&mut self, tok: TokenType) -> bool {
        if self.peek_token_is(tok) {
            self.next_token();
            return true;
        }

        self.errors.push(format!(
            "expect {}, found {}",
            tok,
            self.peek_token.token_type()
        ));

        return false;
    }

    fn peek_token_is(&self, tok: TokenType) -> bool {
        return self.peek_token.token_type() == tok;
    }

    fn cur_token_is(&self, tok: TokenType) -> bool {
        return self.cur_token.token_type() == tok;
    }

    fn parse_statement(&mut self) -> Option<Box<dyn Statement>> {
        self.trace_begin(&format!("parse_statement: {}", self.cur_token.token_type()));
        let result = match self.cur_token.token_type() {
            TokenType::Let => self.parse_let_statement(),
            TokenType::Return => self.parse_return_statement(),
            _ => self.parse_expression_statement(),
        };
        self.trace_end(&format!("parse_statement: {}", self.cur_token.token_type()));
        result
    }

    fn parse_let_statement(&mut self) -> Option<Box<dyn Statement>> {
        let token = self.cur_token.clone();

        if !self.expect_peek(TokenType::Ident) {
            return None;
        }

        let identifier = Identifier {
            token: self.cur_token.clone(),
            value: self.cur_token.literal(),
        };

        // TODO: skip expression parse
        while !self.cur_token_is(TokenType::Semicolon) {
            self.next_token();
        }

        return Some(Box::new(LetStatement {
            token,
            name: Box::new(identifier),
            value: None,
        }));
    }

    fn parse_return_statement(&mut self) -> Option<Box<dyn Statement>> {
        let token = self.cur_token.clone();

        // TODO: skip expression parse
        while !self.cur_token_is(TokenType::Semicolon) {
            self.next_token();
        }

        return Some(Box::new(ReturnStatement { token, value: None }));
    }

    fn parse_expression_statement(&mut self) -> Option<Box<dyn Statement>> {
        let token = self.cur_token.clone();
        let expr = self.parse_expression(OperatorPrecedence::Lowest);
        if self.peek_token_is(TokenType::Semicolon) {
            self.next_token();
        }

        return Some(Box::new(ExpressionStatement { token, expr }));
    }

    fn parse_expression(&mut self, precedence: OperatorPrecedence) -> Option<Box<dyn Expression>> {
        self.trace_begin(&format!("parse_expression: {}", self.cur_token.token_type()));
        // parse prefix
        let mut left_exp = match self.cur_token.token_type() {
            TokenType::Ident => self.parse_identifier(),
            TokenType::Int => self.parse_integer(),
            TokenType::Minus => self.parse_prefix(),
            TokenType::Bang => self.parse_prefix(),
            _ => {
                self.errors
                    .push(format!("no prefix found {}", self.cur_token));
                return None;
            }
        };

        while !self.peek_token_is(TokenType::Semicolon) && precedence < self.peek_precedence() {
            // parse infix
            match self.peek_token.token_type() {
                TokenType::Plus
                | TokenType::Minus
                | TokenType::Asterisk
                | TokenType::Slash
                | TokenType::Eq
                | TokenType::Ne
                | TokenType::Lt
                | TokenType::Gt => {
                    self.next_token();
                    left_exp = self.parse_infix(left_exp);
                }
                _ => return left_exp,
            }
        }

        self.trace_end(&format!("parse_expression: {}", self.cur_token.token_type()));
        return left_exp;
    }

    fn peek_precedence(&self) -> OperatorPrecedence {
        match self.precedences.get(&self.peek_token.token_type()) {
            None => OperatorPrecedence::Lowest,
            Some(p) => *p,
        }
    }

    fn cur_precedence(&self) -> OperatorPrecedence {
        match self.precedences.get(&self.cur_token.token_type()) {
            None => OperatorPrecedence::Lowest,
            Some(p) => *p,
        }
    }

    fn parse_identifier(&mut self) -> Option<Box<dyn Expression>> {
        return Some(Box::new(Identifier {
            token: self.cur_token.clone(),
            value: self.cur_token.literal(),
        }));
    }

    fn parse_integer(&mut self) -> Option<Box<dyn Expression>> {
        let token = self.cur_token.clone();
        let literal = token.literal();
        let value = match literal.parse::<i64>() {
            Err(_) => {
                self.errors
                    .push(format!("cloud not parse {} as integer", literal));
                return None;
            }
            Ok(v) => v,
        };

        Some(Box::new(IntegerLiteral { token, value }))
    }

    fn parse_prefix(&mut self) -> Option<Box<dyn Expression>> {
        self.trace_begin(&format!("parse_prefix: {}", self.cur_token.token_type()));
        let token = self.cur_token.clone();
        let operator = token.literal();
        self.next_token();
        let right = self.parse_expression(OperatorPrecedence::Prefix);

        Some(Box::new(PrefixExpression {
            token,
            operator,
            right,
        }))
    }

    fn parse_infix(&mut self, left: Option<Box<dyn Expression>>) -> Option<Box<dyn Expression>> {
        self.trace_begin(&format!("parse_infix: {}", self.cur_token.token_type()));
        let token = self.cur_token.clone();
        let operator = token.literal();

        // parse right exp
        let precedence = self.cur_precedence();
        self.next_token();
        let right = self.parse_expression(precedence);

        Some(Box::new(InfixExpression {
            token,
            operator,
            left,
            right,
        }))
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        ast::{Expression, ExpressionStatement, Identifier, IntegerLiteral, Node, PrefixExpression, Program},
        lexer::{Lexer, Literal, Token, TokenType},
        parser::Parser,
    };

    struct TestCase<'a> {
        ident: &'a str,
    }

    #[test]
    fn let_statements() {
        let input = r#"
            let x = 5;
            let y = 10;
            let foobar = 838383;
        "#;

        let lexer = Lexer::new(input);
        let mut parser = Parser::new(lexer);
        let program = parser.parse_program();
        assert_eq!(program.is_none(), false, "failed parse program");

        let program = program.unwrap();
        assert_eq!(
            program.stmts.len(),
            3,
            "program.stmts does not contain 3 statements, got={}",
            program.stmts.len()
        );

        let test_cases = vec![
            TestCase { ident: "x" },
            TestCase { ident: "y" },
            TestCase { ident: "foobar" },
        ];
        for (i, tc) in test_cases.into_iter().enumerate() {
            assert_eq!(program.stmts[i].token_literal(), "let");

            let let_stmt = program.stmts[i]
                .as_any()
                .downcast_ref::<crate::ast::LetStatement>();
            assert_eq!(let_stmt.is_none(), false, "statement is not LetStatement");
            let let_stmt = let_stmt.unwrap();
            assert_eq!(let_stmt.name.value, tc.ident);
            assert_eq!(let_stmt.name.token_literal(), tc.ident);
        }
    }

    #[test]
    fn return_statements() {
        let input = r#"
            return 5;
            return 10;
            return add(5, 10);
        "#;

        let lexer = Lexer::new(input);
        let mut parser = Parser::new(lexer);
        let program = parser.parse_program();
        assert_eq!(program.is_none(), false, "failed parse program");

        let program = program.unwrap();
        assert_eq!(program.stmts.len(), 3);

        let test_cases = vec![TestCase { ident: "5" }, TestCase { ident: "10" }];
        for (i, tc) in test_cases.into_iter().enumerate() {
            assert_eq!(program.stmts[i].token_literal(), "return");

            let return_stmt = program.stmts[i]
                .as_any()
                .downcast_ref::<crate::ast::ReturnStatement>();
            assert_eq!(
                return_stmt.is_none(),
                false,
                "statement is not ReturnStatement"
            );
            // let return_stmt = return_stmt.unwrap();
            // assert_eq!(return_stmt.token_literal(), tc.ident);
        }
    }

    #[test]
    fn identifier_expression() {
        let input = r#"
            foobar;
        "#;

        let lexer = Lexer::new(input);
        let mut parser = Parser::new(lexer);

        let program = parser.parse_program();
        assert_eq!(program.is_none(), false, "failed parse program");

        let program = program.unwrap();
        assert_eq!(
            program.stmts.len(),
            1,
            "program.stmts does not contain 1 statement"
        );

        let stmt = program.stmts[0]
            .as_any()
            .downcast_ref::<ExpressionStatement>();
        assert_eq!(
            stmt.is_none(),
            false,
            "statement is not ExpressionStatement"
        );
        assert_eq!(
            stmt.unwrap().expr.is_none(),
            false,
            "statement not found expression"
        );
        let stmt_expr = stmt.unwrap().expr.as_ref().unwrap();

        let stmt_ident = stmt_expr.as_any().downcast_ref::<Identifier>();
        assert_eq!(stmt_ident.is_none(), false, "statement is not Identifier");

        let stmt_ident = stmt_ident.unwrap();
        assert_eq!(stmt_ident.token_literal(), "foobar");
        assert_eq!(stmt_ident.value, "foobar");
    }

    #[test]
    fn integer_literal_expression() {
        let input = r#"
            5;
        "#;

        let lexer = Lexer::new(input);
        let mut parser = Parser::new(lexer);

        let program = parser.parse_program();
        assert_eq!(program.is_none(), false, "failed parse program");

        let program = program.unwrap();
        assert_eq!(
            program.stmts.len(),
            1,
            "program.stmts does not contain 1 statement"
        );

        let stmt = program.stmts[0]
            .as_any()
            .downcast_ref::<ExpressionStatement>();
        assert_eq!(
            stmt.is_none(),
            false,
            "statement is not ExpressionStatement"
        );
        assert_eq!(
            stmt.unwrap().expr.is_none(),
            false,
            "statement not found expression"
        );
        let stmt_expr = stmt.unwrap().expr.as_ref().unwrap();

        let stmt_ident = stmt_expr.as_any().downcast_ref::<IntegerLiteral>();
        assert_eq!(stmt_ident.is_none(), false, "statement is not Identifier");

        let stmt_ident = stmt_ident.unwrap();
        assert_eq!(stmt_ident.token_literal(), "5");
        assert_eq!(stmt_ident.value, 5);
    }

    #[test]
    fn parsing_prefix_expression() {
        struct PrefixTestCase {
            input: String,
            operator: String,
            integer_value: i64,
        }

        let test_cases = vec![
            PrefixTestCase {
                input: "!5;".to_string(),
                operator: "!".to_string(),
                integer_value: 5,
            },
            PrefixTestCase {
                input: "-15;".to_string(),
                operator: "-".to_string(),
                integer_value: 15,
            },
        ];

        for tc in test_cases.iter() {
            let lexer = Lexer::new(tc.input.as_str());
            let mut parser = Parser::new(lexer);

            let program = parser.parse_program();
            assert_eq!(program.is_none(), false, "failed parse program");

            let program = program.unwrap();
            assert_eq!(
                program.stmts.len(),
                1,
                "program.stmts does not contain 1 statement"
            );

            let stmt = program.stmts[0]
                .as_any()
                .downcast_ref::<ExpressionStatement>();
            assert_eq!(
                stmt.is_none(),
                false,
                "statement is not ExpressionStatement"
            );

            assert_eq!(
                stmt.unwrap().expr.is_none(),
                false,
                "statement not found expression"
            );
            let stmt_expr = stmt.unwrap().expr.as_ref().unwrap();

            let prefix_stmt = stmt_expr.as_any().downcast_ref::<PrefixExpression>();
            assert_eq!(prefix_stmt.is_none(), false, "statement is not Identifier");
            let prefix_stmt = prefix_stmt.unwrap();
            assert_eq!(prefix_stmt.operator, tc.operator);
            assert_eq!(prefix_stmt.right.is_none(), false);

            let prefix_right_stmt = prefix_stmt
                .right
                .as_ref()
                .unwrap()
                .as_any()
                .downcast_ref::<IntegerLiteral>();
            assert_eq!(
                prefix_right_stmt.is_none(),
                false,
                "statement is not integer literal"
            );
            let prefix_right_stmt = prefix_right_stmt.unwrap();
            assert_eq!(prefix_right_stmt.value, tc.integer_value);
        }
    }

    #[test]
    fn operator_precedence_parsing() {
        let cases = vec![
            ("a + b * c;", "(a + (b * c))"),
            ("-a * b;", "((-a) * b)"),
            ("!-a;", "(!(-a))"),
            ("a + b + c;", "((a + b) + c)"),
            ("a + b - c;", "((a + b) - c)"),
            ("a * b * c;", "((a * b) * c)"),
            ("a * b / c;", "((a * b) / c)"),
            ("a + b / c;", "(a + (b / c))"),
            ("a + b * c + d / e - f;", "(((a + (b * c)) + (d / e)) - f)"),
            ("3 + 4; -5 * 5;", "(3 + 4)((-5) * 5)"),
            ("5 > 4 == 3 < 4;", "((5 > 4) == (3 < 4))"),
            ("5 < 4 != 3 > 4;", "((5 < 4) != (3 > 4))"),
            (
                "3 + 4 * 5 == 3 * 1 + 4 * 5;",
                "((3 + (4 * 5)) == ((3 * 1) + (4 * 5)))",
            ),
        ];

        for case in cases.iter() {
            let mut parser = Parser::new(Lexer::new(case.0));
            let program = parser.parse_program();
            assert_eq!(program.is_none(), false);

            let program = program.unwrap();
            assert_eq!(case.1, program.to_string().as_str())
        }
    }
}
