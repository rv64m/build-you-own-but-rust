use std::collections::HashMap;

use crate::{
    ast::{
        BlockStatement, BooleanLiteral, CallExpression, Expression, ExpressionStatement, FnLiteral,
        Identifier, IfExpression, InfixExpression, IntegerLiteral, LetStatement,
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
            (TokenType::LParaen, OperatorPrecedence::Call),
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

        if !self.expect_peek(TokenType::Assign) {
            return None;
        }

        self.next_token();

        let value = self.parse_expression(OperatorPrecedence::Lowest);

        if self.peek_token_is(TokenType::Semicolon) {
            self.next_token();
        }

        return Some(Box::new(LetStatement {
            token,
            name: Box::new(identifier),
            value,
        }));
    }

    fn parse_return_statement(&mut self) -> Option<Box<dyn Statement>> {
        let token = self.cur_token.clone();
        self.next_token();

        let value = self.parse_expression(OperatorPrecedence::Lowest);
        if self.peek_token_is(TokenType::Semicolon) {
            self.next_token();
        }

        return Some(Box::new(ReturnStatement { token, value }));
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
        self.trace_begin(&format!(
            "parse_expression: {}",
            self.cur_token.token_type()
        ));
        // parse prefix
        let mut left_exp = match self.cur_token.token_type() {
            TokenType::Ident => self.parse_identifier(),
            TokenType::Int => self.parse_integer(),
            TokenType::Minus => self.parse_prefix(),
            TokenType::Bang => self.parse_prefix(),
            TokenType::LParaen => self.parse_grouped_expr(),
            TokenType::If => self.parse_if_expr(),
            TokenType::Function => self.parse_fn_expr(),
            TokenType::True | TokenType::False => self.parse_boolean(),
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
                TokenType::LParaen => {
                    self.next_token();
                    left_exp = self.parse_call_expr(left_exp);
                }
                _ => return left_exp,
            }
        }

        self.trace_end(&format!(
            "parse_expression: {}",
            self.cur_token.token_type()
        ));
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

    fn parse_boolean(&mut self) -> Option<Box<dyn Expression>> {
        self.trace_begin(&format!("parse_boolean: {}", self.cur_token.token_type()));
        let token = self.cur_token.clone();

        let value = match token.literal().as_str() {
            "true" => true,
            "false" => false,
            _ => {
                self.errors
                    .push(format!("cloud not parse {} as boolean", token.literal()));
                return None;
            }
        };
        self.trace_end(&format!("parse_boolean: {}", self.cur_token.token_type()));

        Some(Box::new(BooleanLiteral { token, value }))
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

    fn parse_call_expr(
        &mut self,
        function: Option<Box<dyn Expression>>,
    ) -> Option<Box<dyn Expression>> {
        self.trace_begin(&format!("parse_call_expr: {}", self.cur_token.token_type()));
        let function = if let Some(function) = function {
            function
        } else {
            return None;
        };
        let token = self.cur_token.clone();
        let arguments = match self.parse_call_args() {
            None => return None,
            Some(args) => args,
        };

        self.trace_end(&format!("parse_call_expr: {}", self.cur_token.token_type()));
        Some(Box::new(CallExpression {
            token,
            function,
            arguments,
        }))
    }

    fn parse_call_args(&mut self) -> Option<Vec<Box<dyn Expression>>> {
        self.trace_begin(&format!("parse_call_args: {}", self.cur_token.token_type()));
        let mut args = Vec::new();

        // empty function call args
        if self.peek_token_is(TokenType::RParaen) {
            return None;
        }

        self.next_token();
        match self.parse_expression(OperatorPrecedence::Lowest) {
            None => return None,
            Some(expr) => args.push(expr),
        }
        while self.peek_token_is(TokenType::Comma) {
            self.next_token(); // move to comma
            self.next_token(); // move to arg expr first
            match self.parse_expression(OperatorPrecedence::Lowest) {
                None => return None,
                Some(expr) => args.push(expr),
            }
        }

        if !self.expect_peek(TokenType::RParaen) {
            return None;
        }

        self.trace_end(&format!("parse_call_args: {}", self.cur_token.token_type()));
        Some(args)
    }

    fn parse_grouped_expr(&mut self) -> Option<Box<dyn Expression>> {
        self.next_token();
        let expr = self.parse_expression(OperatorPrecedence::Lowest);
        if !self.expect_peek(TokenType::RParaen) {
            return None;
        }

        return expr;
    }

    fn parse_if_expr(&mut self) -> Option<Box<dyn Expression>> {
        let token = self.cur_token.clone();

        // the tok should is '('
        if !self.expect_peek(TokenType::LParaen) {
            return None;
        }
        self.next_token();

        // parse expr in "()"
        let condition = match self.parse_expression(OperatorPrecedence::Lowest) {
            Some(cond_expr) => cond_expr,
            None => {
                self.errors.push("expected condition after if".to_string());
                return None;
            }
        };

        // the tok should is ')'
        if !self.expect_peek(TokenType::RParaen) {
            return None;
        }

        // the tok should is '{'
        if !self.expect_peek(TokenType::LBrace) {
            return None;
        }

        // parse block statement in if
        let consequence = self.parse_block_statement();

        let mut alternative = None;
        if self.expect_peek(TokenType::Else) {
            if !self.expect_peek(TokenType::LBrace) {
                return None;
            }

            alternative = Some(self.parse_block_statement());
        }

        Some(Box::new(IfExpression {
            token,
            condition,
            consequence,
            alternative,
        }))
    }

    fn parse_fn_expr(&mut self) -> Option<Box<dyn Expression>> {
        let token = self.cur_token.clone();
        if !self.expect_peek(TokenType::LParaen) {
            return None;
        }

        let parameters = self.parse_fn_parameters();

        if !self.expect_peek(TokenType::LBrace) {
            return None;
        }

        let body = self.parse_block_statement();

        Some(Box::new(FnLiteral {
            token,
            parameters,
            body,
        }))
    }

    fn parse_block_statement(&mut self) -> Box<BlockStatement> {
        self.next_token();

        let token = self.cur_token.clone();
        let mut stmts = Vec::new();
        while !self.cur_token_is(TokenType::RBrace) && !self.cur_token_is(TokenType::Eof) {
            if let Some(stmt) = self.parse_statement() {
                stmts.push(stmt);
            }
            self.next_token();
        }
        Box::new(BlockStatement { token, stmts })
    }

    fn parse_fn_parameters(&mut self) -> Vec<Identifier> {
        let mut idents = Vec::new();
        if self.peek_token_is(TokenType::RParaen) {
            self.next_token();
            return idents;
        }

        // first ident
        self.next_token();
        if !self.cur_token_is(TokenType::Ident) {
            return idents;
        }

        idents.push(Identifier {
            token: self.cur_token.clone(),
            value: self.cur_token.literal(),
        });

        while self.peek_token_is(TokenType::Comma) {
            self.next_token();
            self.next_token();
            idents.push(Identifier {
                token: self.cur_token.clone(),
                value: self.cur_token.literal(),
            });
        }

        if !self.expect_peek(TokenType::RParaen) {
            return Vec::new();
        }

        idents
    }
}

#[cfg(test)]
mod tests {
    use std::any::Any;

    use crate::{
        ast::{
            BooleanLiteral, CallExpression, Expression, ExpressionStatement, FnLiteral, Identifier,
            IfExpression, InfixExpression, IntegerLiteral, Node, PrefixExpression,
        },
        lexer::Lexer,
        parser::Parser,
    };

    fn check_boolean_literal(exp: &dyn Expression, value: bool) {
        let boolean = exp.as_any().downcast_ref::<BooleanLiteral>();
        assert_eq!(boolean.is_none(), false, "statement is not BooleanLiteral");

        let boolean = boolean.unwrap();
        assert_eq!(boolean.value, value, "boolean value is not {}", value);
    }

    fn check_literal_expr(expr: &dyn Expression, expected_value: &dyn Any) {
        if let Some(int_value) = expected_value.downcast_ref::<i64>() {
            let int_exp = expr.as_any().downcast_ref::<IntegerLiteral>();
            assert_eq!(int_exp.is_none(), false, "expression is not IntegerLiteral");
            let int_exp = int_exp.unwrap();
            assert_eq!(int_exp.value, *int_value, "integer value does not match");
        } else if let Some(bool_value) = expected_value.downcast_ref::<bool>() {
            check_boolean_literal(expr, *bool_value);
        } else if let Some(ident_value) = expected_value.downcast_ref::<&str>() {
            let ident_exp = expr.as_any().downcast_ref::<Identifier>();
            assert_eq!(ident_exp.is_none(), false, "expression is not Identifier");
            let ident_exp = ident_exp.unwrap();
            assert_eq!(
                ident_exp.value, *ident_value,
                "identifier value does not match"
            );
        } else {
            panic!("Unsupported value type");
        }
    }

    fn check_function_literal(
        expr: &dyn Expression,
        expected_args: &[&dyn Any],
        expected_body: &str,
    ) {
        let fn_literal = expr.as_any().downcast_ref::<FnLiteral>();
        assert_eq!(fn_literal.is_none(), false, "value is None");

        let fn_literal = fn_literal.unwrap();
        assert_eq!(fn_literal.token_literal(), "fn");
        assert_eq!(fn_literal.parameters.len(), expected_args.len());

        for (i, arg) in fn_literal.parameters.iter().enumerate() {
            check_literal_expr(arg, expected_args[i]);
        }

        assert_eq!(fn_literal.body.to_string().as_str(), expected_body);
    }

    #[test]
    fn test_let_statements() {
        let cases = vec![("let x = 5;", "x", 5i64), ("let y = 10;", "y", 10i64)];
        for (input, name, value) in cases {
            let lexer = Lexer::new(input);
            let mut parser = Parser::new(lexer);
            let program = parser.parse_program();
            assert_eq!(program.is_none(), false, "failed parse program");

            let program = program.unwrap();
            assert_eq!(
                program.stmts.len(),
                1,
                "program.stmts does not contain 1 statement, got={}",
                program.stmts.len()
            );

            let let_stmt = program.stmts[0]
                .as_any()
                .downcast_ref::<crate::ast::LetStatement>();
            assert_eq!(let_stmt.is_none(), false, "statement is not LetStatement");
            let let_stmt = let_stmt.unwrap();
            assert_eq!(let_stmt.name.value, name);
            assert_eq!(let_stmt.name.token_literal(), name);
            assert_eq!(let_stmt.value.is_none(), false, "value is None");

            let let_stmt_value = let_stmt.value.as_ref().unwrap().as_ref();
            check_literal_expr(let_stmt_value, &value);
        }

        let input = r#"
            let x = fn (a, b) { return a + b; };
        "#;

        let lexer = Lexer::new(input);
        let mut parser = Parser::new(lexer);
        let program = parser.parse_program();
        assert_eq!(program.is_none(), false, "failed parse program");

        let program = program.unwrap();

        let let_stmt = program.stmts[0]
            .as_any()
            .downcast_ref::<crate::ast::LetStatement>();
        assert_eq!(let_stmt.is_none(), false, "statement is not LetStatement");
        let let_stmt = let_stmt.unwrap();

        check_literal_expr(let_stmt.name.as_ref(), &"x");

        assert_eq!(let_stmt.value.is_none(), false, "value is None");
        let let_stmt_value = let_stmt.value.as_ref().unwrap().as_ref();
        check_function_literal(let_stmt_value, &[&"a", &"b"], "return (a + b);");
    }

    #[test]
    fn test_return_statements() {
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
    fn parsing_operator_precedence() {
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
            ("true;", "true"),
            ("false;", "false"),
            ("3 > 5 == false;", "((3 > 5) == false)"),
            ("3 < 5 == true;", "((3 < 5) == true)"),
            // grouped expression
            ("1 + (2 + 3) + 4;", "((1 + (2 + 3)) + 4)"),
            ("a * (b + c) / (a * d);", "((a * (b + c)) / (a * d))"),
        ];

        for case in cases.iter() {
            let mut parser = Parser::new(Lexer::new(case.0));
            let program = parser.parse_program();
            assert_eq!(program.is_none(), false);

            let program = program.unwrap();
            assert_eq!(case.1, program.to_string().as_str())
        }
    }

    fn check_identifier(exp: &dyn Expression, ident: &str) {
        let identifier = exp.as_any().downcast_ref::<Identifier>();
        assert_eq!(identifier.is_none(), false, "statement is not Identifier");
        let identifier = identifier.unwrap();
        assert_eq!(identifier.value, ident, "identifier value is not {}", ident);
        assert_eq!(
            identifier.token_literal(),
            ident,
            "identifier token literal is not {}",
            ident
        );
    }

    fn check_prefix_exp(exp: &dyn Expression, operator: &str, right: &dyn Any) {
        let prefix_expr = exp.as_any().downcast_ref::<PrefixExpression>();
        assert_eq!(
            prefix_expr.is_none(),
            false,
            "expression is not PrefixExpression"
        );
        let prefix_expr = prefix_expr.unwrap();
        assert_eq!(
            prefix_expr.operator, operator,
            "prefix operator does not match"
        );
        let prefix_right_expr = prefix_expr.right.as_ref().unwrap().as_ref();
        check_literal_expr(prefix_right_expr, right);
    }

    fn check_infix_exp(exp: &dyn Expression, left: &dyn Any, operator: &str, right: &dyn Any) {
        let infix_expr = exp.as_any().downcast_ref::<InfixExpression>();
        assert_eq!(
            infix_expr.is_none(),
            false,
            "statement is not InfixExpression"
        );
        let infix_expr = infix_expr.unwrap();

        let infix_left_expr = infix_expr.left.as_ref().unwrap().as_ref();
        check_literal_expr(infix_left_expr, left);
        assert_eq!(
            infix_expr.operator, operator,
            "check infix operator failed, expect {}, got {}",
            operator, infix_expr.operator
        );
        let infix_right_expr = infix_expr.right.as_ref().unwrap().as_ref();
        check_literal_expr(infix_right_expr, right);
    }

    #[test]
    fn pasing_prefix() {
        let cases = vec![
            ("!true;", Box::new("!"), Box::new(true)),
            ("!false;", Box::new("!"), Box::new(false)),
        ];

        for case in cases.iter() {
            let mut parser = Parser::new(Lexer::new(case.0));
            let program = parser.parse_program();
            assert_eq!(program.is_none(), false, "failed parse program");

            let program = program.unwrap();
            assert_eq!(program.stmts.len(), 1);

            let expr_stmt = program.stmts[0]
                .as_any()
                .downcast_ref::<ExpressionStatement>();
            assert_eq!(
                expr_stmt.is_none(),
                false,
                "statement is not ExpressionStatement"
            );
            let expr_stmt = expr_stmt.unwrap();
            assert_eq!(expr_stmt.expr.is_none(), false, "failed parse expression");
            let expr = expr_stmt.expr.as_ref().unwrap().as_ref();

            check_prefix_exp(expr, case.1.as_ref(), case.2.as_ref());
        }
    }

    #[test]
    fn parsing_infix() {
        let cases = vec![
            ("true == true;", Box::new(true), "==", Box::new(true)),
            ("true != false;", Box::new(true), "!=", Box::new(false)),
            ("false == false;", Box::new(false), "==", Box::new(false)),
        ];

        for case in cases.iter() {
            let mut parser = Parser::new(Lexer::new(case.0));
            let program = parser.parse_program();
            assert_eq!(program.is_none(), false, "failed parse program");

            let program = program.unwrap();
            assert_eq!(program.stmts.len(), 1);

            let expr_stmt = program.stmts[0]
                .as_any()
                .downcast_ref::<ExpressionStatement>();
            assert_eq!(
                expr_stmt.is_none(),
                false,
                "statement is not ExpressionStatement"
            );
            let expr_stmt = expr_stmt.unwrap();
            assert_eq!(expr_stmt.expr.is_none(), false, "failed parse expression");
            let expr = expr_stmt.expr.as_ref().unwrap().as_ref();

            check_infix_exp(expr, case.1.as_ref(), case.2, case.3.as_ref());
        }
    }

    #[test]
    fn test_if_expr() {
        let input = "if (x < y) { x } ";

        let mut parser = Parser::new(Lexer::new(input));
        let program = parser.parse_program();
        assert_eq!(program.is_none(), false, "failed parse program");

        let program = program.unwrap();

        let expr_stmt = program.stmts[0]
            .as_any()
            .downcast_ref::<ExpressionStatement>();
        assert_eq!(
            expr_stmt.is_none(),
            false,
            "statement is not ExpressionStatement"
        );
        let expr_stmt = expr_stmt.unwrap();
        assert_eq!(expr_stmt.expr.is_none(), false, "failed parse expression");
        let expr = expr_stmt.expr.as_ref().unwrap().as_ref();

        let if_expr = expr.as_any().downcast_ref::<IfExpression>();
        assert_eq!(if_expr.is_none(), false, "failed parse if expression");
        let if_expr = if_expr.unwrap();
        assert_eq!(
            if_expr.token_literal(),
            "if".to_string(),
            "failed parse if expression"
        );

        check_infix_exp(if_expr.condition.as_ref(), &"x", "<", &"y");

        let consequence_expr = if_expr.consequence.stmts[0]
            .as_any()
            .downcast_ref::<ExpressionStatement>();
        assert_eq!(
            consequence_expr.is_none(),
            false,
            "statement is not ExpressionStatement"
        );
        let consequence_expr = consequence_expr.unwrap();
        assert_eq!(
            consequence_expr.expr.is_none(),
            false,
            "failed parse expression"
        );
        let expr = consequence_expr.expr.as_ref().unwrap().as_ref();
        check_identifier(expr, "x");

        assert_eq!(
            if_expr.alternative.is_none(),
            true,
            "failed parse alternative"
        );
    }

    #[test]
    fn test_fn_parameters() {
        // (input, parameters, can't parse)
        let cases = vec![
            (r#"fn() {}"#, vec![], false),
            (r#"fn(x) {}"#, vec!["x".to_string()], false),
            (
                r#"fn(x, y, z) {}"#,
                vec!["x".to_string(), "y".to_string(), "z".to_string()],
                false,
            ),
            (r#"fn(x, y, z,) {}"#, vec![], false),
            (r#"fn(,,x, y, z,) {}"#, vec![], true),
            (r#"fn(x,, y, z,) {}"#, vec![], true),
        ];

        for case in cases.iter() {
            let mut parser = Parser::new(Lexer::new(case.0));
            let program = parser.parse_program();
            assert_eq!(program.is_none(), false, "failed parse program");

            let program = program.unwrap();
            // assert_eq!(program.stmts.len(), 1);

            let expr_stmt = program.stmts[0]
                .as_any()
                .downcast_ref::<ExpressionStatement>();
            assert_eq!(
                expr_stmt.is_none(),
                false,
                "statement is not ExpressionStatement"
            );
            let expr_stmt = expr_stmt.unwrap();
            assert_eq!(expr_stmt.expr.is_none(), case.2, "failed parse expression");
            if !case.2 {
                let expr = expr_stmt.expr.as_ref().unwrap().as_ref();

                let fn_literal = expr.as_any().downcast_ref::<FnLiteral>();
                assert_eq!(fn_literal.is_none(), false, "failed parse fn literal");
                let fn_literal = fn_literal.unwrap();

                assert_eq!(fn_literal.parameters.len(), case.1.len());
                for (i, ident) in case.1.iter().enumerate() {
                    assert_eq!(fn_literal.parameters[i].value, *ident);
                }
            }
        }
    }

    #[test]
    fn test_fn_literal() {
        let input = r#"
            fn(x, y) {
                x + y;
            }
            "#;

        let mut parser = Parser::new(Lexer::new(input));
        let program = parser.parse_program();
        assert_eq!(program.is_none(), false, "failed parse program");

        let program = program.unwrap();

        let expr_stmt = program.stmts[0]
            .as_any()
            .downcast_ref::<ExpressionStatement>();
        assert_eq!(
            expr_stmt.is_none(),
            false,
            "statement is not ExpressionStatement"
        );
        let expr_stmt = expr_stmt.unwrap();
        assert_eq!(expr_stmt.expr.is_none(), false, "failed parse expression");
        let expr = expr_stmt.expr.as_ref().unwrap().as_ref();

        let fn_literal = expr.as_any().downcast_ref::<FnLiteral>();
        assert_eq!(fn_literal.is_none(), false, "failed parse fn literal");

        let fn_literal = fn_literal.unwrap();

        // check parameters
        assert_eq!(
            fn_literal.parameters.len(),
            2,
            "fn literal parameters wrong. expected 2, got {}",
            fn_literal.parameters.len()
        );
        check_literal_expr(&fn_literal.parameters[0], &"x");
        check_literal_expr(&fn_literal.parameters[1], &"y");

        // check body
        let fn_body_expr = fn_literal.body.stmts[0]
            .as_any()
            .downcast_ref::<ExpressionStatement>();
        assert_eq!(fn_body_expr.is_none(), false, "failed parse fn body");
        let fn_body_expr = fn_body_expr.unwrap();

        check_infix_exp(
            fn_body_expr.expr.as_ref().unwrap().as_ref(),
            &"x",
            "+",
            &"y",
        );
    }

    #[test]
    fn test_call_expr() {
        let input = r#"
            add(1, 2 * 3, a + b);
        "#;

        let mut parser = Parser::new(Lexer::new(input));
        let program = parser.parse_program();
        assert_eq!(program.is_none(), false, "failed parse program");

        let program = program.unwrap();

        let stmt = program.stmts[0]
            .as_any()
            .downcast_ref::<ExpressionStatement>();
        assert_eq!(stmt.is_none(), false, "failed parse statement");
        let stmt = stmt.unwrap();
        assert_eq!(stmt.expr.is_none(), false, "failed parse expression");
        let expr = stmt.expr.as_ref().unwrap().as_ref();

        let call_expr = expr.as_any().downcast_ref::<CallExpression>();
        assert_eq!(call_expr.is_none(), false, "failed parse call expression");
        let call_expr = call_expr.unwrap();
        assert_eq!(call_expr.token_literal(), "(");

        let fn_literal = call_expr.function.as_any().downcast_ref::<Identifier>();
        assert_eq!(fn_literal.is_none(), false, "failed parse fn literal");
        let fn_literal = fn_literal.unwrap();
        assert_eq!(fn_literal.value, "add");

        let args: &Vec<Box<dyn Expression>> = call_expr.arguments.as_ref();
        assert_eq!(args.len(), 3);

        // check arg 1
        let arg0 = args[0].as_ref();
        check_literal_expr(arg0, &1i64);

        // check arg 2
        let arg1 = args[1].as_ref();
        check_infix_exp(arg1, &2i64, "*", &3i64);

        // check arg 3
        let arg2 = args[2].as_ref();
        check_infix_exp(arg2, &"a", "+", &"b");
    }
}
