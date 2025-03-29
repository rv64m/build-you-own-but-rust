use crate::lexer::Literal;
use crate::lexer::Token;
use std::any::Any;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum OperatorPrecedence {
    Lowest,
    Equals,
    LessGreater,
    Sum,
    Product,
    Prefix,
    Call,
}

pub trait Node: ToString {
    fn token_literal(&self) -> Literal;
}

pub trait Statement: Node {
    fn statement_node(&self);
    fn as_any(&self) -> &dyn Any;
}

pub trait Expression: Node {
    fn expression_node(&self);

    fn as_any(&self) -> &dyn Any;
}

pub struct Identifier {
    pub token: Token,
    pub value: String,
}

impl ToString for Identifier {
    fn to_string(&self) -> String {
        self.value.clone()
    }
}

impl Node for Identifier {
    fn token_literal(&self) -> Literal {
        self.token.literal()
    }
}

impl Expression for Identifier {
    fn expression_node(&self) {
        todo!()
    }

    fn as_any(&self) -> &dyn Any {
        self
    }
}

pub struct IntegerLiteral {
    pub token: Token,
    pub value: i64,
}

impl ToString for IntegerLiteral {
    fn to_string(&self) -> String {
        self.value.to_string()
    }
}

impl Node for IntegerLiteral {
    fn token_literal(&self) -> Literal {
        self.token.literal()
    }
}

impl Expression for IntegerLiteral {
    fn expression_node(&self) {
        todo!()
    }

    fn as_any(&self) -> &dyn Any {
        self
    }
}

pub struct LetStatement {
    pub token: Token,
    pub name: Box<Identifier>,
    pub value: Option<Box<dyn Expression>>,
}

impl ToString for LetStatement {
    fn to_string(&self) -> String {
        let mut buf = String::new();
        buf.push_str(&self.token_literal());
        buf.push_str(" ");
        buf.push_str(self.name.to_string().as_str());
        buf.push_str(" = ");
        if let Some(value) = self.value.as_ref() {
            buf.push_str(value.to_string().as_str());
        }

        buf.push_str(";");
        return buf;
    }
}

impl Node for LetStatement {
    fn token_literal(&self) -> Literal {
        self.token.literal()
    }
}

impl Statement for LetStatement {
    fn statement_node(&self) {
        // Implementation can be empty
    }

    fn as_any(&self) -> &dyn Any {
        self
    }
}

pub struct ReturnStatement {
    pub token: Token,
    pub value: Option<Box<dyn Expression>>,
}

impl ToString for ReturnStatement {
    fn to_string(&self) -> String {
        let mut buf = String::new();
        buf.push_str(self.token_literal().as_str());
        buf.push_str(" ");
        if let Some(value) = self.value.as_ref() {
            buf.push_str(value.to_string().as_str());
        }
        buf.push_str(";");

        return buf;
    }
}

impl Node for ReturnStatement {
    fn token_literal(&self) -> Literal {
        self.token.literal()
    }
}

impl Statement for ReturnStatement {
    fn statement_node(&self) {
        // Implementation can be empty
    }

    fn as_any(&self) -> &dyn Any {
        self
    }
}

pub struct ExpressionStatement {
    pub token: Token,
    pub expr: Option<Box<dyn Expression>>,
}

impl ToString for ExpressionStatement {
    fn to_string(&self) -> String {
        if let Some(expr) = self.expr.as_ref() {
            return expr.to_string();
        }

        return "".to_string();
    }
}

impl Node for ExpressionStatement {
    fn token_literal(&self) -> Literal {
        self.token.literal()
    }
}

impl Statement for ExpressionStatement {
    fn statement_node(&self) {
        // Implementation can be empty
    }

    fn as_any(&self) -> &dyn Any {
        self
    }
}

pub struct PrefixExpression {
    pub token: Token,
    pub operator: String,
    pub right: Option<Box<dyn Expression>>,
}

pub struct InfixExpression {
    pub token: Token,
    pub operator: String,
    pub left: Option<Box<dyn Expression>>,
    pub right: Option<Box<dyn Expression>>,
}

impl Node for PrefixExpression {
    fn token_literal(&self) -> Literal {
        self.token.literal()
    }
}

impl Statement for PrefixExpression {
    fn statement_node(&self) {
        // Implementation can be empty
    }

    fn as_any(&self) -> &dyn Any {
        self
    }
}

impl Expression for PrefixExpression {
    fn expression_node(&self) {}
    fn as_any(&self) -> &dyn Any {
        self
    }
}

impl ToString for PrefixExpression {
    fn to_string(&self) -> String {
        let mut buf = String::new();
        buf.push_str("(");
        buf.push_str(&self.operator);
        if let Some(right) = self.right.as_ref() {
            buf.push_str(&right.to_string());
        }
        buf.push_str(")");
        buf
    }
}

impl Node for InfixExpression {
    fn token_literal(&self) -> Literal {
        self.token.literal()
    }
}

impl Statement for InfixExpression {
    fn statement_node(&self) {
        // Implementation can be empty
    }

    fn as_any(&self) -> &dyn Any {
        self
    }
}

impl Expression for InfixExpression {
    fn expression_node(&self) {}
    fn as_any(&self) -> &dyn Any {
        self
    }
}

impl ToString for InfixExpression {
    fn to_string(&self) -> String {
        let mut buf = String::new();
        buf.push_str("(");

        if let Some(left) = self.left.as_ref() {
            buf.push_str(&left.to_string());
        }
        buf.push_str(" ");
        buf.push_str(&self.operator);
        buf.push_str(" ");
        if let Some(right) = self.right.as_ref() {
            buf.push_str(&right.to_string());
        }
        buf.push_str(")");
        buf
    }
}

pub struct Program {
    pub stmts: Vec<Box<dyn Statement>>,
}

impl ToString for Program {
    fn to_string(&self) -> String {
        self.stmts
            .iter()
            .map(|stmt| stmt.to_string())
            .collect::<Vec<String>>()
            .join("")
    }
}

#[cfg(test)]
mod tests {
    use crate::lexer::TokenType;

    use super::*;

    #[test]
    fn test_to_string() {
        let program = Program {
            stmts: vec![
                Box::new(LetStatement {
                    token: Token::new(TokenType::Let, "let".to_string()),
                    name: Box::new(Identifier {
                        token: Token::new(TokenType::Ident, "x".to_string()),
                        value: "x".to_string(),
                    }),
                    value: Some(Box::new(Identifier {
                        token: Token::new(TokenType::Ident, "y".to_string()),
                        value: "y".to_string(),
                    })),
                }),
                Box::new(ReturnStatement {
                    token: Token::new(TokenType::Return, "return".to_string()),
                    value: Some(Box::new(Identifier {
                        token: Token::new(TokenType::Ident, "x".to_string()),
                        value: "x".to_string(),
                    })),
                }),
            ],
        };

        assert_eq!(program.to_string(), "let x = y;return x;");
    }
}
