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

pub struct BooleanLiteral {
    pub token: Token,
    pub value: bool,
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

impl ToString for BooleanLiteral {
    fn to_string(&self) -> String {
        self.value.to_string()
    }
}

impl Node for BooleanLiteral {
    fn token_literal(&self) -> Literal {
        self.token.literal()
    }
}

impl Expression for BooleanLiteral {
    fn expression_node(&self) {
        todo!()
    }

    fn as_any(&self) -> &dyn Any {
        self
    }
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

impl ToString for BlockStatement {
    fn to_string(&self) -> String {
        let mut buf = String::new();
        for (i, stmt) in self.stmts.iter().enumerate() {
            buf.push_str(stmt.to_string().as_str());
            if i + 1 != self.stmts.len() {
                buf.push_str("\n");
            }
        }
        return buf;
    }
}

impl Node for BlockStatement {
    fn token_literal(&self) -> Literal {
        self.token.literal()
    }
}

impl Statement for BlockStatement {
    fn statement_node(&self) {
        // Implementation can be empty
    }

    fn as_any(&self) -> &dyn Any {
        self
    }
}

impl Node for IfExpression {
    fn token_literal(&self) -> Literal {
        self.token.literal()
    }
}

impl Statement for IfExpression {
    fn statement_node(&self) {
        // Implementation can be empty
    }

    fn as_any(&self) -> &dyn Any {
        self
    }
}

impl Expression for IfExpression {
    fn expression_node(&self) {}
    fn as_any(&self) -> &dyn Any {
        self
    }
}

impl ToString for IfExpression {
    fn to_string(&self) -> String {
        let mut buf = String::new();
        buf.push_str("if (");
        buf.push_str(self.condition.to_string().as_str());
        buf.push_str(") {");

        buf.push_str(self.consequence.to_string().as_str());
        buf.push_str("}");

        if let Some(alternative) = self.alternative.as_ref() {
            buf.push_str("else { ");
            buf.push_str(alternative.to_string().as_str());
            buf.push_str("} ");
        }

        buf
    }
}

pub struct LetStatement {
    pub token: Token,
    pub name: Box<Identifier>,
    pub value: Option<Box<dyn Expression>>,
}

pub struct ReturnStatement {
    pub token: Token,
    pub value: Option<Box<dyn Expression>>,
}

pub struct ExpressionStatement {
    pub token: Token,
    pub expr: Option<Box<dyn Expression>>,
}

pub struct BlockStatement {
    pub token: Token,
    pub stmts: Vec<Box<dyn Statement>>,
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

pub struct IfExpression {
    /// The 'if' token
    pub token: Token,
    pub condition: Box<dyn Expression>,
    pub consequence: Box<BlockStatement>,
    pub alternative: Option<Box<BlockStatement>>,
}

pub struct FnLiteral {
    /// The 'fn' token
    pub token: Token,
    pub parameters: Vec<Identifier>,
    pub body: Box<BlockStatement>,
}

pub struct CallExpression {
    /// The '(' token
    pub token: Token,
    pub function: Box<dyn Expression>,
    pub arguments: Vec<Box<dyn Expression>>,
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

impl Node for FnLiteral {
    fn token_literal(&self) -> Literal {
        self.token.literal()
    }
}

impl Statement for FnLiteral {
    fn statement_node(&self) {
        // Implementation can be empty
    }

    fn as_any(&self) -> &dyn Any {
        self
    }
}

impl Expression for FnLiteral {
    fn expression_node(&self) {}
    fn as_any(&self) -> &dyn Any {
        self
    }
}

impl ToString for FnLiteral {
    fn to_string(&self) -> String {
        let mut buf = String::new();
        buf
    }
}

impl ToString for CallExpression {
    fn to_string(&self) -> String {
        let mut buf = String::new();
        buf.push_str(&self.function.to_string());
        buf.push_str("(");
        for (i, arg) in self.arguments.iter().enumerate() {
            buf.push_str(&arg.to_string());
            if i + 1 != self.arguments.len() {
                buf.push_str(", ");
            }
        }
        buf.push_str(")");
        buf
    }
}

impl Node for CallExpression {
    fn token_literal(&self) -> Literal {
        self.token.literal()
    }
}

impl Statement for CallExpression {
    fn statement_node(&self) {}
    fn as_any(&self) -> &dyn Any {
        self
    }
}

impl Expression for CallExpression {
    fn expression_node(&self) {}
    fn as_any(&self) -> &dyn Any {
        self
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
