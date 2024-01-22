use std::fmt::Display;

use ordered_float::OrderedFloat;

use crate::scanner::Pos;

#[derive(Debug, PartialEq, Eq)]
pub struct Program(pub Vec<Stmt>);

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FunDecl {
    pub name: String,
    pub parameters: Vec<String>,
    pub body: Box<Stmt>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ClassBody {
    pub methods: Vec<FunDecl>,
    pub class_methods: Vec<FunDecl>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Stmt {
    // Its possible defining this pos across all statements is wasteful of space
    pub pos: Pos,
    pub inner: StmtInner,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum StmtInner {
    VarDecl {
        name: String,
        init: Option<Expr>,
    },
    FunDecl(FunDecl),
    ClassDecl {
        name: String,
        parent: Option<Expr>,
        body: ClassBody,
    },
    Expr(Expr),
    Print(Expr),
    Block(Vec<Stmt>),
    If {
        expr: Expr,
        then: Box<Stmt>,
        or_else: Option<Box<Stmt>>,
    },
    Loop {
        expr: Expr,
        body: Box<Stmt>,
    },
    Break,
    Return(Option<Expr>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Expr {
    // Its possible defining this pos across all expr types is wasteful of space
    pub pos: Pos,
    pub inner: ExprInner,
}

#[derive(Clone, Debug, PartialEq, Eq)]

pub enum ExprInner {
    Ternary {
        test: Box<Expr>,
        if_true: Box<Expr>,
        if_false: Box<Expr>,
    },
    Binary {
        left: Box<Expr>,
        op: BinaryOp,
        right: Box<Expr>,
    },
    Unary {
        op: UnaryOp,
        expr: Box<Expr>,
    },
    Group(Box<Expr>),
    Literal(Literal),
    Variable {
        name: String,
        // How many scopes upwards to resolve
        // This may be a precise number for things in global scope, however, certain bits like global variables are not
        // included
        scope_distance: Option<u32>,
    },
    This {
        scope_distance: Option<u32>,
    },
    Super {
        method: String,
        scope_distance: Option<u32>,
    },
    Assignment {
        target: String,
        scope_distance: Option<u32>,
        expr: Box<Expr>,
    },
    Logical {
        left: Box<Expr>,
        op: LogicalOp,
        right: Box<Expr>,
    },
    Call {
        callee: Box<Expr>,
        arguments: Vec<Expr>,
    },
    Get {
        object: Box<Expr>,
        property: String,
    },
    Set {
        object: Box<Expr>,
        property: String,
        value: Box<Expr>,
    },
}

impl<'a> Display for Expr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.inner {
            ExprInner::Literal(lit) => write!(f, "{}", lit),
            ExprInner::Group(expr) => write!(f, "(group {})", expr),
            ExprInner::Unary { op, expr } => write!(f, "({} {})", op, expr),
            ExprInner::Binary { left, op, right } => write!(f, "({} {} {})", op, left, right),
            ExprInner::Ternary {
                test,
                if_true,
                if_false,
            } => write!(f, "(? {} : {} {})", test, if_true, if_false),
            ExprInner::Variable {
                name,
                scope_distance: _,
            } => write!(f, "(ident {})", name),
            ExprInner::This { scope_distance: _ } => f.write_str("(this)"),
            ExprInner::Super {
                method,
                scope_distance: _,
            } => f.write_str("(super method)"),
            ExprInner::Assignment {
                target,
                scope_distance: _,
                expr,
            } => write!(f, "(= {} {})", target, expr),
            ExprInner::Logical { left, op, right } => write!(f, "({} {} {})", op, left, right),
            ExprInner::Call { callee, arguments } => {
                write!(f, "(call {}", callee)?;
                for arg in arguments {
                    write!(f, " {}", arg)?;
                }
                f.write_str(")")
            }
            ExprInner::Get { object, property } => write!(f, "(get {} {})", object, property),
            ExprInner::Set {
                object,
                property,
                value,
            } => write!(f, "(set {} {} {})", object, property, value),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BinaryOp {
    Equal,
    NotEqual,
    LessThan,
    LessThanEqual,
    GreaterThan,
    GreaterThanEqual,
    Add,
    Subtract,
    Multiply,
    Divide,
}

impl Display for BinaryOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            BinaryOp::Equal => f.write_str("=="),
            BinaryOp::NotEqual => f.write_str("!="),
            BinaryOp::LessThan => f.write_str("<"),
            BinaryOp::LessThanEqual => f.write_str("<="),
            BinaryOp::GreaterThan => f.write_str(">"),
            BinaryOp::GreaterThanEqual => f.write_str(">="),
            BinaryOp::Add => f.write_str("+"),
            BinaryOp::Subtract => f.write_str("-"),
            BinaryOp::Multiply => f.write_str("*"),
            BinaryOp::Divide => f.write_str("/"),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum UnaryOp {
    Not,
    Negative,
}

impl Display for UnaryOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            UnaryOp::Not => f.write_str("!"),
            UnaryOp::Negative => f.write_str("-"),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LogicalOp {
    And,
    Or,
}

impl Display for LogicalOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LogicalOp::And => f.write_str("and"),
            LogicalOp::Or => f.write_str("or"),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Literal {
    Number(OrderedFloat<f64>),
    String(String),
    Boolean(bool),
    Nil,
}

impl<'a> Display for Literal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Literal::Number(OrderedFloat(dbl)) => write!(f, "{}", dbl),
            Literal::String(s) => f.write_str(s),
            Literal::Boolean(b) => write!(f, "{}", b),
            Literal::Nil => f.write_str("nil"),
        }
    }
}
