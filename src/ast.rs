use std::fmt::Display;

use ordered_float::OrderedFloat;

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
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Stmt {
    VarDecl {
        name: String,
        init: Option<Expr>,
    },
    FunDecl(FunDecl),
    ClassDecl {
        name: String,
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
pub enum Expr {
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
    Identifier {
        name: String,
        // How many scopes upwards to resolve
        // This may be a precise number for things in global scope, however, certain bits like global variables are not
        // included
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
        match self {
            Expr::Literal(lit) => write!(f, "{}", lit),
            Expr::Group(expr) => write!(f, "(group {})", expr),
            Expr::Unary { op, expr } => write!(f, "({} {})", op, expr),
            Expr::Binary { left, op, right } => write!(f, "({} {} {})", op, left, right),
            Expr::Ternary {
                test,
                if_true,
                if_false,
            } => write!(f, "(? {} : {} {})", test, if_true, if_false),
            Expr::Identifier {
                name,
                scope_distance: _,
            } => write!(f, "(ident {})", name),
            Expr::Assignment {
                target,
                scope_distance: _,
                expr,
            } => write!(f, "(= {} {})", target, expr),
            Expr::Logical { left, op, right } => write!(f, "({} {} {})", op, left, right),
            Expr::Call { callee, arguments } => {
                write!(f, "(call {}", callee)?;
                for arg in arguments {
                    write!(f, " {}", arg)?;
                }
                f.write_str(")")
            }
            Expr::Get { object, property } => write!(f, "(get {} {})", object, property),
            Expr::Set {
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
