#[derive(PartialEq, Eq, Hash, Clone)]
pub struct Name {
    name: String,
}

impl Name {
    pub fn from(name: String) -> Name {
        Name { name }
    }

    pub fn as_string(&self) -> &String {
        &self.name
    }
}

#[derive(Clone)]
pub struct Code {
    statements: Vec<Statement>,
}

impl Code {
    pub fn from(statements: Vec<Statement>) -> Code {
        Code { statements }
    }

    pub fn as_vec(&self) -> &Vec<Statement> {
        &self.statements
    }
}

#[derive(Clone)]
pub struct Callable {
    pub parameters: Vec<Name>,
    pub body: Code,
}

#[derive(Clone)]
pub enum Statement {
    NamespaceDef { name: Name, body: Code },
    CallableDef { name: Name, function: Callable },
    Assignment { target: Name, expr: Expr },

    Expression(Expr),
}

#[derive(Clone)]
pub struct Binop {
    pub lhs: Box<Expr>,
    pub rhs: Box<Expr>,
}

#[derive(Clone)]
pub enum Expr {
    And(Binop),
    Or(Binop),
    Not { operand: Box<Expr> },

    Equals(Binop),
    LessThan(Binop),
    GreaterThan(Binop),

    Add(Binop),
    Sub(Binop),
    Mul(Binop),
    Div(Binop),
    Mod(Binop),

    Call { callable: Box<Expr>, arguments: Vec<Expr> },
    Trampoline { expr: Box<Expr> },

    NamedValue { name: Name },
    StringLiteral { value: String },
    CharLiteral { value: char },
    IntLiteral { value: i64 },
    BoolLiteral { value: bool },
    BlockLiteral { value: Callable },
}
