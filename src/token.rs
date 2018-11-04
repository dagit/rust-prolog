#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ErrorCode {
    UnrecognizedToken,
    UnterminatedStringLiteral,
    ExpectedStringLiteral,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Error {
    pub location: usize,
    pub code: ErrorCode
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Token<'input> {
    VAR(&'input str),
    NUMBER(&'input str),
    CONST(&'input str),
    FROM,
    COMMA,
    TRUE,
    PERIOD,
    PIPE,
    LPAREN,
    RPAREN,
    LBRACKET,
    RBRACKET,
    GOAL,
    QUIT,
    USE,
    STRING(&'input str),
    EOF,
}

