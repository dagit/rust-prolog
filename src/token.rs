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
  CONST(&'input str),
  FROM,
  COMMA,
  TRUE,
  PERIOD,
  LPAREN,
  RPAREN,
  GOAL,
  QUIT,
  SEMICOLON2,
  USE,
  STRING(&'input str),
  EOF,
}

