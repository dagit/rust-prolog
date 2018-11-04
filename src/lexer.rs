#![cfg_attr(feature = "cargo-clippy", allow(trivial_regex))]
use regex::Regex;

use token::Token;
use token::Error;

pub type Spanned<T> = (usize, T, usize);

/* By default Regex looks for substring matches, that's why we prefix each of these
with ^ so that it always matches from the start of the remaining input */
lazy_static! {
    static ref CONST   : Regex = Regex::new(r"^[a-z][_a-zA-Z0-9]*").unwrap();
    static ref VAR     : Regex = Regex::new(r"^[A-Z][_a-zA-Z0-9]*").unwrap();
    static ref NUMBER  : Regex = Regex::new(r"^[0-9][0-9]*"       ).unwrap();
    static ref COMMENT : Regex = Regex::new(r"^#[^\n]*\n"         ).unwrap();
    static ref NEWLINE : Regex = Regex::new(r"^\n"                ).unwrap();
    static ref WS      : Regex = Regex::new(r"^[[:blank:]]"       ).unwrap();
    static ref USE     : Regex = Regex::new(r"^\$use"             ).unwrap();
    static ref QUIT    : Regex = Regex::new(r"^\$quit"            ).unwrap();
    static ref GOAL    : Regex = Regex::new(r"^\?-"               ).unwrap();
    static ref FROM    : Regex = Regex::new(r"^:-"                ).unwrap();
    static ref TRUE    : Regex = Regex::new(r"^true"              ).unwrap();
    static ref STRING  : Regex = Regex::new(r#"^"[^"]*""#         ).unwrap();
    static ref LPAREN  : Regex = Regex::new(r"^\("                ).unwrap();
    static ref RPAREN  : Regex = Regex::new(r"^\)"                ).unwrap();
    static ref LBRACKET: Regex = Regex::new(r"^\["                ).unwrap();
    static ref RBRACKET: Regex = Regex::new(r"^\]"                ).unwrap();
    static ref COMMA   : Regex = Regex::new(r"^,"                 ).unwrap();
    static ref PERIOD  : Regex = Regex::new(r"^\."                ).unwrap();
    static ref PIPE    : Regex = Regex::new(r"^\|"                ).unwrap();
}

pub struct Lexer<'input> {
    text    : &'input str,
    line    : usize,
    pos     : usize,
}

impl<'input> Lexer<'input> {
    pub fn new(text: &'input str) -> Lexer<'input> {
        Lexer {
            text    : text,
            line    : 1,
            pos     : 0,
        }
    }

    fn match_and_consume<F>(text: &mut &'input str, pos: &mut usize, re: &Regex, action: F)
                            -> Option<Token<'input>>
        where F: Fn(&'input str) -> Token
    {
        if let Some(mat) = re.find(text) {
            *pos += mat.end();
            let ret = Some(action(&text[mat.start()..mat.end()]));
            *text = &text[mat.end()..];
            ret
        } else {
            None
        }
    }

    pub fn next_token(&mut self) -> Option<Token<'input>> {
        /* Ignore comments and whitespace. We separate newline from the other
        whitespace so that we can count line numbers
         */
        loop {
            if let Some(mat) = COMMENT.find(self.text) {
                self.line += 1;
                self.pos  += mat.end();
                self.text = &self.text[mat.end()..];
                continue
            } else if let Some(mat) = NEWLINE.find(self.text) {
                self.line += 1;
                self.pos  += mat.end();
                self.text = &self.text[mat.end()..];
                continue
            } else if let Some(mat) = WS.find(self.text) {
                self.pos += mat.end();
                self.text = &self.text[mat.end()..];
                continue
            }
            break;
        }

        macro_rules! actions {
            ( $( $x:expr => $y:expr ),* ) => {
                if false { None } /* 'if false' just to make the rust syntax below more uniform */
                $(
                    else if let t@Some(_) = Lexer::match_and_consume(&mut self.text,
                                                                    &mut self.pos,
                                                                    &$x,
                                                                    $y) { t }
                )*
                else { None }
            };
        }

        /* Lexers should match the longest string they can, so we list the
        variable length regular expressions first to achieve maximal munch */
        actions![ CONST    => |s:&'input str| Token::CONST(s),
                  VAR      => |s:&'input str| Token::VAR(s),
                  NUMBER   => |s:&'input str| Token::NUMBER(s),
                  USE      => |_| Token::USE,
                  QUIT     => |_| Token::QUIT,
                  GOAL     => |_| Token::GOAL,
                  FROM     => |_| Token::FROM,
                  TRUE     => |_| Token::TRUE,
                  STRING   => |s:&'input str| Token::STRING(&s[1..s.len()-1]),
                  LPAREN   => |_| Token::LPAREN,
                  RPAREN   => |_| Token::RPAREN,
                  LBRACKET => |_| Token::LBRACKET,
                  RBRACKET => |_| Token::RBRACKET,
                  COMMA    => |_| Token::COMMA,
                  PERIOD   => |_| Token::PERIOD,
                  PIPE     => |_| Token::PIPE
        ]
    }
}

impl<'input> Iterator for Lexer<'input> {
    type Item = Result<Spanned<Token<'input>>, Error>;

    fn next(&mut self) -> Option<Self::Item> {
        match self.next_token() {
            /* TODO: fix this span */
            Some(t) => Some(Ok((0,t,0))),
            None    => None,
        }
    }
}
