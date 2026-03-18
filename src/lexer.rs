#![allow(clippy::trivial_regex)]
use lazy_regex::{lazy_regex, Lazy, Regex};

use crate::token::Error;
use crate::token::Token;

pub type Spanned<T> = (usize, T, usize);

/* By default Regex looks for substring matches, that's why we prefix each of these
with ^ so that it always matches from the start of the remaining input */
static CONST: Lazy<Regex> = lazy_regex!(r"^[a-z][_a-zA-Z0-9]*");
static VAR: Lazy<Regex> = lazy_regex!(r"^[A-Z][_a-zA-Z0-9]*");
static NUMBER: Lazy<Regex> = lazy_regex!(r"^[0-9][0-9]*");
static COMMENT: Lazy<Regex> = lazy_regex!(r"^#[^\n]*\n");
static NEWLINE: Lazy<Regex> = lazy_regex!(r"^\n");
static WS: Lazy<Regex> = lazy_regex!(r"^[[:blank:]]");
static USE: Lazy<Regex> = lazy_regex!(r"^\$use");
static QUIT: Lazy<Regex> = lazy_regex!(r"^\$quit");
static GOAL: Lazy<Regex> = lazy_regex!(r"^\?-");
static FROM: Lazy<Regex> = lazy_regex!(r"^:-");
static TRUE: Lazy<Regex> = lazy_regex!(r"^true");
static STRING: Lazy<Regex> = lazy_regex!(r#"^"[^"]*""#);
static LPAREN: Lazy<Regex> = lazy_regex!(r"^\(");
static RPAREN: Lazy<Regex> = lazy_regex!(r"^\)");
static LBRACKET: Lazy<Regex> = lazy_regex!(r"^\[");
static RBRACKET: Lazy<Regex> = lazy_regex!(r"^\]");
static COMMA: Lazy<Regex> = lazy_regex!(r"^,");
static PERIOD: Lazy<Regex> = lazy_regex!(r"^\.");
static PIPE: Lazy<Regex> = lazy_regex!(r"^\|");

pub struct Lexer<'input> {
    text: &'input str,
    line: usize,
    pos: usize,
}

impl<'input> Lexer<'input> {
    pub fn new(text: &'input str) -> Lexer<'input> {
        Lexer {
            text,
            line: 1,
            pos: 0,
        }
    }

    fn match_and_consume<F>(
        text: &mut &'input str,
        pos: &mut usize,
        re: &Regex,
        action: F,
    ) -> Option<Token<'input>>
    where
        F: Fn(&'input str) -> Token,
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
                self.pos += mat.end();
                self.text = &self.text[mat.end()..];
                continue;
            } else if let Some(mat) = NEWLINE.find(self.text) {
                self.line += 1;
                self.pos += mat.end();
                self.text = &self.text[mat.end()..];
                continue;
            } else if let Some(mat) = WS.find(self.text) {
                self.pos += mat.end();
                self.text = &self.text[mat.end()..];
                continue;
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
        self.next_token().map(|t| Ok((0, t, 0)))
    }
}
