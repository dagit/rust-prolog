use regex::Regex;

use token::Token;


pub struct Lexer<'input> {
  text    : &'input str,
  line    : usize,
  pos     : usize,
  const_  : Regex,
  var     : Regex,
  comment : Regex,
  newline : Regex,
  ws      : Regex,
  use_    : Regex,
  quit    : Regex,
  goal    : Regex,
  from    : Regex,
  true_   : Regex,
  string  : Regex,
  lparen  : Regex,
  rparen  : Regex,
  comma   : Regex,
  period  : Regex,
}

impl<'input> Lexer<'input> {
  pub fn new(text: &'input str) -> Lexer<'input> {
    Lexer {
      text    : text,
      line    : 0,
      pos     : 0,
      /* By default Regex looks for substring matches, that's why we prefix each of these
         with ^ so that it always matches from the start of the remaining input */
      const_  : Regex::new(r"^[a-z][_a-zA-Z0-9]*").unwrap(),
      var     : Regex::new(r"^[A-Z][_a-zA-Z0-9]*").unwrap(),
      comment : Regex::new(r"^#[^\n]*\n"         ).unwrap(),
      newline : Regex::new(r"^\n"                ).unwrap(),
      ws      : Regex::new(r"^[:blank:]"         ).unwrap(),
      use_    : Regex::new(r"^\$use"             ).unwrap(),
      quit    : Regex::new(r"^\$quit"            ).unwrap(),
      goal    : Regex::new(r"^\?-"               ).unwrap(),
      from    : Regex::new(r"^:-"                ).unwrap(),
      true_   : Regex::new(r"^true"              ).unwrap(),
      string  : Regex::new(r#"^"[^"]*""#         ).unwrap(),
      lparen  : Regex::new(r"^\("                ).unwrap(),
      rparen  : Regex::new(r"^\)"                ).unwrap(),
      comma   : Regex::new(r"^,"                 ).unwrap(),
      period  : Regex::new(r"^\."                ).unwrap(),
    }
  }

  fn match_and_consume<F>(text: &mut &'input str, pos: &mut usize, re: &Regex, action: F)
  -> Option<Token<'input>>
  where F: Fn(&'input str) -> Token
  {
    if let Some((start,end)) = re.find(text) {
      *pos += end;
      let ret = Some(action(&text[start..end]));
      *text = &text[end..];
      ret
    } else {
      None
    }
  }

  pub fn next(&mut self) -> Option<Token> {
    /* Ignore comments and whitespace. We separate newline from the other
       whitespace so that we can count line numbers
    */
    loop {
      if let Some((_,end)) = self.comment.find(self.text) {
        self.line += 1;
        self.pos  += end;
        self.text = &self.text[end..];
        continue
      } else if let Some((_,end)) = self.newline.find(self.text) {
        self.line += 1;
        self.pos  += end;
        self.text = &self.text[end..];
        continue
      } else if let Some((_,end)) = self.ws.find(self.text) {
        self.pos += end;
        self.text = &self.text[end..];
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
    actions![ self.const_ => |s:&'input str| Token::CONST(s),
              self.var    => |s:&'input str| Token::VAR(s),
              self.use_   => |_| Token::USE,
              self.quit   => |_| Token::QUIT,
              self.goal   => |_| Token::GOAL,
              self.from   => |_| Token::FROM,
              self.true_  => |_| Token::TRUE,
              self.string => |s:&'input str| Token::STRING(&s[1..s.len()-1]),
              self.lparen => |_| Token::LPAREN,
              self.rparen => |_| Token::RPAREN,
              self.comma  => |_| Token::COMMA,
              self.period => |_| Token::PERIOD
            ]
  }
}
