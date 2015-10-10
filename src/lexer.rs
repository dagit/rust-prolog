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
        self.pos += end;
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

    if let t@Some(_) = Lexer::match_and_consume(&mut self.text,
                                                &mut self.pos,
                                                &self.const_,
                                                |s:&'input str| Token::CONST(s))
    {
      t
    } else if let t@Some(_) = Lexer::match_and_consume(&mut self.text,
                                                       &mut self.pos,
                                                       &self.var,
                                                       |s: &'input str| Token::VAR(s))
    {
      t
    } else if let t@Some(_) = Lexer::match_and_consume(&mut self.text,
                                                       &mut self.pos,
                                                       &self.use_,
                                                       |_| Token::USE)
    {
      t
    } else if let t@Some(_) = Lexer::match_and_consume(&mut self.text,
                                                       &mut self.pos,
                                                       &self.quit,
                                                       |_| Token::QUIT)
    {
      t
    } else if let t@Some(_) = Lexer::match_and_consume(&mut self.text,
                                                       &mut self.pos,
                                                       &self.goal,
                                                       |_| Token::GOAL)
    {
      t
    } else if let t@Some(_) = Lexer::match_and_consume(&mut self.text,
                                                       &mut self.pos,
                                                       &self.from,
                                                       |_| Token::FROM)
    {
      t
    } else if let t@Some(_) = Lexer::match_and_consume(&mut self.text,
                                                       &mut self.pos,
                                                       &self.true_,
                                                       |_| Token::TRUE)
    {
      t
    } else if let t@Some(_) = Lexer::match_and_consume(&mut self.text,
                                                       &mut self.pos,
                                                       &self.string,
                                                       |s:&'input str| Token::STRING(s))
    {
      t
    } else if let t@Some(_) = Lexer::match_and_consume(&mut self.text,
                                                       &mut self.pos,
                                                       &self.lparen,
                                                       |_| Token::LPAREN)
    {
      t
    } else if let t@Some(_) = Lexer::match_and_consume(&mut self.text,
                                                       &mut self.pos,
                                                       &self.rparen,
                                                       |_| Token::RPAREN)
    {
      t
    } else if let t@Some(_) = Lexer::match_and_consume(&mut self.text,
                                                       &mut self.pos,
                                                       &self.comma,
                                                       |_| Token::COMMA)
    {
      t
    } else if let t@Some(_) = Lexer::match_and_consume(&mut self.text,
                                                       &mut self.pos,
                                                       &self.period,
                                                       |_| Token::PERIOD)
    {
      t
    } else {
      None
    }
  }
}

/*
rule token = parse
    '#' [^'\n']* '\n' { incr_linenum lexbuf; token lexbuf }
  | '\n'            { incr_linenum lexbuf; token lexbuf }
  | [' ' '\t']      { token lexbuf }
  | "$use"          { USE }
  | "$quit"         { QUIT }
  | "?-"            { GOAL }
  | ":-"            { FROM }
  | "true"          { TRUE }
  | '\"' [^'\"']* '\"' { let str = lexeme lexbuf in
                        STRING (String.sub str 1 (String.length str - 2)) }
  | '('             { LPAREN }
  | ')'             { RPAREN }
  | ','             { COMMA }
  | '.'             { PERIOD }
  | const           { CONST (lexeme lexbuf) }
  | var             { VAR (lexeme lexbuf) }
  | eof             { EOF }
*/
