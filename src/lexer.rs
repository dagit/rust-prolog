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

    if let Some((start,end)) = self.const_.find(self.text) {
      self.pos += end;
      let ret = Some(Token::CONST(&self.text[start..end]));
      self.text = &self.text[end..];
      ret
    } else if let Some((start,end)) = self.var.find(self.text) {
      self.pos += end;
      let ret = Some(Token::VAR(&self.text[start..end]));
      self.text = &self.text[end..];
      ret
    } else if let Some((_,end)) = self.use_.find(self.text) {
      self.pos += end;
      let ret = Some(Token::USE);
      self.text = &self.text[end..];
      ret
    } else if let Some((_,end)) = self.quit.find(self.text) {
      self.pos += end;
      let ret = Some(Token::QUIT);
      self.text = &self.text[end..];
      ret
    } else if let Some((_,end)) = self.goal.find(self.text) {
      self.pos += end;
      let ret = Some(Token::GOAL);
      self.text = &self.text[end..];
      ret
    } else if let Some((_,end)) = self.from.find(self.text) {
      self.pos += end;
      let ret = Some(Token::FROM);
      self.text = &self.text[end..];
      ret
    } else if let Some((_,end)) = self.true_.find(self.text) {
      self.pos += end;
      let ret = Some(Token::TRUE);
      self.text = &self.text[end..];
      ret
    } else if let Some((start,end)) = self.string.find(self.text) {
      self.pos += end;
      let ret = Some(Token::STRING(&self.text[start..end]));
      self.text = &self.text[end..];
      ret
    } else if let Some((_,end)) = self.lparen.find(self.text) {
      self.pos += end;
      let ret = Some(Token::LPAREN);
      self.text = &self.text[end..];
      ret
    } else if let Some((_,end)) = self.rparen.find(self.text) {
      self.pos += end;
      let ret = Some(Token::RPAREN);
      self.text = &self.text[end..];
      ret
    } else if let Some((_,end)) = self.comma.find(self.text) {
      self.pos += end;
      let ret = Some(Token::COMMA);
      self.text = &self.text[end..];
      ret
    } else if let Some((_,end)) = self.period.find(self.text) {
      self.pos += end;
      let ret = Some(Token::PERIOD);
      self.text = &self.text[end..];
      ret
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
