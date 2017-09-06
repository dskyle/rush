use ast::{Pos, Span};

pub use lex::Tok;

lexer! {
    fn take_token(text: 'a) -> Tok;

    r##"#[^\n\r]*"## => Tok::Comment(text.into()),

    r##"([ \t]*(\n|\r\n))+[ \t]*"## =>
        Tok::NewLine(text.chars().filter(|ch| *ch == '\n').count()),
    r##"[ \t\r]+"## => Tok::Whitespace,

    r##","## => Tok::Comma,

    r##"\("## => Tok::LParen,
    r##"\)"## => Tok::RParen,

    r##"'([^'])*'"## => Tok::SingleString(text.trim_matches('\'').into()),
    r##""([^\\"]|\\"|\\.)*""## => Tok::DoubleString(text[1..(text.len() - 1)].into(), true),
    r##"$/([^\\/]|\\/|\\.)*/"## => Tok::Rex(text[2..(text.len() - 1)].into()),

    r##"Err!"## => Tok::Ident(text.into()),
    r##"[_a-zA-Z][_a-zA-Z0-9]*(::[_a-zA-Z][_a-zA-Z0-9]*)*"## => Tok::Ident(text.into()),
    r##"[^ \r\t\n"'\\\(\),]+"## => Tok::NakedString(text.into()),
    r##"\\ "## => Tok::SingleString(" ".into()),
    r##"\\."## => Tok::DoubleString(text.into(), true),

    r##"."## => Tok::Error(text.into()),
}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct ValueLexer {
    line : usize,
    pos : usize,
}

#[derive(Debug, Eq, PartialEq, Hash)]
pub struct ValueLexerIterator<'a, 'b> {
    lexer : &'a mut ValueLexer,
    input : &'b str,
}

impl<'a> ValueLexer {
    pub fn new() -> ValueLexer { ValueLexer { line: 1, pos: 1 } }

    pub fn lex<'b>(&'a mut self, input : &'b str) -> ValueLexerIterator<'a, 'b> {
        ValueLexerIterator::<'a, 'b>{lexer: self, input: input}
    }
}

use lex::slice_dist;

impl<'a, 'b> Iterator for ValueLexerIterator<'a, 'b> {
    type Item = (Tok, Span);

    fn next(&mut self) -> Option<Self::Item> {
        let begin = self.input;
        let tok = take_token(&mut self.input);
        if tok == None { return None }
        let tok = tok.unwrap();
        let start_pos = Pos::new(self.lexer.line, self.lexer.pos);
        let dist = slice_dist(begin.as_ptr(), self.input.as_ptr());
        self.lexer.pos += dist;

        match tok {
            Tok::NewLine(c) => {
                self.lexer.line += c;
                self.lexer.pos = 1;
            },

            Tok::Comment(_) => {
                self.lexer.line += 1;
                self.lexer.pos = 1;
            },

            _ => {},
        }

        let end_pos = Pos::new(self.lexer.line, self.lexer.pos);
        let span = Span::new(start_pos, end_pos);
        Some((tok, span))
    }
}
