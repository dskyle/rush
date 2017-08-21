use ast::{Pos, Span};
use std::collections::VecDeque;
use regex::Regex;

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum Tok {
    Ident(String),
    NakedString(String),
    SingleString(String),
    DoubleString(String),
    LParen,
    RParen,
    LBrace,
    RBrace,
    LSquare,
    RSquare,
    Comma,
    Semi,
    Range,
    Colon,
    Pipe,
    LBracePipe,
    LambdaOpen,
    Amp,
    Lt,
    Gt,
    Assign,
    Into,
    AssignIfNull,
    Suffix,
    Prefix,
    Let,
    Global,
    Sys,
    Read,
    Recv,
    If,
    Else,
    While,
    For,
    Iter,
    Match,
    MatchAll,
    Return,
    Break,
    Continue,
    Func,
    Or,
    And,
    Whitespace,
    NewLine(usize),
    Comment(String),
    Var(String),
    VarLBrace(String),
    Exec(String),
    ExecLParen(String),
    ExecLSquare(String),
    Redir(u8, u8),
    Rex(String),
    Error(String),
}

lexer! {
    fn take_token(text: 'a) -> Tok;

    r##"#[^\n\r]*"## => Tok::Comment(text.into()),

    r##"([ \t]*(\n|\r\n))+[ \t]*"## =>
        Tok::NewLine(text.chars().filter(|ch| *ch == '\n').count()),
    r##"[ \t\r]+"## => Tok::Whitespace,

    r##"let"## => Tok::Let,
    r##"global"## => Tok::Global,
    r##"sys"## => Tok::Sys,
    r##"read"## => Tok::Read,
    r##"recv"## => Tok::Recv,
    r##"if"## => Tok::If,
    r##"else"## => Tok::Else,
    r##"while"## => Tok::While,
    r##"for"## => Tok::For,
    r##"iter"## => Tok::Iter,
    r##"fn"## => Tok::Func,
    r##"match"## => Tok::Match,
    r##"match_all"## => Tok::MatchAll,
    r##"break"## => Tok::Break,
    r##"continue"## => Tok::Continue,
    r##"return"## => Tok::Return,

    r##"="## => Tok::Assign,
    r##"=>"## => Tok::Into,
    r##"\?="## => Tok::AssignIfNull,
    r##"\+="## => Tok::Suffix,
    r##"^="## => Tok::Prefix,
    r##":"## => Tok::Colon,
    r##","## => Tok::Comma,
    r##";"## => Tok::Semi,
    r##"\.\.\."## => Tok::Range,

    r##"\|\|"## => Tok::Or,
    r##"\&\&"## => Tok::And,

    r##"\("## => Tok::LParen,
    r##"\)"## => Tok::RParen,

    r##"$\|"## => Tok::LambdaOpen,

    r##"\{"## => Tok::LBrace,
    r##"\{\|"## => Tok::LBracePipe,
    r##"\}"## => Tok::RBrace,

    r##"\["## => Tok::LSquare,
    r##"\]"## => Tok::RSquare,

    r##"\$(|,|-|,-|-,)\{"## => Tok::VarLBrace(text.into()),
    r##"\$\("## => Tok::ExecLParen(text.into()),
    r##"\$(|,|-|,-|-,)\["## => Tok::ExecLSquare(text.into()),

    r##"\$(|,)"## => Tok::Var(text.into()),

    r##"'([^'])*'"## => Tok::SingleString(text.trim_matches('\'').into()),
    r##""([^\\"]|\\"|\\.)*""## => Tok::DoubleString(text[1..(text.len() - 1)].into()),
    r##"$/([^\\/]|\\/|\\.)*/"## => Tok::Rex(text[2..(text.len() - 1)].into()),

    r##"[0-9]>\&[0-9]"## => { let t = text.as_bytes(); Tok::Redir(t[0] - '0' as u8, t[3] - '0' as u8) },
    r##">\&[0-9]"## => { let t = text.as_bytes(); Tok::Redir(1, t[2] - '0' as u8) },

    r##"\|"## => Tok::Pipe,
    r##"\&"## => Tok::Amp,
    r##"<"## => Tok::Lt,
    r##">"## => Tok::Gt,

    r##"Err!"## => Tok::Ident(text.into()),
    //r##"[_a-zA-Z][_a-zA-Z0-9]*"## => Tok::Ident(text.into()),
    r##"[_a-zA-Z][_a-zA-Z0-9]*(::[_a-zA-Z][_a-zA-Z0-9]*)*"## => Tok::Ident(text.into()),
    //r##"[_a-zA-Z][_a-zA-Z0-9]*(::[_a-zA-Z][_a-zA-Z0-9]*)*\.[_a-zA-Z][_a-zA-Z0-9]*"## => Tok::Ident(text.into()),
    r##"[^ \r\t\n"'\\\$\(\)\{\}\[\]&|,;]+"## => Tok::NakedString(text.into()),

    r##"."## => Tok::Error(text.into()),
}

static NAKED_STRING_RE: &str = r##"^[^ \r\t\n"'\\\$\(\)\{\}\[\]&|,;]+$"##;

pub fn naked_string_regex() -> &'static Regex {
    lazy_static! {
        static ref RE: Regex = Regex::new(NAKED_STRING_RE).unwrap();
    }
    &*RE
}

pub fn is_valid_naked_string(s: &str) -> bool {
    naked_string_regex().is_match(s)
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
enum KWAllow {
    All,
    Assign,
    Else,
    Let,
    No,
    Colon,
}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct ContextLexer {
    context : Vec<char>,
    line : usize,
    pos : usize,
    kw : KWAllow,
}

#[derive(Debug, Eq, PartialEq, Hash)]
pub struct ContextLexerIterator<'a, 'b> {
    lexer : &'a mut ContextLexer,
    input : &'b str,
    override_queue : VecDeque<(Tok, Span)>,
}

impl<'a> ContextLexer {
    pub fn new() -> ContextLexer { ContextLexer { context: vec!(), line: 1, pos: 1, kw: KWAllow::All } }

    pub fn lex<'b>(&'a mut self, input : &'b str) -> ContextLexerIterator<'a, 'b> {
        ContextLexerIterator::<'a, 'b>{lexer: self, input: input, override_queue: VecDeque::new()}
    }

    //pub fn complete(&'a self) -> bool { self.context.len() == 0 }
}

fn pop_expect(v: &mut Vec<char>, expect: char) -> Option<LexError>
{
    let ret = v.pop();
    if let Some(ret) = ret {
        if ret == expect {
            None
        } else {
            Some(LexError::Mismatched(expect))
        }
    } else {
        Some(LexError::Mismatched(expect))
    }
}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum LexError {
    Mismatched(char),
    Unexpected(String),
}

pub fn slice_dist<S, T>(l: *const S, r: *const T) -> usize {
    let p1 = l as usize;
    let p2 = r as usize;
    if p1 > p2 { p1 - p2 } else { p2 - p1 }
}

pub fn identifier_regex() -> &'static Regex {
    lazy_static! {
        static ref RE: Regex = Regex::new(
r##"^[_a-zA-Z][_a-zA-Z0-9]*(::[_a-zA-Z][_a-zA-Z0-9]*)*$"##).unwrap();
    }
    &*RE
}

pub fn is_identifier(s: &str) -> bool {
    identifier_regex().is_match(s)
}

impl<'a, 'b> ContextLexerIterator<'a, 'b> {
    fn check_one_op(lhs: &mut &str, op: char) -> bool {
        let l = lhs.trim_right_matches(op);
        if l.len() != lhs.len() {
            *lhs = l;
            return true;
        }
        return false;
    }
    fn check_assign_op(lhs: &mut &str) -> Tok {
        if Self::check_one_op(lhs, '?') {
            Tok::AssignIfNull
        } else if Self::check_one_op(lhs, '+') {
            Tok::Suffix
        } else if Self::check_one_op(lhs, '^') {
            Tok::Prefix
        } else {
            Tok::Assign
        }
    }

    fn split_assign(&mut self, s: &String, span: Span) -> Option<Tok> {
        let split : Vec<&str> = s.splitn(3, '=').collect();
        if split.len() == 2 {
            let mut lhs = split[0];
            let rhs = split[1];
            let op = Self::check_assign_op(&mut lhs);
            if is_identifier(lhs) && (rhs.len() == 0 || is_identifier(rhs)) {
                self.override_queue.push_front((op, span));
                if rhs.len() > 0 {
                    self.override_queue.push_front((Tok::Ident(rhs.into()), span));
                }
                Some(Tok::Ident(lhs.into()))
            } else {
                return None
            }
        } else {
            None
        }
    }

    fn split_range(&mut self, s: &String, span: Span) -> Option<Tok> {
        let split : Vec<&str> = s.splitn(3, "...").collect();
        if split.len() == 2 {
            let lhs = split[0];
            let rhs = split[1];
            if lhs.len() > 0 {
                let tok = if is_identifier(lhs) {
                    Tok::Ident(lhs.into())
                } else {
                    Tok::NakedString(lhs.into())
                };
                self.override_queue.push_front((tok, span));
            }
            self.override_queue.push_front((Tok::Range, span));
            if rhs.len() > 0 {
                let tok = if is_identifier(rhs) {
                    Tok::Ident(rhs.into())
                } else {
                    Tok::NakedString(rhs.into())
                };
                self.override_queue.push_front((tok, span));
            }
            Some(self.override_queue.pop_back().unwrap().0)
        } else {
            None
        }
    }
}

impl<'a, 'b> Iterator for ContextLexerIterator<'a, 'b> {

    type Item = (Tok, Span);

    fn next(&mut self) -> Option<Self::Item> {
        if !self.override_queue.is_empty() {
            return self.override_queue.pop_back();
        }
        let begin = self.input;
        let tok = take_token(&mut self.input);
        let start_pos = Pos::new(self.lexer.line, self.lexer.pos);
        let dist = slice_dist(begin.as_ptr(), self.input.as_ptr());
        self.lexer.pos += dist;
        if let Some(tok) = tok {
            use self::KWAllow::*;

            let kw = self.lexer.kw;
            let mut next_kw = kw;

            match tok {
                Tok::LParen | Tok::ExecLParen(_) =>
                    { self.lexer.context.push(')'); next_kw = All; },

                Tok::LSquare | Tok::ExecLSquare(_) =>
                    { self.lexer.context.push(']'); next_kw = All; },

                Tok::LBrace | Tok::VarLBrace(_) | Tok::LBracePipe =>
                    { self.lexer.context.push('}'); next_kw = All; },

                Tok::RParen => {
                    next_kw = No;
                    pop_expect(&mut self.lexer.context, ')');
                },

                Tok::RSquare => {
                    next_kw = No;
                    pop_expect(&mut self.lexer.context, ']');
                },

                Tok::RBrace => {
                    next_kw = Else;
                    pop_expect(&mut self.lexer.context, '}');
                },

                Tok::NewLine(c) => {
                    next_kw = All;
                    self.lexer.line += c;
                    self.lexer.pos = 1;
                },

                Tok::Comment(_) => {
                    next_kw = All;
                    self.lexer.line += 1;
                    self.lexer.pos = 1;
                },

                Tok::Semi | Tok::Assign | Tok::AssignIfNull | Tok::Suffix |
                    Tok::Prefix | Tok::And | Tok::Or | Tok::Pipe |
                    Tok::Else | Tok::Into => { next_kw = All; },

                Tok::If | Tok::While => { next_kw = Let; },

                Tok::Let | Tok::Global | Tok::Sys =>
                    { next_kw = Assign; }

                Tok::Colon =>
                    { next_kw = Colon; }

                Tok::For | Tok::Func | Tok::Match | Tok::MatchAll | Tok::Comma |
                    Tok::Break | Tok::Continue | Tok::Return |
                    Tok::Gt | Tok::Lt |
                    Tok::Var(_) | Tok::Exec(_) | Tok::Redir(_, _) |
                    Tok::Ident(_) | Tok::NakedString(_) | Tok::Range |
                    Tok::SingleString(_) | Tok::DoubleString(_) |
                    Tok::Rex(_) | Tok::Read | Tok::Recv | Tok::Iter |
                    Tok::LambdaOpen =>
                        { next_kw = No; },

                Tok::Error(_) => {},
                Tok::Whitespace | Tok::Amp => {},
            }

            let end_pos = Pos::new(self.lexer.line, self.lexer.pos);
            let span = Span::new(start_pos, end_pos);

            let tok = if let Tok::Iter = tok {
                if kw == Colon { tok } else { Tok::Ident("iter".into()) }
            } else { tok };
            let tok = match kw {
                All => tok,
                No | Assign | Else | Let | Colon => match tok {
                    Tok::If => Tok::Ident("if".into()),
                    Tok::For => Tok::Ident("for".into()),
                    Tok::While => Tok::Ident("while".into()),
                    Tok::Let => if kw == Let { tok } else { Tok::Ident("let".into()) },
                    Tok::Read => if kw == Let { tok } else { Tok::Ident("read".into()) },
                    Tok::Recv => if kw == Let { tok } else { Tok::Ident("recv".into()) },
                    Tok::Global => Tok::Ident("global".into()),
                    Tok::Sys => Tok::Ident("sys".into()),
                    Tok::Func => Tok::Ident("fn".into()),
                    Tok::Match => Tok::Ident("match".into()),
                    Tok::MatchAll => Tok::Ident("match_all".into()),
                    Tok::Break => Tok::Ident("break".into()),
                    Tok::Continue => Tok::Ident("continue".into()),
                    Tok::Return => Tok::Ident("return".into()),

                    Tok::Else => if kw == Else { tok } else { Tok::Ident("else".into()) },

                    _ => tok,
                }
            };

            let tok = match kw {
                All | Assign | Colon => match tok {
                    Tok::NakedString(s) => {
                        if let Some(t) = self.split_assign(&s, span) {
                            t
                        } else {
                            Tok::NakedString(s.into())
                        }
                    },
                    _ => tok,
                },
                _ => tok,
            };

            let tok = match tok {
                Tok::NakedString(s) =>
                    if let Some(t) = self.split_range(&s, span) {
                        t
                    } else {
                        Tok::NakedString(s.into())
                    },
                _ => tok,
            };

            self.lexer.kw = next_kw;

            if let Tok::Comment(..) = tok {
                self.next()
            } else {
                Some((tok, span))
            }
        } else {
            None
        }
    }
}
