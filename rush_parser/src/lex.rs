use ast::{Pos, Span};
use std::collections::VecDeque;
use regex::Regex;

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum Tok {
    Ident(String),
    NakedString(String),
    SingleString(String),
    DoubleString(String, bool),
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
    DoubleColon,
    Pipe,
    LambdaOpen,
    Amp,
    Lt,
    Gt,
    Assign,
    Into,
    Member(String),
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
    VarIdent(String),
    VarLBrace(String),
    Exec(String),
    ExecLParen(String),
    ExecLSquare(String),
    Redir(u8, u8),
    Rex(String),
    Heredoc(bool, bool, bool, String),
    Error(String),
}

impl Tok {
    pub fn mk_heredoc(s: &str) -> Tok {
        let s = s.trim();
        let (as_val, s) = if s.starts_with('$') {
            (true, &s[1..])
        } else {
            (false, s)
        };
        let s = &s[2..];
        let (trim_ws, s) = if s.starts_with('-') {
            (true, &s[1..])
        } else {
            (false, s)
        };
        let (do_subst, s) = if s.starts_with('\'') {
            let s = &s[1..];
            if let Some(pos) = s.find('\'') {
                let (s, _) = s.split_at(pos);
                (false, s)
            } else {
                (false, s)
            }
        } else {
            (true, s)
        };
        let mut body = String::with_capacity(s.len() + 2);
        body.push('\n');
        body.push_str(s);
        body.push('\n');
        Tok::Heredoc(as_val, do_subst, trim_ws, body)
    }
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
    r##"fn"## => Tok::Func,
    r##"match"## => Tok::Match,
    r##"match_all"## => Tok::MatchAll,
    r##"break"## => Tok::Break,
    r##"continue"## => Tok::Continue,
    r##"return"## => Tok::Return,

    r##"="## => Tok::Assign,
    r##"=>"## => Tok::Into,
    r##"\$\.(|,|-|,-|-,)"## => Tok::Member(text.into()),
    r##"\?="## => Tok::AssignIfNull,
    r##"\+="## => Tok::Suffix,
    r##"^="## => Tok::Prefix,
    r##":"## => Tok::Colon,
    r##"::"## => Tok::DoubleColon,
    r##","## => Tok::Comma,
    r##";"## => Tok::Semi,
    r##"\.\.\."## => Tok::Range,

    r##"\|\|"## => Tok::Or,
    r##"\&\&"## => Tok::And,

    r##"\("## => Tok::LParen,
    r##"\)"## => Tok::RParen,

    r##"$\|"## => Tok::LambdaOpen,

    r##"\{"## => Tok::LBrace,
    r##"\}"## => Tok::RBrace,

    r##"\["## => Tok::LSquare,
    r##"\]"## => Tok::RSquare,

    r##"\$(|,|-|,-|-,)\{"## => Tok::VarLBrace(text.into()),
    r##"\$\("## => Tok::ExecLParen(text.into()),
    r##"\$(|,|-|,-|-,)\["## => Tok::ExecLSquare(text.into()),

    r##"\$(|,|-|,-|-,)[_a-zA-Z][_a-zA-Z0-9]*(::[_a-zA-Z][_a-zA-Z0-9]*)*"## => Tok::VarIdent(text.into()),
    r##"\$(|,|-|,-|-,)"## => Tok::Var(text.into()),

    r##"(|\$)<<(|-)[_a-zA-Z0-9]+[ \t\r]*(|\n)"## => Tok::mk_heredoc(text),
    r##"(|\$)<<(|-)'[_a-zA-Z0-9]+'[ \t\r]*(|\n)"## => Tok::mk_heredoc(text),
    r##"'([^'])*'"## => Tok::SingleString(text.trim_matches('\'').into()),
    r##""([^\\"]|\\"|\\.)*""## => Tok::DoubleString(text[1..(text.len() - 1)].into(), true),
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
    r##"\\ "## => Tok::SingleString(" ".into()),
    r##"\\."## => Tok::DoubleString(text.into(), true),

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
}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct ContextLexer {
    context : Vec<(char, bool)>,
    line : usize,
    pos : usize,
    kw : KWAllow,
    heredoc : Option<(Tok, Span, String)>,
}

#[derive(Debug, Eq, PartialEq, Hash)]
pub struct ContextLexerIterator<'a, 'b> {
    lexer : &'a mut ContextLexer,
    input : &'b str,
    override_queue : VecDeque<(Tok, Span)>,
}

impl<'a> ContextLexer {
    pub fn new() -> ContextLexer { ContextLexer { context: vec![], line: 1, pos: 1, kw: KWAllow::All, heredoc: None } }

    pub fn lex<'b>(&'a mut self, input : &'b str) -> ContextLexerIterator<'a, 'b> {
        ContextLexerIterator::<'a, 'b>{lexer: self, input: input, override_queue: VecDeque::new()}
    }

    pub fn pop_expect(&mut self, expect: char) -> Option<LexError>
    {
        let ret = self.context.pop();
        if let Some(ret) = ret {
            if ret.0 == expect {
                None
            } else {
                Some(LexError::Mismatched(expect))
            }
        } else {
            Some(LexError::Mismatched(expect))
        }
    }

    pub fn does_expect(&self, c: char) -> bool {
        self.context.last().map(|x| x.0) == Some(c)
    }

    pub fn suppress_newlines(&self) -> bool {
        if self.heredoc.is_some() { return false; }
        self.context.last().map(|x| x.1).unwrap_or(false)
    }

    pub fn complete(&'a self) -> bool {
        if self.heredoc.is_some() { return false; }
        for c in self.context.iter() {
            if c.0 != '=' {
                return false;
            }
        }
        return true;
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
        if let Some(pos) = s.find('=') {
            let (mut left, right) = s.split_at(pos);
            let right = &right[1..];
            let op = Self::check_assign_op(&mut left);
            if left.len() > 0 {
                if is_identifier(left) {
                    self.override_queue.push_front((Tok::Ident(left.into()), span));
                } else {
                    return None;
                }
            }
            self.override_queue.push_front((op, span));

            if right.len() > 0 {
                self.override_queue.push_front((Tok::NakedString(right.into()), span));
            }
            return Some(self.override_queue.pop_back().unwrap().0);
        }
        return None;
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

enum ChainedFindResult {
    NotFound,
    OnlyFirst(usize),
    Spanning(usize),
    OnlyLast(usize),
}

fn chained_find(s1: &str, s2: &str, needle: &str) -> ChainedFindResult {
    use self::ChainedFindResult::*;

    if let Some(pos) = s1.find(needle) {
        return OnlyFirst(pos);
    }
    for (i, _) in needle.char_indices().skip(1) {
        if s1.ends_with(&needle[0..i]) {
            if s2.starts_with(&needle[i..]) {
                return Spanning(i)
            }
        }
    }
    if let Some(pos) = s2.find(needle) {
        return OnlyLast(pos);
    }
    NotFound
}

fn trim_all_leading_ws(s: String) -> String {
    s.lines().map(|line| line.trim_left()).collect::<Vec<&str>>().join("\n")
}

impl<'a, 'b> Iterator for ContextLexerIterator<'a, 'b> {

    type Item = (Tok, Span);

    fn next(&mut self) -> Option<Self::Item> {
        if let Some((Tok::Heredoc(as_val, do_subst, trim_ws, body), span, mut s)) = self.lexer.heredoc.take() {
            use self::ChainedFindResult::*;

            fn finalize(as_val: bool, do_subst: bool, trim_ws: bool, s: String) -> Tok {
                if as_val {
                    if do_subst {
                        Tok::DoubleString(s, false)
                    } else {
                        Tok::SingleString(s)
                    }
                } else {
                    Tok::Heredoc(as_val, do_subst, trim_ws, s)
                }
            }

            match chained_find(&s, self.input, &body) {
                NotFound => {
                    s.push_str(self.input);
                    self.input = &self.input[(self.input.len())..];
                    self.lexer.heredoc = Some((Tok::Heredoc(as_val, do_subst, trim_ws, body), span, s));
                    return None;
                },
                OnlyFirst(_) => {
                    unreachable!();
                },
                Spanning(i) => {
                    let l = s.len() - i;
                    s.truncate(l);
                    self.input = &self.input[(body.len() - i)..];
                    let s = if trim_ws { trim_all_leading_ws(s) } else {s};
                    return Some((finalize(as_val, do_subst, trim_ws, s), span));
                },
                OnlyLast(i) => {
                    s.push_str(&self.input[0..i]);
                    self.input = &self.input[(i + body.len())..];
                    let s = if trim_ws { trim_all_leading_ws(s) } else {s};
                    return Some((finalize(as_val, do_subst, trim_ws, s), span));
                },
            }
        }
        let (tok, span) = if let Some(o) = self.override_queue.pop_back() {
            o
        } else {
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
            (tok, span)
        };

        use self::KWAllow::*;

        let kw = self.lexer.kw;
        let mut next_kw = kw;

        match tok {
            Tok::LParen =>
                { self.lexer.context.push((')', true)); next_kw = No; },

            Tok::ExecLParen(_) =>
                { self.lexer.context.push((')', false)); next_kw = All; },

            Tok::LSquare =>
                { self.lexer.context.push((']', true)); next_kw = No; },

            Tok::ExecLSquare(_) =>
                { self.lexer.context.push((']', false)); next_kw = All; },

            Tok::LBrace =>
                { '{'; self.lexer.context.push(('}', false)); next_kw = All; },

            Tok::VarLBrace(_) =>
                { '{'; self.lexer.context.push(('}', true)); next_kw = No; },

            Tok::RParen => {
                next_kw = No;
                self.lexer.pop_expect(')');
            },

            Tok::RSquare => {
                next_kw = No;
                self.lexer.pop_expect(']');
            },

            Tok::RBrace => {
                next_kw = Else; '{';
                self.lexer.pop_expect('}');
            },

            Tok::NewLine(..) => {
                next_kw = Let;
                if self.lexer.does_expect('=') {
                    self.lexer.context.pop();
                }
            },

            Tok::Comment(..) => {
                next_kw = Let;
            },

            Tok::Assign => {
                if self.lexer.does_expect('=') {
                    self.lexer.context.pop();
                }
                next_kw = No;
            }

            Tok::Semi => {
                if self.lexer.does_expect('=') {
                    self.lexer.context.pop();
                }
                next_kw = Let;
            },

            Tok::AssignIfNull | Tok::Suffix |
                Tok::Prefix | Tok::And | Tok::Or | Tok::Pipe |
                Tok::Else | Tok::Into => { next_kw = All; },

            Tok::If | Tok::While => next_kw = Let,

            Tok::Let | Tok::Global | Tok::Sys => { next_kw = Assign },

            Tok::For | Tok::Func | Tok::Match | Tok::MatchAll | Tok::Comma |
                Tok::Break | Tok::Continue | Tok::Return |
                Tok::Gt | Tok::Lt |
                Tok::Var(_) | Tok::VarIdent(_) | Tok::Exec(_) | Tok::Redir(_, _) |
                Tok::Ident(_) | Tok::NakedString(_) | Tok::Range |
                Tok::SingleString(_) | Tok::DoubleString(..) |
                Tok::Rex(_) | Tok::Read | Tok::Recv | Tok::LambdaOpen |
                Tok::Member(..) | Tok::Colon | Tok::DoubleColon =>
                    { next_kw = No; },

            Tok::Error(_) => {},
            Tok::Whitespace | Tok::Amp | Tok::Heredoc(..) => {},
        }

        let tok = match kw {
            All => tok,
            No | Assign | Else | Let => match tok {
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

        let tok = loop { match tok {
            Tok::Let | Tok::Sys | Tok::Global => {
                self.lexer.context.push(('=', false));
            },
            Tok::For => {
                self.lexer.context.push((':', true));
            },
            Tok::NakedString(s) => {
                if kw == All || kw == Assign || self.lexer.does_expect('=') {
                    if let Some(t) = self.split_assign(&s, span) {
                        break t
                    }
                }
                if let Some(t) = self.split_range(&s, span) {
                    break t
                }
                break Tok::NakedString(s)
            },
            Tok::VarIdent(s) => {
                let pos = s.find(|c| !(c == '$' || c == '-' || c==','));
                let (left, right) = if let Some(pos) = pos {
                    s.split_at(pos)
                } else {
                    (&s[..], &""[..])
                };
                self.override_queue.push_front((Tok::Ident(right.into()), span));
                break Tok::Var(left.into())
            },
            Tok::Colon => {
                if self.lexer.does_expect(':') {
                    self.lexer.context.pop();
                } else {
                    break Tok::NakedString(":".into())
                }
            },
            Tok::DoubleColon => {
                if self.lexer.does_expect(':') {
                    self.lexer.context.pop();
                } else {
                    break Tok::NakedString("::".into())
                }
            },
            Tok::NewLine(..) => {
                if self.lexer.suppress_newlines() {
                    break Tok::Whitespace
                }
            },
            _ => {},
        }; break tok };

        self.lexer.kw = next_kw;

        if let Tok::Heredoc(..) = tok {
            self.lexer.heredoc = Some((tok, span, String::new()));
            self.next()
        } else if let Tok::Comment(..) = tok {
            self.next()
        } else {
            Some((tok, span))
        }
    }
}
