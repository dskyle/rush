//#![feature(plugin)]
//#![plugin(plex)]
#![feature(inclusive_range_syntax)]
#![feature(box_patterns)]
#![feature(splice)]
#![feature(const_fn)]
#![feature(integer_atomics)]

//extern crate regex;

#[macro_use]
extern crate lazy_static;

extern crate rush_parser;

#[macro_use]
extern crate rush_pat;

extern crate rush_rt;

extern crate users;

extern crate nix;

extern crate tempfile;

extern crate glob;

extern crate signal;

extern crate libc;
extern crate errno;
extern crate bounded_spsc_queue;


pub mod func;
pub mod interp;
pub mod sitter;
pub mod jobs;
pub mod pipeline;
pub mod util;
pub mod builtins;

use rush_pat::pat::Pat;
use func::{Func};
pub use rush_rt::val::Val;
pub use func::Control;
use rush_rt::val::InternalIterable;
use std::borrow::{Cow};
pub use rush_parser::lex::{ContextLexer, Tok};
pub use rush_parser::ast::{Span};

pub fn test(input: &str) -> () {
    {
        let mut lex = rush_parser::lex::ContextLexer::new();
        for cur in lex.lex(input) {
            println!("{:?}", cur)
        }
    }
    {
        let mut lex = rush_parser::lex::ContextLexer::new();
        let parsed = rush_parser::parse::parse(lex.lex(input));
        println!("{:#?}", parsed);
    }
}

fn mk_wild_pat(name: &str) -> Pat {
use self::Pat::*;

Tup(vec![Str(name.into()), Wild(vec![ID("args".into())])])
}

fn mk_noarg_pat(name: &str) -> Pat{
use self::Pat::*;
Tup(vec![Str(name.into())])
}

fn mk_binary_pat(name: &str) -> Pat{
use self::Pat::*;
Tup(vec![Str(name.into()), ID("l".into()), ID("r".into())])
}

use rush_rt::vars::{LocalVars, Scoped};

pub struct Processor {
    pub interp: interp::Interp,
    pub locals: LocalVars,
}

pub type PartialLex = (Vec<(Tok, Span)>, ContextLexer);

impl Processor {
    pub fn new() -> Processor {
        let mut interp = interp::Interp::new();

        {
            let fns = &mut interp.funcs;
            fns.reg(Func::built_in(mk_wild_pat("system"), builtins::system));
            fns.reg(Func::mac("eval", builtins::eval));
            fns.reg(Func::mac("mkval", builtins::mkval));
            fns.reg(Func::mac("source", builtins::source));
            fns.reg(Func::built_in(mk_wild_pat("echo"), builtins::echo));
            fns.reg(Func::built_in(mk_wild_pat("repr"), builtins::repr));
            fns.reg(Func::built_in(mk_wild_pat("erepr"), builtins::erepr));
            fns.reg(Func::built_in(mk_wild_pat("len"), builtins::len));
            fns.reg(Func::built_in(mk_wild_pat("count"), builtins::count));
            fns.reg(Func::built_in(mk_wild_pat("debug"), builtins::debug));
            fns.reg(Func::built_in(mk_wild_pat("add"), builtins::add));
            fns.reg(Func::built_in(mk_wild_pat("keys"), builtins::keys));
            fns.reg(Func::built_in(mk_wild_pat("values"), builtins::values));
            fns.reg(Func::built_in(mk_pat!( ("expand", {range = ("Range", ...)}) ), builtins::expand_range));
            fns.reg(Func::built_in(mk_wild_pat("val"), builtins::val));
            fns.reg(Func::built_in(mk_pat!( ("op::index", {tup}, {i}) ), builtins::index));
            fns.reg(Func::built_in(mk_pat!( ("op::get_prop", {tup}, {i}) ), builtins::index));
            fns.reg(Func::built_in(mk_binary_pat("equals"), builtins::equals));
            fns.reg(Func::built_in(mk_wild_pat("cd"), builtins::cd));
            fns.reg(Func::built_in(mk_noarg_pat("jobs"), builtins::jobs));
            fns.reg(Func::built_in(mk_wild_pat("fg"), builtins::fg));
            fns.reg(Func::built_in(mk_wild_pat("exit"), builtins::exit));

            fns.reg(Func::built_in(mk_pat!( ("iter", ("Range", {l}, {r})) ), builtins::range_iter_start));
            fns.reg(Func::built_in(mk_pat!( ("next", ("Range::Iter", {cur}, {l}, {r})) ), builtins::range_iter_next));

            fns.reg(Func::built_in(mk_pat!( ("readline") ), builtins::readline_iter_start));
            fns.reg(Func::built_in(mk_pat!( ("next", ("readline::Iter", {cur})) ), builtins::readline_iter_next));

            fns.reg(Func::built_in(mk_pat!( ("map", {iter}, {op}) ), builtins::map_iter_start));
            fns.reg(Func::built_in(mk_pat!( ("next", ("map::Iter", {cur}, {iter}, {op})) ), builtins::map_iter_next));

            fns.reg(Func::built_in(mk_pat!( ("header", {iter}, [{header}]) ), builtins::header_iter_start));
            fns.reg(Func::built_in(mk_pat!( ("next", ("header::Iter", {cur}, {iter}, {header})) ), builtins::header_iter_next));

            fns.reg(Func::mac("iter", builtins::list_iter_start));
            fns.reg(Func::mac("next", builtins::list_iter_next));

            fns.reg(Func::built_in(mk_pat!( ("op::bool", ("Status", {s})) ), builtins::op_bool_status));
        }

        let mut locals = LocalVars::new();
        locals.enter_scope();

        Processor { interp, locals }
    }

    pub fn exec_toks<I: IntoIterator<Item = (Tok, Span)>>(&mut self, toks: I) -> (Val, Control) {
        let parsed = rush_parser::parse::parse(toks.into_iter());

        let ret = self.interp.exec_stmt_list(&mut parsed.unwrap(), &mut self.locals);
        ret.0.unhandled();
        ret
    }

    pub fn exec(&mut self, input: &str) -> (Val, Control) {
        let mut lexer = ContextLexer::new();
        self.exec_toks(lexer.lex(input))
    }

    pub fn exec_partial(&mut self, input: &str, pending: Option<PartialLex>) -> Result<(Val, Control), PartialLex>
    {
        let (mut toks, mut lexer) = if let Some((t, l)) = pending {
            (t, l)
        } else {
            (Vec::new(), ContextLexer::new())
        };
        toks.extend(lexer.lex(input));
        if lexer.complete() {
            Ok(self.exec_toks(toks))
        } else {
            Err((toks, lexer))
        }
    }

    pub fn add_local(&mut self, varname: &str, val: Val) {
        use rush_rt::vars::Binder;

        self.locals.bind(varname, val);
    }
}

pub fn exec(input: &str) -> () {
    test(input);
    let mut prc = Processor::new();
    let (val, _) = prc.exec(input);
    val.unhandled();
    println!("Prog returns: {:?}", val);
    Cow::from(val).for_each(&mut |v: Cow<str>, s| { println!("{}: {:?}", s, v); true } );
}
