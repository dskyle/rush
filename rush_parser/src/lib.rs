#![feature(plugin)]
#![plugin(plex)]
#![feature(inclusive_range_syntax)]
#![feature(box_patterns)]

extern crate regex;
extern crate odds;

#[macro_use]
extern crate lazy_static;

extern crate rush_pat;

pub mod ast;
pub mod lex;
pub mod val_lex;
pub mod parse;
