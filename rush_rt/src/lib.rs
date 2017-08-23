#![feature(inclusive_range_syntax)]
#![feature(splice)]
#![feature(box_patterns)]
#![feature(try_from)]
#![feature(conservative_impl_trait)]
#![feature(slice_get_slice)]

extern crate rush_parser;
extern crate rush_pat;
extern crate regex;
extern crate num_traits;

#[macro_use]
extern crate into_val_derive;

pub mod error;
pub mod pat;
pub mod range;
pub mod val;
pub mod vars;
