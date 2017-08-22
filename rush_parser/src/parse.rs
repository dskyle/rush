use ast::{ExprS, Span, Pos, Expr, TupleStyle, SubsMode, ImportScope, SetOp,
          ManOp, ASTRange};

use lex::Tok;
use rush_pat::pat::{Pat, RegexEq};
use regex::Regex;

use lex::Tok::*;
use std::cell::RefCell;

#[derive(Debug, Clone, PartialEq)]
pub enum ParseError {
    GenericError(Span, String),
    UnexpectedEOF(&'static str),
    UnexpectedToken(Span, Tok, &'static str),
    UnexpectedChar(Span, char),
    InvalidVarRef(ExprS),
    InvalidCapture(ExprS),
    InvalidCaptureTarget(ExprS),
    InvalidSubsMode(Span, String),
    InvalidRange(&'static str),
    InvalidPattern(ExprS, &'static str),
    InvalidRegex(Span, String, String),
}

use self::ParseError::*;

pub type Res<T> = Result<T, ParseError>;

pub fn parse<I: Iterator<Item=(Tok, Span)>>(i: I) -> Res<Vec<ExprS>> {
    parse_impl(i).unwrap_or_else(|x| match x {
        (Some((tok, span)), s) => match tok {
            Tok::Error(t) => Err(UnexpectedChar(span, t.chars().nth(0).unwrap_or('\0'))),
            _ => Err(UnexpectedToken(span, tok, s)),
        },
        (None, s) => Err(UnexpectedEOF(s)),
    })
}

parser! {
    pub fn parse_impl(Tok, Span);

    (a, b) {
        Span {
            l: a.l,
            r: b.r,
        }
    }

    stmt_list: Res<Vec<ExprS>> {
        stmt[s] => {
            let s = s?;
            if s.0 == Expr::Nop {
                Ok(vec!())
            } else {
                Ok(vec!(s))
            }
        }
        stmt_list[slist] ws stmt_sep stmt[s] => {
            let mut slist = slist?;
            let s = s?;
            if s.0 == Expr::Nop {
                /* Ignore Nops */
            } else {
                slist.push(s);
            }
            Ok(slist)
        }
    }

    stmt_sep: () {
        Semi ws => (),

        #[overriding]
        NewLine(_) ws => (),
    }

    stmt: Res<ExprS> {
        stmt2[s] ws => s,
        let_rule[i] => i,
        func[f] => f,
        control_flow[c] => c,
        => Ok(ExprS(Expr::Nop, Span::new(Pos::new(1,1), Pos::new(1,1)))),
    }

    stmt2: Res<ExprS> {
        set_rule[i] => i,
        stmt3[s] ws => s,
        stmt3[s] ws Amp => Ok(ExprS(Expr::Background(Box::new(s?)), span!())),
    }

    stmt3: Res<ExprS> {
        pipeline[p] => {
            let mut p = p?;
            if p.len() == 1 {
                Ok(p.pop().unwrap())
            } else {
                Ok(ExprS(Expr::Pipe(p, None), span!()))
            }
        },
        pipeline[p] Gt nl expr[f] => {
            let p = p?;
            Ok(ExprS(Expr::Pipe(p, Some(Box::new(f?))), span!()))
        },
    }

    pipeline: Res<Vec<ExprS>> {
        call[e] ws => Ok(vec![e?]),
        pipeline[p] Pipe nl call[e] ws => { let mut p = p?; p.push(e?); Ok(p) }
        pipeline[p] Pipe Amp nl call[e] ws => {
            let mut p = p?;
            let last = p.pop().unwrap();
            let last_span = last.1;
            p.push(ExprS(Expr::Manip(ManOp::Merge{into: 1, from: 2},
                                     Box::new(last)), last_span));
            p.push(e?); Ok(p)
        }
    }

    call: Res<ExprS> {
        expr[e] => e,
        call[c] ws manop[f] => Ok(ExprS(Expr::Manip(f?, Box::new(c?)), span!())),
    }

    manop: Res<ManOp> {
        Redir(from, to) => Ok(ManOp::Merge{from: from as u32, into: to as u32}),
    }

    expr: Res<ExprS> {
        subexpr[e] => e,
        and_or_ops[ao] => ao,
        block_expr[b] ws => b,
    }

    subexpr: Res<ExprS> {
        //expr3[e] => e,
        ws_tuple_val[tup] => tup,
        comma_tuple_val[tup] => tup,
    }

    /*expr3: Res<ExprS> {
        if_rule[i] => i,
        while_rule[w] => w,
        for_rule[f] => f,
        match_rule[m] => m,
    }*/

    ws_tuple_val: Res<ExprS> {
        #[no_reduce(Range, Ident, NakedString, DoubleString, SingleString, Rex, Var, LParen, VarLBrace, ExecLParen, ExecLSquare,
                    Read, Recv, If, While, For, Match, MatchAll, LBracePipe, LambdaOpen)]
        ws_tuple[tup] => {
            let mut tup = tup?;
            if tup.len() == 1 {
                Ok(tup.pop().unwrap())
            } else {
                Ok(ExprS(Expr::Tuple(TupleStyle::Spaced, tup), span!()))
            }
        },
    }

    comma_tuple_val: Res<ExprS> {
        comma_tuple[tup] =>
            Ok(ExprS(Expr::Tuple(TupleStyle::Comma, tup?), span!())),
    }

    parens: Res<ExprS> {
        LParen nl stmt2[e] nl RParen => e,
        LParen nl RParen =>
            Ok(ExprS(Expr::Tuple(TupleStyle::Comma, vec![]), span!())),
    }

    member: Res<ExprS> {
        #[no_reduce(LSquare)]
        indexing[i] ws => i,
        member[l] ws Member(m) ws var_ref_inline[r] ws => make_member(l?, m, r?, span!()),
        member[l] ws Member(m) ws parens[r] ws => make_member(l?, m, r?, span!()),
    }

    subexpr2: Res<ExprS> {
        if_rule[i] => i,
        while_rule[w] => w,
        for_rule[f] => f,
        read_rule[r] => r,
        recv_rule[r] => r,
        match_rule[m] => m,
        named_tuple[t] ws => t,
        lambda_val[b] ws => b,
        range[r] ws => r,

        #[no_reduce(Range)]
        val[v] ws => v,
    }

    val: Res<ExprS> {
        var_ref[vr] ws => vr,
        exec[ex] ws => ex,
        parens[p] ws => p,
    }

    ws: () {
        #[no_reduce(Whitespace)]
        => (),
        Whitespace => (),
    }

    nl: () {
        #[no_reduce(NewLine)]
        ws => (),
        ws NewLine(_) ws => (),
    }

    ident: Res<ExprS> {
        Ident(s) => Ok(ExprS::ident(s, span!())),
    }

    naked_string: Res<ExprS> {
        NakedString(s) => Ok(ExprS::string(s, span!())),
    }

    single_string: Res<ExprS> {
        SingleString(s) => Ok(ExprS::lstring(s, span!())),
    }

    double_string: Res<ExprS> {
        DoubleString(s) => {
            let v = process_xstring(s.clone(), span!());
            if v.len() == 1 {
                Ok(v.into_iter().nth(0).unwrap())
            } else {
                Ok(ExprS(Expr::XString(v), span!()))
            }
        },
    }

    regex: Res<ExprS> {
        Rex(s) => Ok(ExprS(Expr::Rex(RegexEq(Regex::new(&s).map_err(|e| InvalidRegex(span!(), s.clone(), format!("{}", e)))?)), span!())),
    }

    range: Res<ExprS> {
        #[no_reduce(Range)]
        atom[a] ws => a,

        #[no_reduce(Ident, NakedString, DoubleString, SingleString, Rex, Var, LParen, VarLBrace, ExecLParen, ExecLSquare, LBracePipe, LambdaOpen)]
        Range ws => Ok(ExprS(Expr::Range(ASTRange::All), span!())),

        #[no_reduce(Ident, NakedString, DoubleString, SingleString, Rex, Var, LParen, VarLBrace, ExecLParen, ExecLSquare, LBracePipe, LambdaOpen)]
        atom[a] ws Range ws => Ok(ExprS(Expr::Range(ASTRange::From(Box::new(a?))), span!())),

        #[no_reduce(Ident, NakedString, DoubleString, SingleString, Rex, Var, LParen, VarLBrace, ExecLParen, ExecLSquare, LBracePipe, LambdaOpen)]
        val[a] ws Range ws => Ok(ExprS(Expr::Range(ASTRange::From(Box::new(a?))), span!())),

        Range ws atom[a] ws => Ok(ExprS(Expr::Range(ASTRange::Till(Box::new(a?))), span!())),
        Range ws val[a] ws => Ok(ExprS(Expr::Range(ASTRange::Till(Box::new(a?))), span!())),
        atom[a] ws Range ws atom[b] ws => Ok(ExprS(Expr::Range(ASTRange::Within(Box::new(a?), Box::new(b?))), span!())),
        val[a] ws Range ws val[b] ws => Ok(ExprS(Expr::Range(ASTRange::Within(Box::new(a?), Box::new(b?))), span!())),
        atom[a] ws Range ws val[b] ws => Ok(ExprS(Expr::Range(ASTRange::Within(Box::new(a?), Box::new(b?))), span!())),
        val[a] ws Range ws atom[b] ws => Ok(ExprS(Expr::Range(ASTRange::Within(Box::new(a?), Box::new(b?))), span!())),
    }

    atom: Res<ExprS> {
        #[no_reduce(LParen)]
        ident[i] => i,
        naked_string[s] => s,
        single_string[s] => s,
        double_string[s] => s,
        regex[r] => r,
    }

    ws_tuple: Res<Vec<ExprS>> {
        #[no_reduce(Comma, LSquare, Member)]
        member[a] ws => Ok(vec![a?]),

        #[no_reduce(LSquare, Member)]
        ws_tuple[tup] member[a] ws => {
            let mut tup = tup?; tup.push(a?); Ok(tup)
        },
    }

    comma_tuple: Res<Vec<ExprS>> {
        #[no_reduce(Range, Ident, NakedString, DoubleString, SingleString, Rex, Var, LParen, VarLBrace, ExecLParen,
                    ExecLSquare, Read, Recv, If, While, For, Match, MatchAll, LBracePipe, LambdaOpen)]
        member[a] ws Comma ws => Ok(vec![a?]),

        #[no_reduce(Comma, LSquare, Member)]
        member[a] ws Comma ws member[b] ws => Ok(vec![a?, b?]),

        member[a] ws Comma ws comma_tuple[tup] => {
            let tup = tup?; let mut v = vec![a?]; v.extend(tup); Ok(v)
        },
    }

    named_tuple_init: Res<Vec<ExprS>> {
        ident[n] parens[e] => {
            let e = e?;
            if let ExprS(Expr::Ident(t), span) = n? {
                let mut v = vec![ExprS::string(t, span)];
                match e {
                    ExprS(Expr::Tuple(TupleStyle::Named, _), _) => v.push(e),
                    ExprS(Expr::Tuple(_, tupv), _) => {
                        v.extend(tupv);
                    },
                    _ => v.push(e),
                }
                Ok(v)
            } else {
                unreachable!()
            }
        }
    }

    named_tuple: Res<ExprS> {
        #[no_reduce(LBrace)]
        named_tuple_init[t] =>
            Ok(ExprS::tuple(TupleStyle::Named, t?, span!())),
    }

    var_ref_inline: Res<ExprS> {
        #[no_reduce(LParen)]
        ident[n] => n,
        named_tuple[t] => t,
        var_ref[r] => r,
    }

    var_ref_init: Res<(String, ExprS)> {
        #[no_reduce(LParen)]
        Var(s) var_ref_inline[n] => Ok((s, n?)),
        VarLBrace(s) ws stmt2[n] ws RBrace => Ok((s, n?)),
    }

                  /*
    var_ref_expr: Res<ExprS> {
        VarLBrace(m) ws atom[n] ws => ExprS(Expr::Var(parse_subs_mode(m.trim_right_matches('{'), span!())?, Box::new(n)),nspan),
        var_ref_expr[e] ws LSquare nl expr[i] nl RSquare ws => {
            Ok(ExprS(Expr::Index(SubsMode::new(), Box::new(e?), Box::new(i?)), span!()))
        ,
    }*/

    var_ref: Res<ExprS> {
        var_ref_init[t] => {
            let (s, n) = t?;
            let m = parse_subs_mode(s.trim_right_matches('{'), span!())?;
            fn fixup(m: SubsMode, n: ExprS, span: Span) -> Res<ExprS> {
                match n.0 {
                    Expr::Ident(_) | Expr::Var(..) => Ok(ExprS::var(m, n, span)),
                    //Expr::String(_) | Expr::XString(_) =>
                    Expr::Member(_, val, call) => {
                        let new_val: ExprS = fixup(SubsMode::new(), *val, span)?;
                        Ok(ExprS(Expr::Member(m, Box::new(new_val), call), span))
                    },
                    Expr::Index(_, val, idx) => {
                        let new_val: ExprS = fixup(SubsMode::new(), *val, span)?;
                        Ok(ExprS(Expr::Index(m, Box::new(new_val), idx), span))
                    },
                    _ => Ok(ExprS::call(m, n, span)),
                    //Expr::Tuple(..) =>
                        //Ok(ExprS::call(parse_subs_mode(s.trim_right_matches('{'), span!())?, n, span!())),
                    //_ => Err(InvalidVarRef(n)),
                }
            }
            fixup(m, n, span!())

        },

        //Var(s) indexing[idx] => Ok(make_index_call(idx?, span!(), s.as_str())?),

        /*
        var_ref_expr[e] ws RBrace ws => {
            let mut e = e?;
            e.0.set_subs_mode(m);
            Ok(e)
            //Ok(make_index_call(idx?, span!(), s.trim_right_matches('{'))?),
        }*/
    }

             /*
    exec_subexpr: Res<ExprS> {
        #[no_reduce(LParen)]
        ident[n] => n,
        named_tuple[t] => t,
        var_ref[v] => v,
    }*/

    exec: Res<ExprS> {
        /*
        Exec(s) exec_subexpr[n] =>
            Ok(ExprS::exec(parse_exec_subs_mode(s.trim_right_matches('!'), span!())?,
                        n?, span!())),*/

        ExecLParen(s) nl stmt2[n] nl RParen =>
            Ok(ExprS::exec(parse_exec_subs_mode(s.trim_right_matches('('), span!())?,
                        n?, span!())),

        ExecLSquare(s) nl stmt2[n] nl RSquare =>
            Ok(ExprS::exec_to_list(parse_exec_subs_mode(s.trim_right_matches('['), span!())?,
                        n?, span!())),
    }

    block: Res<Vec<ExprS>> {
        LBrace nl stmt_list[e] nl RBrace => Ok(e?),
    }

    block_expr: Res<ExprS> {
        block[b] => Ok(ExprS(Expr::Block(b?), span!()))
    }

    capture: Res<Vec<(String, Option<ExprS>)>> {
        LSquare nl comma_tuple[c] nl RSquare => {
            let c = c?;
            let mut ret = Vec::with_capacity(c.len());
            for x in c.into_iter() {
                match x {
                    ExprS(Expr::Ident(i), _) => { ret.push((i, None)); continue },
                    ExprS(Expr::Block(v), s) => {
                        if v.len() == 1 {
                            let x = v.into_iter().next().unwrap();
                            if let ExprS(Expr::Set(SetOp::Assign, b, e), _) = x {
                                if let ExprS(Expr::Ident(i), _) = *b {
                                    ret.push((i, Some(*e)));
                                    continue
                                }
                                return Err(InvalidCaptureTarget(*b))
                            }
                            return Err(InvalidCapture(x))
                        }
                        return Err(InvalidCapture(ExprS(Expr::Block(v), s)))
                    },
                    ExprS(Expr::Set(SetOp::Assign, b, e), _) => {
                        if let ExprS(Expr::Ident(i), _) = *b {
                            ret.push((i, Some(*e)));
                            continue
                        }
                        return Err(InvalidCaptureTarget(*b))
                    },
                    _ => return Err(InvalidCaptureTarget(x)),
                }
            }
            Ok(ret)
        }
    }

    lambda_body: Res<Vec<ExprS>> {
        LBrace nl stmt_list[e] nl RBrace => e,
        subexpr[e] => Ok(vec![e?]),
    }

    lambda: Res<(Vec<(String, Option<ExprS>)>, Pat, RefCell<Option<Vec<ExprS>>>)> {
        LambdaOpen nl Pipe ws lambda_body[e] =>
            Ok((vec![], ExprS::lambda_to_pat(vec![], ExprS(Expr::Tuple(TupleStyle::Comma, vec![]), span!()))?, RefCell::new(Some(e?)))),
        LambdaOpen nl expr[a] nl Pipe ws lambda_body[e] =>
            Ok((vec![], ExprS::lambda_to_pat(vec![], a?)?, RefCell::new(Some(e?)))),
        LambdaOpen nl Pipe nl capture[c] ws lambda_body[e] => {
            let c = c?; let binds = c.iter().map(|x| x.0.clone()).collect();
            Ok((c, ExprS::lambda_to_pat(binds, ExprS(Expr::Tuple(TupleStyle::Comma, vec![]), span!()))?, RefCell::new(Some(e?))))
        },
        LambdaOpen nl expr[a] nl Pipe nl capture[c] ws lambda_body[e] => {
            let c = c?; let binds = c.iter().map(|x| x.0.clone()).collect();
            Ok((c, ExprS::lambda_to_pat(binds, a?)?, RefCell::new(Some(e?))))
        },
    }

    lambda_val: Res<ExprS> {
        lambda[l] => {
            let l = l?;
            Ok(ExprS(Expr::Lambda(l.0, l.1, l.2), span!()))
        },
    }

    if_cond: Res<ExprS> {
        subexpr[cond] => cond,
        let_expr[l] => l,
    }

    if_rule: Res<ExprS> {
        If ws if_cond[cond] nl block[then] ws =>
            Ok(make_if_val(cond?, then?, None, span!())),

        If ws if_cond[cond] nl block[then] ws Else ws block[el] ws =>
            Ok(make_if_val(cond?, then?, Some(el?), span!())),

        If ws if_cond[cond] nl block[then] ws Else ws if_rule[el] =>
            Ok(make_if_val(cond?, then?, Some(vec![el?]), span!())),
    }

    while_rule: Res<ExprS> {
        While ws if_cond[cond] nl block[lo] ws => {
            Ok(ExprS(Expr::While{cond: Box::new(cond?), lo: lo?}, span!()))
        },
    }

    for_rule: Res<ExprS> {
        For ws expr[bind] nl Colon nl subexpr[iter] nl block[lo] ws => {
            let pat = ExprS::to_pat(bind?)?;
            let iter = iter?;
            let iter_span = iter.1;
            if let ExprS(Expr::Range(..), ..) = iter {
                Ok(ExprS(Expr::ForIter{pat: pat, iter:
                    Box::new(ExprS(Expr::Call(SubsMode::new(), Box::new(ExprS(Expr::Tuple(TupleStyle::Named, vec![
                        ExprS(Expr::Ident("iter".into()), iter.1),
                        iter]), iter_span)), vec![]), iter_span)), lo: lo?}, span!()))
            } else {
                Ok(ExprS(Expr::For{pat: pat, val: Box::new(iter), lo: lo?}, span!()))
            }
        },

        For ws expr[bind] nl DoubleColon nl subexpr[iter] nl block[lo] ws => {
            let pat = ExprS::to_pat(bind?)?;
            Ok(ExprS(Expr::ForIter{pat: pat, iter: Box::new(iter?), lo: lo?}, span!()))
        },
    }

    indexing: Res<ExprS> {
        subexpr2[n] ws => n,
        indexing[n] ws LSquare nl expr[i] nl RSquare ws => {
            let mut n = n?;
            let m = n.0.take_subs_mode().unwrap_or(SubsMode::new());
            Ok(ExprS(Expr::Index(m, Box::new(n), Box::new(i?)), span!()))
        },
    }

    let_lhs: Res<ExprS> {
        expr[e] => e,
    }

    let_rule: Res<ExprS> {
        Let nl let_lhs[i] nl Assign nl expr[e] ws => {
            Ok(ExprS(Expr::Let(ExprS::to_pat(i?)?, Box::new(e?)), span!()))
        },
    }

    set_lhs: Res<ExprS> {
        //atom[e] ws => e,
        member[i] ws => i,
    }

    id_list: Res<Vec<ExprS>> {
        ident[i] ws => Ok(vec![i?]),
        id_list[l] ws ident[i] ws => Ok({let mut l = l?; l.push(i?); l}),
    }

    read_rule: Res<ExprS> {
        #[no_reduce(Ident)]
        Read ws id_list[i] ws => {
            Ok(ExprS(Expr::Read(i?), span!()))
        },

        Read ws LParen ws id_list[i] ws RParen ws => {
            Ok(ExprS(Expr::Read(i?), span!()))
        },
    }

    recv_rule: Res<ExprS> {
        Recv ws subexpr[p] ws => {
            Ok(ExprS(Expr::Recv(ExprS::to_pat(p?)?), span!()))
        },
    }

    scope: ImportScope {
        Global => ImportScope::Global,
        Sys => ImportScope::Sys,
    }

    set_op: SetOp {
        Assign => SetOp::Assign,
        AssignIfNull => SetOp::AssignIfNull,
        Suffix => SetOp::Suffix,
        Prefix => SetOp::Prefix,
    }

    set_rule: Res<ExprS> {
        set_lhs[i] set_op[o] nl expr[e] ws =>
            Ok(ExprS(Expr::Set(o, Box::new(i?), Box::new(e?)), span!())),

        scope[s] nl ident[i] ws =>
            Ok(ExprS::import(s, i?, span!())),

        scope[s] nl ident[i] ws set_op[o] nl expr[e] ws =>
            Ok(ExprS::import_set(s, i?, o, e?, span!())),

        scope[s] nl ident[i] ws Colon nl ident[a] ws =>
            Ok(ExprS::import_as(s, i?, a?, span!())),

        scope[s] nl ident[i] ws Colon nl ident[a] ws set_op[o] nl expr[e] ws=>
            Ok(ExprS::import_as_and_set(s, i?, a?, o, e?, span!())),
    }

    let_expr: Res<ExprS> {
        Let nl let_lhs[i] nl Assign nl subexpr[e] ws =>
            Ok(ExprS(Expr::Let(ExprS::to_pat(i?)?, Box::new(e?)), span!())),
    }

    and_or_ops: Res<ExprS> {
        subexpr[l] And nl subexpr[r] ws =>
            Ok(make_and_or_val(Expr::And, l?, r?, span!())),

        subexpr[l] Or nl subexpr[r] ws =>
            Ok(make_and_or_val(Expr::Or, l?, r?, span!())),

        and_or_ops[l] And nl subexpr[r] ws =>
            Ok(make_and_or_val(Expr::And, l?, r?, span!())),

        and_or_ops[l] Or nl subexpr[r] ws =>
            Ok(make_and_or_val(Expr::Or, l?, r?, span!())),
    }

    func: Res<ExprS> {
        Func nl subexpr[i] nl block[b] ws => {
            let p = ExprS::to_pat(i?)?;
            Ok(ExprS(Expr::FuncDec(p, RefCell::new(Some(b?))), span!()))
        },
    }

    match_one: Res<(Pat, ExprS)> {
        expr[e] ws Into ws stmt3[b] ws => {
            Ok((ExprS::to_pat(e?)?, b?))
        }
        //expr[e] ws Into ws block[b] ws => {
            //Ok((ExprS::to_pat(e?)?, b?))
        //}
    }

    match_list: Res<Vec<(Pat, ExprS)>> {
        match_one[l] => Ok(vec![l?]),
        match_list[m] nl Comma nl match_one[l] => { let mut m = m?; m.push(l?); Ok(m) }
    }

    match_block: Res<Vec<(Pat, ExprS)>> {
        LBrace nl match_list[l] nl RBrace ws => l,
        LBrace nl match_list[l] nl Comma nl RBrace ws => l,
    }

    match_rule: Res<ExprS> {
        Match nl subexpr[i] nl match_block[n] ws =>
            Ok(ExprS(Expr::Match{val: Box::new(i?), cases: n?}, span!())),

        MatchAll nl subexpr[i] nl match_block[n] ws =>
            Ok(ExprS(Expr::MatchAll{val: Box::new(i?), cases: n?}, span!())),
    }

    control_flow: Res<ExprS> {
        return_rule[r] => r,
        break_rule[b] => b,
        continue_rule[c] => c,
    }

    return_rule: Res<ExprS> {
        Return ws expr[e] ws => Ok(ExprS(Expr::Return(Some(Box::new(e?))), span!())),
        Return ws => Ok(ExprS(Expr::Return(None), span!())),
    }

    break_rule: Res<ExprS> {
        Break ws expr[e] ws => Ok(ExprS(Expr::Break(Some(Box::new(e?))), span!())),
        Break ws => Ok(ExprS(Expr::Break(None), span!())),
    }

    continue_rule: Res<ExprS> {
        Continue ws expr[e] ws => Ok(ExprS(Expr::Continue(Some(Box::new(e?))), span!())),
        Continue ws => Ok(ExprS(Expr::Continue(None), span!())),
    }
}

fn make_if_val(cond: ExprS,
               then: Vec<ExprS>,
               el: Option<Vec<ExprS>>,
               span: Span) -> ExprS {
    ExprS(Expr::If{cond: Box::new(cond),
                   then: then,
                   el: el}, span)
}

fn make_and_or_val<B: FnOnce(Box<ExprS>, Box<ExprS>) -> Expr>(
        build: B,
        l: ExprS,
        r: ExprS,
        span: Span) -> ExprS {
    ExprS(build(Box::new(l), Box::new(r)), span)
}

fn parse_exec_subs_mode(s: &str, span: Span) -> Res<SubsMode> {
    parse_subs_mode(s, span)
}

fn parse_subs_mode(s: &str, span: Span) -> Res<SubsMode> {
    let s = s.trim_left_matches('$');
    let mut ret = SubsMode::new();
    for c in s.chars() {
        match c {
            ',' => ret.embed = true,
            '-' => ret.flatten = true,
            _ => return Err(InvalidSubsMode(span, s.into())),
        }
    }
    return Ok(ret)
}

/*
fn make_index_call(idx: ExprS, span: Span, s: &str) -> Res<ExprS> {
    if let ExprS(Expr::Index((n, ns), i), _) = idx {
        Ok(ExprS::call(parse_subs_mode(s, span)?, ExprS::tuple(TupleStyle::Named, vec![
                ExprS::ident("op::index".into(), span),
                ExprS::var(SubsMode::new(), ExprS(Expr::Ident(n), ns), span), *i
            ], span), span))
    } else { unreachable!() }
}

fn make_member_call(t: ExprS) {
    if let ExprS(Expr::Tuple(t), span) = t {
        if t.len() >= 1 {
            let n = t[0];
            if let ExprS(Expr::Ident(n), span) = n {
                let parts : Vec<&str> = n.split('.').collect();
                let mut v : Vec<ExprS> =
                    if parts.len() == 1 {
                        vec![ExprS::string(n.clone(), span)]
                    } else {
                        vec![
                          ExprS::string(parts[1].to_string(), span),
                          ExprS::var(SubsMode::Insert,
                                     ExprS::ident(parts[0].to_string(),
                                                  span), span),
                        ]
                    };
                match e {
                    ExprS(Expr::Tuple(TupleStyle::Named, _), _) => v.push(e),
                    ExprS(Expr::Tuple(_, tupv), _) => {
                        v.extend(tupv);
                    },
                    _ => v.push(e),
                }
                return v
            }
        }
    }
    n
}*/

fn xstring_ensure_last_is_str(v: &mut Vec<ExprS>) {
    let need_append = {
        match *v.last().unwrap() {
            ExprS(Expr::LString(_), _) => false,
            _ => true,
        }
    };
    if need_append {
        let span = { v.last().unwrap().1 } + 1;
        v.push(ExprS(Expr::LString("".into()), Span::new(span.r, span.r)))
    }
}

fn xstring_add_char(v: &mut Vec<ExprS>, c: char, width: usize) {
    xstring_ensure_last_is_str(v);
    {
        let mut cur_str = v.last_mut().unwrap().0.get_str_mut().unwrap();
        cur_str.push(c);
    }
    {
        let mut cur_span = &mut v.last_mut().unwrap().1;
        *cur_span += width;
    }
}

fn xstring_add_expr(v: &mut Vec<ExprS>, e: Expr, width: usize) {
    let span = { v.last().unwrap().1 } + 1;
    v.push(ExprS(e, Span::new(span.r, span.r + (0, width))));
}

fn count_to_matching(s: &str, open: char, close: char) -> (usize, usize) {
    let mut count = 0;
    let mut depth = 0;
    let mut iter = s.chars();
    loop {
        let c = { if let Some(c) = iter.next() { c } else { break }};
        if c == open {
            depth += 1;
        } else if c == close {
            depth -= 1;
        }
        count += 1;
        if depth == 0 { break; }
    }
    (count, depth)
}

fn parse_subst(s: &str) -> Expr {
    let mut lex = ::lex::ContextLexer::new();
    let parsed = parse(lex.lex(s));
    match parsed {
        Ok(list) => {
            if list.len() == 1 {
                list.into_iter().nth(0).unwrap().0
            } else {
                panic!("Expected single statement in substitution");
            }
        },
        Err(err) => {
            panic!("{:?}", err);
        }
    }
}

fn process_xstring_subst<'a>(v: &mut Vec<ExprS>, s: &'a str) -> &'a str {
    lazy_static! {
        static ref RE: Regex = Regex::new(
r##"^[_a-zA-Z][_a-zA-Z0-9]*(::[_a-zA-Z][_a-zA-Z0-9]*)*"##).unwrap();
    }

    if let Some(next) = s.chars().nth(1) {
        if next == '{' {
            let (count, depth) = count_to_matching(&s[1..], '{', '}');
            if depth != 0 || count < 2 {
                panic!("Invalid variable substitution: missing closing }");
            }
            let slice = &s[0..(count + 1)];
            if slice.len() > 3 {
                xstring_add_expr(v, parse_subst(slice), slice.len() + 1);
            }
            return &s[(slice.len() - 1)..];
        } else if next == '(' {
            let (count, depth) = count_to_matching(&s[1..], '(', ')');
            if depth != 0 || count < 2 {
                panic!("Invalid variable substitution: missing closing )");
            }
            let slice = &s[0..(count + 1)];
            if slice.len() > 3 {
                xstring_add_expr(v, parse_subst(slice), slice.len() + 1);
            }
            return &s[(slice.len() - 1)..];
        } else {
            let mut len = RE.find(&s[1..]).map(|m| m.end()).unwrap_or(0);
            if len == 0 {
                panic!("Invalid variable substitution: invalid character after $");
            }
            let next = s.chars().nth(len + 1);
            if let Some('(') = next {
                let (count, depth) = count_to_matching(&s[(len + 1)..], '(', ')');
                if depth == 0 && count >= 2 {
                    len += count;
                }
            }
            let slice = &s[0..(len + 1)];
            xstring_add_expr(v, parse_subst(slice), slice.len() + 1);
            return &s[(slice.len() - 1)..];
        }
    } else {
        return s;
    }
}

fn process_xstring(s: String, span: Span) -> Vec<ExprS> {
    let mut ret = vec![ExprS(Expr::LString("".into()), Span::new(span.l, span.l))];
    let mut iter = s.chars();
    loop {
        let c = { if let Some(c) = iter.clone().nth(0) { c } else { break }};
        match c {
            '\\' => {
                let c = { if let Some(c) = iter.clone().nth(1) { c } else { break }};
                match c {
                    'n' => xstring_add_char(&mut ret, '\n', 2),
                    't' => xstring_add_char(&mut ret, '\t', 2),
                    'r' => xstring_add_char(&mut ret, '\r', 2),
                    '0' => xstring_add_char(&mut ret, '\0', 2),
                    c => xstring_add_char(&mut ret, c, 2),
                }
                iter.next();
            },
            '$' => {
                iter = process_xstring_subst(&mut ret, iter.as_str()).chars();
            },
            c => {
                xstring_add_char(&mut ret, c, 1);
            }
        }
        iter.next();
    }
    xstring_ensure_last_is_str(&mut ret);
    return ret;
}

fn make_member(l: ExprS, m: String, r: ExprS, span: Span) -> Res<ExprS> {
    Ok(ExprS(Expr::Member(parse_subs_mode(&m[2..], l.1)?, Box::new(l), Box::new(r)), span))
}
