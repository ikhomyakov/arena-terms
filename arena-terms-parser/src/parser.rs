use crate::lexer::{TermLexer, TermToken, Value};
use crate::oper::{Assoc, Fixity, MAX_OPER_PREC, MIN_OPER_PREC, OperDef, OperDefTab, OperDefs};
use anyhow::{Context, Result, anyhow, bail};
use arena_terms::{Arena, IntoTerm, Term, View, atom, func, list};
use once_cell::sync::Lazy;
use parlex::{Lexer, LexerCtx, LexerData, Token};
use smartstring::alias::String;
use std::iter::FusedIterator;
use std::str::FromStr;
use std::{fmt, mem};

include!(concat!(env!("OUT_DIR"), "/parser_data.rs"));

// pub const PARSER_OPER_DEFS_STR: &str = "[op(-(x), prefix, 800, right, none, false), op(++(x, y), infix, 500, left, none, false), op(=(x, y), infix, 100, right, none, false), op(op(f, =(type, fun), =(prec, 0), =(assoc, none), =(rename_to, none), =(embed_type, false)), fun, 0, none, none, false)]";
pub fn parser_oper_defs(arena: &mut Arena) -> OperDefs {
    let term = list![
        func!(
            "op";
            func!("-"; atom!("x")),
            atom!("prefix"),
            800,
            atom!("right"),
            atom!("none"),
            atom!("false"),
        ),
        func!(
            "op";
            func!("++"; atom!("x"), atom!("y")),
            atom!("infix"),
            500,
            atom!("left"),
            atom!("none"),
            atom!("false"),
        ),
        func!(
            "op";
            func!("="; atom!("x"), atom!("y")),
            atom!("infix"),
            100,
            atom!("right"),
            atom!("none"),
            atom!("false"),
        ),
        func!(
            "op";
            func!(
                "op";
                atom!("f"),
                func!("="; atom!("type"), atom!("fun")),
                func!("="; atom!("prec"), 0),
                func!("="; atom!("assoc"), atom!("none")),
                func!("="; atom!("rename_to"), atom!("none")),
                func!("="; atom!("embed_type"), atom!("false")),
            ),
            atom!("fun"),
            0,
            atom!("none"),
            atom!("none"),
            atom!("false"),
        ),
        => arena
    ];
    OperDefs::try_from_ops(arena, term).unwrap()
}

pub struct TermParser<I>
where
    I: FusedIterator<Item = u8>,
{
    ctx: ParserCtx<TermLexer<I>, <Self as Parser<Arena>>::ParserData, Arena>,
    terms: Vec<Term>,
}

impl<I> TermParser<I>
where
    I: FusedIterator<Item = u8>,
{
    pub fn try_new(input: I, opers: Option<OperDefs>) -> Result<Self> {
        let lexer = TermLexer::try_new(input, opers)?;
        let ctx = ParserCtx::new(lexer);
        Ok(Self {
            ctx,
            terms: Vec::new(),
        })
    }

    pub fn try_collect_terms(&mut self, arena: &mut Arena) -> Result<Vec<Term>> {
        let mut ts = Vec::new();
        while let Some(t) = self.try_next_term(arena)? {
            ts.push(t);
        }
        Ok(ts)
    }

    #[inline]
    pub fn try_next_term(&mut self, arena: &mut Arena) -> Result<Option<Term>> {
        while let Some(tok) = self.try_next(arena)? {
            match tok.token_id {
                TokenID::Term => match tok.value {
                    Value::None => {}
                    Value::Term(term) => return Ok(Some(term)),
                    value => bail!("Unexpected token value {:?}", value),
                },
                token_id => bail!("Unexpected token id {:?}", token_id),
            }
        }
        Ok(None)
    }

    pub fn define_opers<J: FusedIterator<Item = u8>>(
        &mut self,
        arena: &mut Arena,
        defs_input: J,
        opers: Option<OperDefs>,
    ) -> Result<()> {
        let opers = match opers {
            Some(opers) => opers,
            None => parser_oper_defs(arena),
        };

        let defs_lexer = TermLexer::try_new(defs_input, Some(opers))?;
        let defs_ctx = ParserCtx::new(defs_lexer);
        let mut defs_parser = TermParser {
            ctx: defs_ctx,
            terms: Vec::new(),
        };
        while let Some(term) = defs_parser.try_next_term(arena)? {
            log::trace!(
                "Stats: {:?}, {:?}",
                defs_parser.ctx().lexer.stats(),
                defs_parser.stats()
            );
            defs_parser
                .ctx_mut()
                .lexer
                .opers
                .define_opers(arena, term)?;
        }
        let defs_opers = std::mem::take(&mut defs_parser.ctx_mut().lexer.opers);
        self.ctx_mut().lexer.opers = defs_opers;

        Ok(())
    }

    fn normalize_term(
        &self,
        arena: &mut Arena,
        term: Term,
        fixity: Fixity,
        op_tab_index: Option<usize>,
    ) -> Result<Term> {
        match self.ctx().lexer.opers.get(op_tab_index)[fixity] {
            Some(ref op_def) => {
                let (functor, vs) = match term.view(arena)? {
                    View::Atom(_) => (term, &[] as &[Term]),
                    View::Func(_, functor, args) => {
                        if args.is_empty() {
                            bail!("invalid Func");
                        }
                        (*functor, args)
                    }
                    _ => {
                        return Ok(term);
                    }
                };
                let name = functor.atom_name(arena)?;

                let n_required_args = OperDef::required_arity(fixity);
                if vs.len() < n_required_args {
                    bail!(
                        "missing {} required arguments in term {:?}",
                        n_required_args - vs.len(),
                        name
                    );
                }

                let args = &op_def.args;
                let mut xs: Vec<Option<Term>> = vec![None; args.len()];

                for (i, value) in vs.iter().enumerate() {
                    if i < n_required_args {
                        xs[i] = Some(*value);
                    } else {
                        match value.view(arena)? {
                            View::Func(ar, functor, vs)
                                if vs.len() == 2 && functor.atom_name(ar)? == "=" =>
                            {
                                let arg_name = vs[0].atom_name(arena)?;

                                if let Some(pos) = args.iter().position(|x| x.name == arg_name) {
                                    if xs[pos].is_none() {
                                        xs[pos] = Some(vs[1]);
                                    } else {
                                        bail!(
                                            "cannot redefine argument {:?} at position {} in {:?}",
                                            arg_name,
                                            pos,
                                            name
                                        );
                                    }
                                } else {
                                    bail!("invalid argument name {:?} in {:?}", arg_name, name);
                                }
                            }
                            _ => {
                                if xs[i].is_none() {
                                    xs[i] = Some(*value);
                                } else {
                                    bail!(
                                        "cannot redefine argument {:?} at position {} in {:?}",
                                        args[i].name,
                                        i,
                                        name
                                    );
                                }
                            }
                        }
                    }
                }

                let vs: Option<Vec<_>> = xs
                    .into_iter()
                    .enumerate()
                    .map(|(i, x)| x.or(args[i].default))
                    .collect();
                let mut vs = match vs {
                    Some(vs) => vs,
                    None => bail!("missing arguments in {:?}", name),
                };

                let rename_to = match op_def.rename_to {
                    Some(rename_to) => rename_to,
                    None => functor,
                };

                if op_def.embed_fixity {
                    vs.insert(0, arena.atom(String::from(fixity)));
                }

                if vs.is_empty() {
                    Ok(rename_to)
                } else {
                    Ok(arena.funcv(std::iter::once(&rename_to).chain(vs.iter()))?)
                }
            }
            None => match fixity {
                Fixity::Fun => Ok(term),
                _ => bail!("missing opdef for fixity {:?}", fixity),
            },
        }
    }
}

impl<I> Parser<Arena> for TermParser<I>
where
    I: FusedIterator<Item = u8>,
{
    type Lexer = TermLexer<I>;
    type ParserData = ParData;

    fn ctx(&self) -> &ParserCtx<Self::Lexer, Self::ParserData, Arena> {
        &self.ctx
    }

    fn ctx_mut(&mut self) -> &mut ParserCtx<Self::Lexer, Self::ParserData, Arena> {
        &mut self.ctx
    }

    fn stats(&self) -> ParserStats {
        self.ctx().stats.clone()
    }

    fn resolve_ambiguity(
        &mut self,
        _arena: &mut Arena,
        ambig: AmbigID,
        tok2: &TermToken,
    ) -> Result<Action> {
        let ambigs = ParData::lookup_ambig(ambig);

        let shift_action = ambigs[0];
        assert!(matches!(shift_action, Action::Shift(_)));

        let reduce_action = ambigs[1];
        assert!(matches!(reduce_action, Action::Reduce(_)));

        let Action::Reduce(prod) = reduce_action else {
            bail!("can't match reduce action")
        };

        log::trace!(
            "Conflict between reducing {:?} and shifting {:?}",
            prod,
            tok2
        );

        let (fixity1, tok1) = match prod {
            ProdID::Infix1 => {
                // Expr -> Expr atomOper Expr
                (Fixity::Infix, self.tokens_peek(1))
            }
            ProdID::Infix2 => {
                // Expr -> Expr funcOper Seq ) Expr
                (Fixity::Infix, self.tokens_peek(3))
            }
            ProdID::Prefix1 => {
                // Expr -> atomOper Expr
                (Fixity::Prefix, self.tokens_peek(1))
            }
            ProdID::Prefix2 => {
                // Expr -> funcOper Seq ) Expr
                (Fixity::Prefix, self.tokens_peek(3))
            }
            ProdID::Postfix1 => {
                // Expr -> Expr atomOper
                (Fixity::Postfix, self.tokens_peek(0))
            }
            ProdID::Postfix2 => {
                // Expr -> Expr funcOper Seq )
                (Fixity::Postfix, self.tokens_peek(2))
            }
            _ => bail!(
                "unexpected conflict: reduction of {:?} with shifting token {:?}",
                prod,
                tok2
            ),
        };

        let op_tab1 = self.ctx().lexer.opers.get(tok1.op_tab_index);
        let op_tab2 = self.ctx().lexer.opers.get(tok2.op_tab_index);

        assert!(op_tab1.is_oper());

        if op_tab2.is_oper() {
            let op_def1 = match op_tab1[fixity1] {
                Some(ref op_def1) => op_def1,
                None => return Ok(shift_action),
            };

            let prec1 = op_def1.prec;
            let assoc1 = op_def1.assoc;

            let min_prec2 = std::cmp::min(
                op_tab2[Fixity::Infix]
                    .as_ref()
                    .map(|x| x.prec)
                    .unwrap_or(MAX_OPER_PREC),
                op_tab2[Fixity::Postfix]
                    .as_ref()
                    .map(|x| x.prec)
                    .unwrap_or(MAX_OPER_PREC),
            );
            let max_prec2 = std::cmp::max(
                op_tab2[Fixity::Infix]
                    .as_ref()
                    .map(|x| x.prec)
                    .unwrap_or(MIN_OPER_PREC),
                op_tab2[Fixity::Postfix]
                    .as_ref()
                    .map(|x| x.prec)
                    .unwrap_or(MIN_OPER_PREC),
            );

            if prec1 > min_prec2 {
                Ok(reduce_action)
            } else if prec1 < max_prec2 {
                Ok(shift_action)
            } else if min_prec2 == max_prec2 && prec1 == min_prec2 {
                if assoc1 == Assoc::None {
                    bail!(
                        "precedence conflict: cannot chain non-associative operator {:?}; use parenthesis",
                        tok1
                    );
                }
                if op_tab2[Fixity::Infix]
                    .as_ref()
                    .is_some_and(|x| x.assoc == Assoc::None)
                    || op_tab2[Fixity::Postfix]
                        .as_ref()
                        .is_some_and(|x| x.assoc == Assoc::None)
                {
                    bail!(
                        "precedence conflict: cannot chain non-associative operator {:?}; use parenthesis",
                        tok2
                    );
                }
                if op_tab2[Fixity::Infix]
                    .as_ref()
                    .is_some_and(|x| x.assoc != assoc1)
                    || op_tab2[Fixity::Postfix]
                        .as_ref()
                        .is_some_and(|x| x.assoc != assoc1)
                {
                    bail!(
                        "associativity conflict: cannot chain operators {:?} and {:?}; use parenthesis",
                        tok1,
                        tok2
                    );
                } else {
                    if assoc1 == Assoc::Left {
                        Ok(reduce_action)
                    } else {
                        Ok(shift_action)
                    }
                }
            } else {
                bail!(
                    "precedence conflict: cannot chain operators {:?} and {:?}; use parenthesis",
                    tok1,
                    tok2
                );
            }
        } else {
            Ok(shift_action)
        }
    }

    fn reduce(&mut self, arena: &mut Arena, prod: ProdID, token: &TermToken) -> Result<()> {
        match prod {
            ProdID::Start => {
                // Accept - does not get reduced
                unreachable!()
            }

            ProdID::Term1 => {
                // Term -> Expr
                let mut expr_tok = self.tokens_pop()?;
                expr_tok.token_id = TokenID::Term;
                self.tokens_push(expr_tok);
            }

            ProdID::Term2 => {
                // Term -> Expr .
                self.tokens_pop()?;
                let mut expr_tok = self.tokens_pop()?;
                expr_tok.token_id = TokenID::Term;
                self.tokens_push(expr_tok);
            }

            ProdID::Term3 => {
                // Term ->
                self.tokens_push(TermToken::new(TokenID::Term, Value::None, token.line_no));
            }

            ProdID::Term4 => {
                // Term -> .
                self.tokens_pop()?;
                self.tokens_push(TermToken::new(TokenID::Term, Value::None, token.line_no));
            }

            ProdID::Func => {
                // Expr -> func Seq )
                self.tokens_pop()?;
                let index = usize::try_from(self.tokens_pop()?.value)?;
                let func_tok = self.tokens_pop()?;
                let line_no = func_tok.line_no;
                let op_tab_index = func_tok.op_tab_index;
                let functor = Term::try_from(func_tok.value)?;

                let vs = std::iter::once(&functor).chain(self.terms[index..].iter());
                let term = arena.funcv(vs)?;
                self.terms.truncate(index);

                let term = self.normalize_term(arena, term, Fixity::Fun, op_tab_index)?;

                self.tokens_push(TermToken::new(TokenID::Expr, Value::Term(term), line_no));
            }

            ProdID::List => {
                // Expr -> [ Seq ]
                self.tokens_pop()?;
                let seq_tok = self.tokens_pop()?;
                let left_brack_tok = self.tokens_pop()?;
                let index = usize::try_from(seq_tok.value)?;

                let term = arena.list(&self.terms[index..]);
                self.terms.truncate(index);

                self.tokens_push(TermToken::new(
                    TokenID::Expr,
                    Value::Term(term),
                    left_brack_tok.line_no,
                ));
            }

            ProdID::Nil => {
                // Expr -> [ ]
                self.tokens_pop()?;
                let left_brack_tok = self.tokens_pop()?;
                self.tokens_push(TermToken::new(
                    TokenID::Expr,
                    Value::Term(Term::NIL),
                    left_brack_tok.line_no,
                ));
            }

            ProdID::List2 => {
                // Expr -> [ Seq | Expr ]
                self.tokens_pop()?;
                let tail = Term::try_from(self.tokens_pop()?.value)?;
                self.tokens_pop()?;
                let index = usize::try_from(self.tokens_pop()?.value)?;
                let left_brack_tok = self.tokens_pop()?;

                let term = arena.listc(&self.terms[index..], tail);
                self.terms.truncate(index);

                self.tokens_push(TermToken::new(
                    TokenID::Expr,
                    Value::Term(term),
                    left_brack_tok.line_no,
                ));
            }

            ProdID::Tuple => {
                // Expr -> ( Seq )
                self.tokens_pop()?;
                let seq_tok = self.tokens_pop()?;
                let left_paren_tok = self.tokens_pop()?;

                let index = usize::try_from(seq_tok.value)?;

                // Arena terms parser does not currently support unary tuples.
                // TODO: Consider adding explicit unary tuple syntax `(expr,)`.
                let vs = &self.terms[index..];
                let term = if vs.len() == 1 {
                    vs[0]
                } else {
                    arena.tuple(vs)
                };
                self.terms.truncate(index);

                self.tokens_push(TermToken::new(
                    TokenID::Expr,
                    Value::Term(term),
                    left_paren_tok.line_no,
                ));
            }

            ProdID::Unit => {
                // Expr -> ( )
                self.tokens_pop()?;
                let left_paren_tok = self.tokens_pop()?;
                self.tokens_push(TermToken::new(
                    TokenID::Expr,
                    Value::Term(Term::UNIT),
                    left_paren_tok.line_no,
                ));
            }

            ProdID::Var | ProdID::Int | ProdID::Real | ProdID::Date | ProdID::Str | ProdID::Bin => {
                // Expr -> xxx
                let mut tok = self.tokens_pop()?;
                tok.token_id = TokenID::Expr;
                self.tokens_push(tok);
            }

            ProdID::Atom => {
                // Expr -> atom
                let atom_tok = self.tokens_pop()?;
                let line_no = atom_tok.line_no;
                let op_tab_index = atom_tok.op_tab_index;

                let atom = Term::try_from(atom_tok.value)?;

                let term = self.normalize_term(arena, atom, Fixity::Fun, op_tab_index)?;

                self.tokens_push(TermToken::new(TokenID::Expr, Value::Term(term), line_no));
            }

            ProdID::Infix1 => {
                // Expr -> Expr atomOper Expr
                let expr2_tok = self.tokens_pop()?;
                let oper_tok = self.tokens_pop()?;
                let expr1_tok = self.tokens_pop()?;
                let line_no = expr1_tok.line_no;
                let op_tab_index = oper_tok.op_tab_index;

                let expr2 = Term::try_from(expr2_tok.value)?;
                let oper = Term::try_from(oper_tok.value)?;
                let expr1 = Term::try_from(expr1_tok.value)?;

                let term = arena.funcv([oper, expr1, expr2])?;
                let term = self.normalize_term(arena, term, Fixity::Infix, op_tab_index)?;

                self.tokens_push(TermToken::new(TokenID::Expr, Value::Term(term), line_no));
            }

            ProdID::Infix2 => {
                // Expr -> Expr func Seq ) Expr
                let expr2_tok = self.tokens_pop()?;
                self.tokens_pop()?;
                let index = usize::try_from(self.tokens_pop()?.value)?;
                let oper_tok = self.tokens_pop()?;
                let expr1_tok = self.tokens_pop()?;
                let line_no = expr1_tok.line_no;
                let op_tab_index = oper_tok.op_tab_index;

                let expr2 = Term::try_from(expr2_tok.value)?;
                let oper = Term::try_from(oper_tok.value)?;
                let expr1 = Term::try_from(expr1_tok.value)?;

                let xs = [oper, expr1, expr2];
                let vs = xs.iter().chain(self.terms[index..].iter());
                let term = arena.funcv(vs)?;
                self.terms.truncate(index);

                let term = self.normalize_term(arena, term, Fixity::Infix, op_tab_index)?;

                self.tokens_push(TermToken::new(TokenID::Expr, Value::Term(term), line_no));
            }

            ProdID::Prefix1 => {
                // Expr -> atom Expr
                let expr1_tok = self.tokens_pop()?;
                let oper_tok = self.tokens_pop()?;
                let line_no = oper_tok.line_no;
                let op_tab_index = oper_tok.op_tab_index;

                let expr1 = Term::try_from(expr1_tok.value)?;
                let oper = Term::try_from(oper_tok.value)?;

                let term = match oper.view(arena)? {
                    // Arena terms parser currently gives special treatment to unary minus
                    // on integer and real literals (it directly negates them).
                    // TODO: Consider handling minus at the lexical level.
                    View::Atom(s)
                        if s == "-"
                            && matches!(expr1.view(arena)?, View::Int(_) | View::Real(_)) =>
                    {
                        match expr1.view(arena)? {
                            View::Int(i) => arena.int(-i),
                            View::Real(r) => arena.real(-r),
                            _ => unreachable!(),
                        }
                    }
                    _ => {
                        let term = arena.funcv([oper, expr1])?;
                        self.normalize_term(arena, term, Fixity::Prefix, op_tab_index)?
                    }
                };

                self.tokens_push(TermToken::new(TokenID::Expr, Value::Term(term), line_no));
            }

            ProdID::Prefix2 => {
                // Expr -> func Seq ) Expr
                let expr1_tok = self.tokens_pop()?;
                self.tokens_pop()?;
                let index = usize::try_from(self.tokens_pop()?.value)?;
                let oper_tok = self.tokens_pop()?;
                let line_no = oper_tok.line_no;
                let op_tab_index = oper_tok.op_tab_index;

                let oper = Term::try_from(oper_tok.value)?;
                let expr1 = Term::try_from(expr1_tok.value)?;

                let xs = [oper, expr1];
                let vs = xs.iter().chain(self.terms[index..].iter());
                let term = arena.funcv(vs)?;
                self.terms.truncate(index);

                let term = self.normalize_term(arena, term, Fixity::Prefix, op_tab_index)?;

                self.tokens_push(TermToken::new(TokenID::Expr, Value::Term(term), line_no));
            }

            ProdID::Postfix1 => {
                // Expr -> Expr atomOper
                let oper_tok = self.tokens_pop()?;
                let expr1_tok = self.tokens_pop()?;
                let line_no = expr1_tok.line_no;
                let op_tab_index = oper_tok.op_tab_index;

                let oper = Term::try_from(oper_tok.value)?;
                let expr1 = Term::try_from(expr1_tok.value)?;

                let term = arena.funcv([oper, expr1])?;
                let term = self.normalize_term(arena, term, Fixity::Postfix, op_tab_index)?;

                self.tokens_push(TermToken::new(TokenID::Expr, Value::Term(term), line_no));
            }

            ProdID::Postfix2 => {
                // Expr -> Expr func Seq )
                self.tokens_pop()?;
                let index = usize::try_from(self.tokens_pop()?.value)?;
                let oper_tok = self.tokens_pop()?;
                let expr1_tok = self.tokens_pop()?;
                let line_no = expr1_tok.line_no;
                let op_tab_index = oper_tok.op_tab_index;

                let oper = Term::try_from(oper_tok.value)?;
                let expr1 = Term::try_from(expr1_tok.value)?;

                let xs = [oper, expr1];
                let vs = xs.iter().chain(self.terms[index..].iter());
                let term = arena.funcv(vs)?;
                self.terms.truncate(index);

                let term = self.normalize_term(arena, term, Fixity::Postfix, op_tab_index)?;

                self.tokens_push(TermToken::new(TokenID::Expr, Value::Term(term), line_no));
            }

            ProdID::Seq1 => {
                // Seq -> BareSeq
                let mut bare_seq_tok = self.tokens_pop()?;
                bare_seq_tok.token_id = TokenID::Seq;
                self.tokens_push(bare_seq_tok);
            }

            ProdID::Seq2 => {
                // Seq -> BareSeq ,
                self.tokens_pop()?;
                let mut bare_seq_tok = self.tokens_pop()?;
                bare_seq_tok.token_id = TokenID::Seq;
                self.tokens_push(bare_seq_tok);
            }

            ProdID::BareSeq1 => {
                // BareSeq -> Expr
                let expr_tok = self.tokens_pop()?;
                let line_no = expr_tok.line_no;
                let expr = Term::try_from(expr_tok.value)?;

                let index = self.terms.len();
                self.terms.push(expr);

                self.tokens_push(TermToken::new(
                    TokenID::BareSeq,
                    Value::Index(index),
                    line_no,
                ));
            }

            ProdID::BareSeq2 => {
                // BareSeq -> BareSeq , Expr
                let expr_tok = self.tokens_pop()?;
                let expr = Term::try_from(expr_tok.value)?;
                self.tokens_pop()?;

                self.terms.push(expr);
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const SAMPLE_DEFS: &str = r#"[
op(==(x,y),infix,350,none),
op(!=(x,y),infix,350,none),
op( <(x,y),infix,350,none),
op( >(x,y),infix,350,none),
op(<=(x,y),infix,350,none),
op(>=(x,y),infix,350,none),
op('+'(x,y),infix,380,left),
op('-'(x,y),infix,380,left),
op('-'(x),postfix,900,left, rename_to=some('postfix_minus')),
op('*'(x,y),infix,400,left),
op('/'(x,y),infix,400,left),
op('+'(x),prefix,800,right),
op(and(x,y),infix,300,left),
op(or(x,y),infix,250,left),
op(not(x),prefix,800,right),
]"#;

    fn parse(arena: &mut Arena, defs: Option<&str>, s: &str) -> Result<Vec<Term>> {
        let mut parser = TermParser::try_new(s.bytes().fuse(), Some(parser_oper_defs(arena)))?;
        if let Some(defs) = defs {
            parser.define_opers(arena, defs.bytes().fuse(), None)?;
        }
        parser.try_collect_terms(arena)
    }

    #[test]
    fn one_term() {
        let _ = env_logger::builder().is_test(true).try_init();
        let arena = &mut Arena::new();
        let ts = parse(arena, Some(SAMPLE_DEFS), " . . 2 * 2 <= 5 . .").unwrap();
        dbg!(&ts);
        let s = format!("{}", ts[0].display(arena));
        dbg!(&s);
        assert_eq!(ts.len(), 1);
        assert_eq!(s, "'<='('*'(2, 2), 5)");
    }

    #[test]
    #[should_panic]
    fn missing_ops() {
        let arena = &mut Arena::new();
        let ts = parse(arena, None, "2 * 2 <= 5").unwrap();
    }

    #[test]
    fn more_complicated_term() {
        let _ = env_logger::builder().is_test(true).try_init();
        let arena = &mut Arena::new();
        let x = "(
[(1, 2) | unit] ++ foo(baz(1e-9)),
date{2025-09-30T18:24:22.154Z},
\"aaa{
1 + 2
}bbb{
3 * 4
}ccc\",
{player = {pos = {x = 0, y = 0}, health = 100}},
)";
        let ts = parse(arena, Some(SAMPLE_DEFS), x).unwrap();
        let s = format!("{}", ts[0].display(arena));
        assert_eq!(ts.len(), 1);
        assert_eq!(
            s,
            "('++'([(1, 2) | unit], foo(baz(0.000000001))), date(2025-09-30T18:24:22.154+00:00), '++'('++'('++'('++'(\"aaa\", '+'(1, 2)), \"bbb\"), '*'(3, 4)), \"ccc\"), \"player = {pos = {x = 0, y = 0}, health = 100}\")"
        );
    }
}
