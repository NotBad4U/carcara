use super::*;
use itertools::Itertools;
use pretty::RcDoc;
use std::io::{self};

pub const DEFAULT_WIDTH: usize = 120;
pub const DEFAULT_INDENT: isize = 4;

pub const WHITE_SPACE: &str = " ";
const LBRACE: &str = "{";
const RBRACE: &str = "}";
const COMMA: &str = ",";
const CLAUSE_NIL: &str = "□";

const NIL: &str = "⧈";

macro_rules! concat {
    ($l:expr => $( $r:expr ) => * ) => { $l$(.append($r))* };
}

/// Characters that cannot appear in a Lambdapi regular identifier
/// (`forbidden_letter` in its lexer).
const FORBIDDEN: &[char] = &[
    ' ', ',', ';', '\r', '\t', '\n', '(', ')', '{', '}', '[', ']', ':', '.', '`', '"', '@', '$',
    '|', '/',
];

/// Lambdapi keywords, which are not identifiers either even though their spelling is
/// otherwise regular.
const KEYWORDS: &[&str] = &[
    "abort",
    "admit",
    "admitted",
    "all_hyps",
    "apply",
    "as",
    "assert",
    "assertnot",
    "associative",
    "assume",
    "assumption",
    "begin",
    "builtin",
    "change",
    "coerce_rule",
    "commutative",
    "compute",
    "constant",
    "debug",
    "end",
    "eval",
    "fail",
    "first_hyp",
    "flag",
    "focus",
    "generalize",
    "have",
    "in",
    "induction",
    "inductive",
    "infix",
    "injective",
    "left",
    "let",
    "notation",
    "off",
    "on",
    "opaque",
    "open",
    "orelse",
    "postfix",
    "prefix",
    "print",
    "private",
    "proofterm",
    "protected",
    "prover",
    "prover_timeout",
    "quantifier",
    "refine",
    "reflexivity",
    "remove",
    "repeat",
    "require",
    "rewrite",
    "right",
    "rule",
    "search",
    "sequential",
    "set",
    "simplify",
    "solve",
    "symbol",
    "symmetry",
    "try",
    "type",
    "TYPE",
    "unif_rule",
    "verbose",
    "why3",
    "with",
    "≔",
    "→",
    "≡",
    "↪",
    "λ",
    "Π",
    "⊢",
    "_",
];

/// Would Lambdapi refuse to read `s` as an identifier?
fn is_irregular(s: &str) -> bool {
    // `/` on its own is the one forbidden character that is also a valid identifier.
    s != "/" && (s.is_empty() || s.contains(FORBIDDEN) || KEYWORDS.contains(&s))
}

/// Render an identifier, wrapping it in `{|…|}` when `escape` is set and Lambdapi
/// would not accept it as written.
///
/// SMT-LIB symbols are far more permissive than Lambdapi identifiers -- an
/// Isabelle/HOL export names its sorts `S$`, `A_literal_multiset$` and its functions
/// `fun_app$`, and `$` is one of the characters Lambdapi forbids. Escaping keeps the
/// original name; mangling it instead would lose the distinction between two symbols
/// that differ only in a stripped character. It is off by default because escaped
/// names are noisier to read and most problems never need them; the CLI turns it on
/// with `-e`.
///
/// Only ever applied to names -- `Term::TermId`, and the binder positions of
/// `symbol`, `have`, `assume` and friends. Module paths are excluded: they are dotted
/// on purpose, and `{|alethe.core|}` would name a module with a dot in it.
///
/// Escaped identifiers cannot themselves contain `|}`; an SMT-LIB quoted symbol
/// cannot contain `|` at all, so nothing reachable from a problem can hit that.
fn ident(s: &str, escape: bool) -> RcDoc<'_, ()> {
    if escape && is_irregular(s) {
        RcDoc::text(format!("{{|{s}|}}"))
    } else {
        RcDoc::text(s)
    }
}

pub trait PrettyPrint {
    /// Render, wrapping identifiers Lambdapi would reject in `{|…|}` when `escape`
    /// is set. See [`ident`].
    fn to_doc_with(&self, escape: bool) -> RcDoc<'_, ()>;

    fn to_doc(&self) -> RcDoc<'_, ()> {
        self.to_doc_with(false)
    }

    fn to_pretty_with_width(&self, width: usize) -> String {
        let mut w = Vec::new();
        self.to_doc().render(width, &mut w).unwrap();
        String::from_utf8(w).unwrap()
    }

    fn to_pretty(&self) -> String {
        self.to_pretty_with_width(DEFAULT_WIDTH)
    }

    fn render_with(&self, f: &mut impl io::Write, escape: bool) -> io::Result<()> {
        let doc = self.to_doc_with(escape);
        doc.render(DEFAULT_WIDTH, f)
    }

    fn render(&self, f: &mut impl io::Write) -> io::Result<()> {
        self.render_with(f, false)
    }

    fn render_fmt(&self, f: &mut impl std::fmt::Write) -> std::fmt::Result {
        let doc = self.to_doc();
        doc.render_fmt(DEFAULT_WIDTH, f)
    }
}

pub trait PrettyHelper<'a, T: 'a>: Sized {
    fn surround(self, pre: &'a str, post: &'a str) -> Self;

    fn surround_doc(self, pre: RcDoc<'a, T>, post: RcDoc<'a, T>) -> Self;

    fn semicolon(self) -> Self;

    fn begin_end(self) -> Self {
        self.surround_doc(
            RcDoc::line().append(RcDoc::text("begin").append(RcDoc::line())),
            RcDoc::line().append(RcDoc::text("end")),
        )
    }

    fn parens(self) -> Self {
        self.surround("(", ")")
    }

    fn braces(self) -> Self {
        self.surround(LBRACE, RBRACE)
    }

    fn spaces(self) -> Self {
        self.surround(WHITE_SPACE, WHITE_SPACE)
    }
}

impl<'a, A> PrettyHelper<'a, A> for RcDoc<'a, A> {
    fn surround(self, l: &'a str, r: &'a str) -> Self {
        RcDoc::text(l).append(self).append(RcDoc::text(r))
    }

    fn surround_doc(self, pre: RcDoc<'a, A>, post: RcDoc<'a, A>) -> Self {
        pre.append(self).append(post)
    }

    fn semicolon(self) -> Self {
        self.append(RcDoc::text(";"))
    }
}

#[inline]
fn arrow<'a>() -> RcDoc<'a, ()> {
    RcDoc::text("→")
}

#[inline]
fn semicolon<'a>() -> RcDoc<'a, ()> {
    RcDoc::text(";")
}

#[inline]
fn symbol<'a>() -> RcDoc<'a, ()> {
    RcDoc::text("symbol")
}

#[inline]
fn is<'a>() -> RcDoc<'a, ()> {
    text("≔").spaces()
}

#[inline]
fn space<'a>() -> RcDoc<'a, ()> {
    RcDoc::space()
}

#[inline]
fn text<'a>(s: &'a str) -> RcDoc<'a, ()> {
    RcDoc::text(s)
}

#[inline]
fn colon<'a>() -> RcDoc<'a, ()> {
    text(":")
}

#[inline]
fn tab<'a>() -> RcDoc<'a, ()> {
    RcDoc::text(" ".repeat(DEFAULT_INDENT as usize))
}

#[inline]
fn line<'a>() -> RcDoc<'a, ()> {
    RcDoc::line()
}

impl PrettyPrint for BuiltinSort {
    fn to_doc_with(&self, escape: bool) -> RcDoc<'_, ()> {
        match self {
            BuiltinSort::Bool => text("o"),
            BuiltinSort::Int => text("int"),
            BuiltinSort::Arrow(a, b) => concat! {
                a.to_doc_with(escape)
                => text("⤳").spaces()
                => b.to_doc_with(escape)
            },
        }
    }
}

impl PrettyPrint for Term {
    fn to_doc_with(&self, escape: bool) -> RcDoc<'_, ()> {
        match self {
            Term::Alethe(term) => term.to_doc_with(escape),
            Term::TermId(id) => ident(id, escape),
            Term::Underscore => text("_"),
            Term::Sort(sort) => sort.to_doc_with(escape),
            Term::Terms(terms) => {
                RcDoc::intersperse(terms.iter().map(|term| term.to_doc_with(escape)), space())
                    .parens()
            }
            Term::Function(terms) => RcDoc::intersperse(
                terms.iter().map(|term| term.to_doc_with(escape)),
                arrow().spaces(),
            ),
            Term::Nat(n) => RcDoc::text(nat_literal(*n)),
            Term::Int(i) => RcDoc::text(int_literal(i)),
        }
    }
}

impl PrettyPrint for Modifier {
    fn to_doc_with(&self, _escape: bool) -> RcDoc<'_, ()> {
        match self {
            Modifier::Constant => text("constant"),
            Modifier::Opaque => text("opaque"),
        }
    }
}

impl PrettyPrint for SortedTerm {
    fn to_doc_with(&self, escape: bool) -> RcDoc<'_, ()> {
        self.0
            .to_doc_with(escape)
            .append(space())
            .append(self.1.to_doc_with(escape))
    }
}

impl PrettyPrint for VecN {
    fn to_doc_with(&self, escape: bool) -> RcDoc<'_, ()> {
        // Take the last element because we will reverse the list latter so: last l = first (rev l)
        let (first, elems) = self.0.split_last().expect("distinct should not be empty");

        // Generate the root of the vector: (cons _  term1 □)
        let first_doc = concat! {
            text("cons") // constructor
            => first.to_doc_with(escape).spaces() // element
            => text(NIL)
        }
        .parens();

        // Generate a vector (cons _  term_n ... (cons _  term2 (cons _  term1 □))

        elems.iter().fold(first_doc, |acc, elem| {
            concat! {
                text("cons") // constructor
                => elem.to_doc_with(escape).spaces() // element
                => acc // rest of the vector
            }
            .parens()
        })
    }
}

impl PrettyPrint for List {
    fn to_doc_with(&self, escape: bool) -> RcDoc<'_, ()> {
        self.0.iter().fold(text("□"), |acc, elem| {
            concat! {
                elem.to_doc_with(escape).clone()
                => text("⸬").spaces()
                => acc
            }
        })
    }
}

impl PrettyPrint for LTerm {
    fn to_doc_with(&self, escape: bool) -> RcDoc<'_, ()> {
        match self {
            LTerm::True => text("⊤"),
            LTerm::False => text("⊥"),
            LTerm::NAnd(terms) => RcDoc::intersperse(
                terms.iter().map(|term| term.to_doc_with(escape)),
                text("∧").spaces(),
            )
            .parens(),
            LTerm::NOr(terms) => RcDoc::intersperse(
                terms.iter().map(|term| term.to_doc_with(escape)),
                text("∨").spaces(),
            )
            .parens(),
            LTerm::Neg(Some(term)) => text("¬")
                .append(space())
                .append(term.to_doc_with(escape).parens())
                .parens(),
            LTerm::Neg(None) => text("¬"),
            LTerm::Proof(term) => text("π̇").append(space()).append(term.to_doc_with(escape)),
            LTerm::ClassicProof(term) => text("π").append(space()).append(term.to_doc_with(escape)),
            LTerm::Clauses(terms) => {
                if terms.is_empty() {
                    text(CLAUSE_NIL)
                } else {
                    RcDoc::intersperse(
                        terms.iter().map(|term| term.to_doc_with(escape)),
                        line().append(text("⸬").spaces()),
                    )
                    .append(line().append(text("⸬").append(space()).append(text(CLAUSE_NIL))))
                    .group()
                    .parens()
                    .nest(DEFAULT_INDENT)
                }
            }
            LTerm::Eq(l, r) => l
                .to_doc_with(escape)
                .append(text("=").spaces())
                .append(r.to_doc_with(escape))
                .parens(),
            LTerm::Iff(l, r) => l
                .to_doc_with(escape)
                .append(text("⇔").spaces())
                .append(r.to_doc_with(escape))
                .parens(),
            LTerm::Implies(l, r) => l
                .to_doc_with(escape)
                .parens()
                .append(space().append(text("⇒")).append(space()))
                .append(r.to_doc_with(escape).parens())
                .parens(),
            LTerm::Exist(bindings, term) => RcDoc::intersperse(
                bindings.0.iter().map(|b| {
                    text("`∃")
                        .append(space())
                        .append(
                            b.0.to_doc_with(escape)
                                .append(text(":").spaces().append(b.1.to_doc_with(escape)))
                                .parens(),
                        )
                        .append(COMMA)
                }), // we ignore the type here
                space(),
            )
            .append(term.to_doc_with(escape))
            .parens(),
            LTerm::Forall(bindings, term) => RcDoc::intersperse(
                bindings.0.iter().map(|b| {
                    text("`∀")
                        .append(space())
                        .append(
                            b.0.to_doc_with(escape)
                                .append(text(":").spaces().append(b.1.to_doc_with(escape)))
                                .parens(),
                        )
                        .append(COMMA)
                }), // we ignore the type here
                space(),
            )
            .append(space())
            .append(term.to_doc_with(escape))
            .parens(),
            LTerm::Distinct(v) => concat! {
                text("distinct")
                => v.to_doc_with(escape)
            }
            .parens(),
            LTerm::List(l) => l.to_doc_with(escape).parens(),
            LTerm::Choice(bindings, p) => concat!(
                RcDoc::intersperse(bindings.0.iter().map(|b| {
                    text("`ϵ")
                        .append(space())
                        .append(b.0.to_doc_with(escape))
                        .append(COMMA)
                }), space())
                => space()
                => p.to_doc_with(escape)
            )
            .parens(),
        }
    }
}

impl PrettyPrint for Param {
    fn to_doc_with(&self, escape: bool) -> RcDoc<'_, ()> {
        // Parenthesised: a symbol's parameters sit between its name and the `:` of
        // its type, so `symbol f x : A : B;` would not parse. Every call site passed
        // an empty parameter list until the goal hypothesis started being threaded
        // through the steps that use it, so this had never been exercised.
        ident(self.0.as_str(), escape)
            .append(colon().spaces())
            .append(self.1.to_doc_with(escape))
            .parens()
    }
}

impl PrettyPrint for ProofStep {
    fn to_doc_with(&self, escape: bool) -> RcDoc<'_, ()> {
        match self {
            ProofStep::Admit => RcDoc::text("admit").append(semicolon()),
            ProofStep::Apply(t, subproofs) => RcDoc::text("apply")
                .append(space())
                .append(t.to_doc_with(escape))
                .append(subproofs.0.is_some().then(space))
                .append(subproofs.0.as_ref().map_or(RcDoc::nil(), |proofs| {
                    RcDoc::intersperse(
                        proofs
                            .iter()
                            .map(|p| {
                                line()
                                    .append(text(LBRACE).append(line()))
                                    .append(tab()) //FIXME: we append a tab because `assume` is not incremented (hack)
                                    .append(p.to_doc_with(escape).nest(4))
                                    .append(line().append(RBRACE))
                            })
                            .collect_vec(),
                        RcDoc::nil(),
                    )
                }))
                .append(semicolon()),
            ProofStep::Assume(params) => text("assume")
                .append(space())
                .append(RcDoc::intersperse(
                    params.iter().map(|p| ident(p, escape)),
                    space(),
                ))
                .append(semicolon()),
            ProofStep::Have(name, r#type, steps) => text("have")
                .append(space())
                .append(ident(name, escape))
                .append(colon().spaces())
                .append(r#type.to_doc_with(escape))
                .append(space())
                .append(LBRACE)
                .append(line())
                .append(RcDoc::intersperse(
                    steps.iter().map(|s| s.to_doc_with(escape)),
                    line(),
                ))
                .append(line())
                .nest(DEFAULT_INDENT)
                .append(text(RBRACE))
                .append(semicolon()),
            ProofStep::Change(t) => text("change")
                .append(space())
                .append(t.to_doc_with(escape))
                .semicolon(),
            ProofStep::Reflexivity => text("reflexivity").append(semicolon()),
            ProofStep::Refine(func, subproofs) => text("refine")
                .append(space())
                .append(func.to_doc_with(escape))
                .append(space())
                .append(subproofs.0.as_ref().map_or(RcDoc::nil(), |proofs| {
                    RcDoc::intersperse(
                        proofs
                            .iter()
                            .map(|p| RcDoc::braces(p.to_doc_with(escape)))
                            .collect_vec(),
                        line(),
                    )
                }))
                .append(semicolon()),
            ProofStep::Try(t) => text("try").append(space()).append(t.to_doc_with(escape)),
            ProofStep::Rewrite(flag, pattern, h, args, subproofs) => text("rewrite")
                .append(flag.then(|| text("left").spaces()).unwrap_or(text("")))
                .append(space())
                .append(pattern.as_ref().map_or(text(""), |pattern| {
                    text(".").append(text(pattern.as_str())).append(space())
                }))
                .append(
                    h.to_doc_with(escape)
                        .append(args.is_empty().then(RcDoc::nil).unwrap_or(space()))
                        .append(RcDoc::intersperse(
                            args.iter().map(|a| a.to_doc_with(escape).parens()),
                            space(),
                        )), //.spaces(),
                )
                .append(subproofs.0.is_some().then(space))
                .append(subproofs.0.as_ref().map_or(RcDoc::nil(), |proofs| {
                    RcDoc::intersperse(
                        proofs
                            .iter()
                            .map(|p| {
                                line()
                                    .append(text(LBRACE).append(line()))
                                    .append(tab()) //FIXME: we append a tab because `assume` is not incremented (hack)
                                    .append(p.to_doc_with(escape).nest(4))
                                    .append(line().append(RBRACE))
                            })
                            .collect_vec(),
                        RcDoc::nil(),
                    )
                }))
                .append(semicolon()),
            ProofStep::Symmetry => text("symmetry").append(semicolon()),
            ProofStep::Simplify(ss) if ss.is_empty() => text("simplify").append(semicolon()),
            ProofStep::Simplify(ss) => ss.iter().fold(RcDoc::nil(), |acc, s| {
                // We have to generate one simplify per term because Lambdapi does not support multiple arguments for simplify
                acc.append(text("simplify").append(space()).append(ident(s, escape)))
                    .append(semicolon())
            }),
            ProofStep::Set(name, def) => text("set").append(space()).append(
                ident(name, escape)
                    .append(is())
                    .append(def.to_doc_with(escape))
                    .append(semicolon()),
            ),
            ProofStep::Varmap(name, list) => text("set").append(space()).append(
                ident(name, escape)
                    .append(is())
                    .append(
                        RcDoc::intersperse(
                            list.iter().map(|term| term.to_doc_with(escape)),
                            text("⸬").spaces(),
                        )
                        .append(text("⸬").spaces())
                        .append(NIL),
                    )
                    .append(semicolon()),
            ),
            ProofStep::Why3 => text("why3").append(semicolon()),
            ProofStep::Eval(t) => text("eval")
                .append(t.to_doc_with(escape).spaces())
                .append(semicolon()),
        }
    }
}

impl PrettyPrint for Proof {
    fn to_doc_with(&self, escape: bool) -> RcDoc<'_, ()> {
        RcDoc::intersperse(self.0.iter().map(|step| step.to_doc_with(escape)), line())
    }
}

impl PrettyPrint for Command {
    fn to_doc_with(&self, escape: bool) -> RcDoc<'_, ()> {
        match self {
            Command::RequireOpen(path) => text("require open")
                .append(space())
                .append(text(path))
                .semicolon(),
            Command::Symbol(modifier, name, params, r#text, proof) => modifier
                .as_ref()
                .map_or(RcDoc::nil(), |m| m.to_doc_with(escape).append(space()))
                .append(symbol())
                .append(space())
                .append(ident(name, escape))
                .append(
                    params.is_empty().then(RcDoc::nil).unwrap_or(
                        RcDoc::intersperse(params.iter().map(|p| p.to_doc_with(escape)), space())
                            .spaces(),
                    ),
                )
                .append(colon().spaces())
                .append(r#text.to_doc_with(escape))
                .append(proof.as_ref().map_or(RcDoc::nil(), |p| {
                    is().append(p.to_doc_with(escape).begin_end())
                }))
                .append(semicolon()),
            Command::Definition(name, params, r#type, definition) => symbol()
                .append(space())
                .append(ident(name, escape))
                .append(
                    params.is_empty().then(RcDoc::nil).unwrap_or(
                        RcDoc::intersperse(params.iter().map(|p| p.to_doc_with(escape)), space())
                            .spaces(),
                    ),
                )
                .append(r#type.as_ref().map_or(RcDoc::nil(), |ty| {
                    colon().spaces().append(ty.to_doc_with(escape))
                }))
                .append(
                    definition
                        .as_ref()
                        .map_or(RcDoc::nil(), |def| is().append(def.to_doc_with(escape))),
                )
                .append(semicolon()),
            Command::Rule(l, r) => text("rule")
                .append(space())
                .append(l.to_doc_with(escape))
                .append(text("↪").spaces())
                .append(r.to_doc_with(escape))
                .append(semicolon()),
        }
    }
}

impl PrettyPrint for ProofFile {
    fn to_doc_with(&self, escape: bool) -> RcDoc<'_, ()> {
        RcDoc::intersperse(
            self.requires
                .iter()
                .chain(self.definitions.iter())
                .chain(self.content.iter())
                .map(|cmd| cmd.to_doc_with(escape)),
            line().append(line()),
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn only_irregular_identifiers_are_escaped() {
        // Names the library and the printer produce all the time. Escaping any of
        // these would rename a symbol that does exist into one that does not.
        for regular in [
            "t14",
            "p_8",
            "hGoal",
            "∨ᵢ₁",
            "π̇ₗ",
            "clᵢ₁'",
            "⊤ᵢ",
            "disj_resolutionN2",
            "?v0",
            "#repeat_or_id_r",
            "τ",
            "=",
            "⇒",
            "/",
        ] {
            assert!(!is_irregular(regular), "{regular} should be left alone");
        }

        // `$` is what an Isabelle/HOL export uses; the rest round out the forbidden
        // set, and `rule` is a keyword whose spelling is otherwise regular.
        for irregular in [
            "S$", "fun_app$", "a.b", "a b", "a|b", "a@b", "(=)", "rule", "",
        ] {
            assert!(is_irregular(irregular), "{irregular} should be escaped");
        }
    }

    #[test]
    fn escaping_is_off_unless_asked() {
        let term = Term::TermId("fun_app$".to_owned());
        assert_eq!(
            term.to_doc_with(false).pretty(DEFAULT_WIDTH).to_string(),
            "fun_app$"
        );
        assert_eq!(
            term.to_doc_with(true).pretty(DEFAULT_WIDTH).to_string(),
            "{|fun_app$|}"
        );
    }

    /// An operator used as a value is a parenthesised term, not a name, so it must
    /// survive escaping unchanged.
    #[test]
    fn an_operator_section_is_not_a_name() {
        let section = Term::from(crate::ast::Operator::Equals);
        assert_eq!(
            section.to_doc_with(true).pretty(DEFAULT_WIDTH).to_string(),
            "(=)"
        );
    }
}
