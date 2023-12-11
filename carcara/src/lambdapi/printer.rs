use super::*;
use pretty::RcDoc;

pub const DEFAULT_WIDTH: usize = 120;
pub const DEFAULT_INDENT: isize = 4;

const LBRACE: &'static str = "{";
const RBRACE: &'static str = "}";
const COMMA: &'static str = ",";
const CLAUSE_NIL: &'static str = "▩";

const CONS: &'static str = "⸬";
const NIL: &'static str = "□";

macro_rules! concat {
    ($l:expr => $( $r:expr ) => * ) => {
        $l$(.append($r))*
    };
}

pub trait PrettyPrint {
    fn to_doc(&self) -> RcDoc<()>;

    fn to_pretty_with_width(&self, width: usize) -> String {
        let mut w = Vec::new();
        self.to_doc().render(width, &mut w).unwrap();
        String::from_utf8(w).unwrap()
    }

    fn to_pretty(&self) -> String {
        self.to_pretty_with_width(DEFAULT_WIDTH)
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
fn classic<'a>(op: &'a str) -> RcDoc<'a, ()> {
    text(op).append(text("ᶜ"))
}

#[inline]
fn colon<'a>() -> RcDoc<'a, ()> {
    text(":")
}

#[inline]
fn implicit<'a, T: PrettyPrint>(x: &'a Option<Box<T>>) -> RcDoc<'a, ()> {
    x.as_ref().map_or(text("_"), |x| x.to_doc())
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
    fn to_doc(&self) -> RcDoc<()> {
        match self {
            BuiltinSort::Bool => text("Prop"),
        }
    }
}

impl PrettyPrint for Term {
    fn to_doc(&self) -> RcDoc<()> {
        match self {
            Term::Alethe(term) => term.to_doc(),
            Term::TermId(id) => text(id),
            Term::Underscore => text("_"),
            Term::Sort(sort) => sort.to_doc(),
            Term::Terms(terms) => {
                RcDoc::intersperse(terms.iter().map(|term| term.to_doc()), space()).parens()
            }
            Term::Function(terms) => {
                RcDoc::intersperse(terms.iter().map(|term| term.to_doc()), arrow().spaces())
            }
        }
    }
}

impl PrettyPrint for Modifier {
    fn to_doc(&self) -> RcDoc<()> {
        match self {
            Modifier::Constant => text("constant"),
            Modifier::Opaque => text("opaque"),
        }
    }
}

impl PrettyPrint for SortedTerm {
    fn to_doc(&self) -> RcDoc<()> {
        self.0.to_doc().append(space()).append(self.1.to_doc())
    }
}

impl PrettyPrint for ListLP {
    fn to_doc(&self) -> RcDoc<()> {
        RcDoc::intersperse(self.0.iter().map(|term| term.to_doc()), text(CONS).spaces())
            .append(space().append(text(CONS)).append(space()).append(NIL))
            .parens()
    }
}

impl PrettyPrint for LTerm {
    fn to_doc(&self) -> RcDoc<()> {
        match self {
            LTerm::True => text("⊤"),
            LTerm::False => text("⊥"),
            LTerm::NAnd(terms) => RcDoc::intersperse(
                terms.into_iter().map(|term| term.to_doc()),
                classic("∧").spaces(),
            )
            .parens(),
            LTerm::NOr(terms) => RcDoc::intersperse(
                terms.into_iter().map(|term| term.to_doc()),
                classic("∨").spaces(),
            )
            .parens(),
            LTerm::Neg(Some(term)) => classic("¬")
                .append(space())
                .append(term.to_doc().parens())
                .parens(),
            LTerm::Neg(None) => classic("¬"),
            LTerm::Proof(term) => text("π̇").append(space()).append(term.to_doc()),
            LTerm::Clauses(terms) => {
                if terms.is_empty() {
                    text(CLAUSE_NIL)
                } else {
                    RcDoc::intersperse(
                        terms.into_iter().map(|term| term.to_doc()),
                        line().append(text("⟇").spaces()),
                    )
                    .append(line().append(text("⟇").append(space()).append(text(CLAUSE_NIL))))
                    .group()
                    .parens()
                    .nest(DEFAULT_INDENT)
                }
            }
            LTerm::Eq(l, r) => l
                .to_doc()
                .append(space().append(classic("⟺")).append(space()))
                .append(r.to_doc())
                .parens(),
            LTerm::Implies(l, r) => l
                .to_doc()
                .parens()
                .append(space().append(classic("⟹")).append(space()))
                .append(r.to_doc().parens())
                .parens(),
            LTerm::Exist(bindings, term) => RcDoc::intersperse(
                bindings.0.iter().map(|b| {
                    classic("`∃")
                        .append(space())
                        .append(b.0.to_doc())
                        .append(COMMA)
                }), // we ignore the type here
                space(),
            )
            .append(term.to_doc())
            .parens(),
            LTerm::Forall(bindings, term) => RcDoc::intersperse(
                bindings.0.iter().map(|b| {
                    classic("`∀")
                        .append(space())
                        .append(b.0.to_doc())
                        .append(COMMA)
                }), // we ignore the type here
                space(),
            )
            .append(space())
            .append(term.to_doc())
            .parens(),
            LTerm::Resolution(flag, pivot, a, b, hyp_pivot_a, hyp_pivot_b) => flag
                .then(|| text("resolutionₗ"))
                .unwrap_or(text("resolutionᵣ"))
                .append(space())
                .append(RcDoc::intersperse(
                    [
                        implicit(pivot),
                        implicit(a),
                        implicit(b),
                        hyp_pivot_a.to_doc(),
                        hyp_pivot_b.to_doc(),
                    ],
                    space(),
                )),
            LTerm::Distinct(v) => concat!(
                text("distinct")
                => space()
                => v.to_doc()
            ),
        }
    }
}

impl PrettyPrint for Param {
    fn to_doc(&self) -> RcDoc<()> {
        text(self.0.as_str())
            .append(colon().spaces())
            .append(self.1.to_doc())
    }
}

impl PrettyPrint for ProofStep {
    fn to_doc(&self) -> RcDoc<()> {
        match self {
            ProofStep::Admit => RcDoc::text("admit").append(semicolon()),
            ProofStep::Apply(func, args, subproofs) => RcDoc::text("apply")
                .append(space())
                .append(func.to_doc())
                .append(args.is_empty().then(|| RcDoc::nil()).unwrap_or(space()))
                .append(RcDoc::intersperse(args.iter().map(|a| a.to_doc()), space()))
                .append(subproofs.0.is_some().then(|| space()))
                .append(subproofs.0.as_ref().map_or(RcDoc::nil(), |proofs| {
                    RcDoc::intersperse(
                        proofs
                            .into_iter()
                            .map(|p| {
                                line()
                                    .append(text(LBRACE).append(line()))
                                    .append(tab()) //FIXME: we append a tab because `assume` is not incremented (hack)
                                    .append(p.to_doc().nest(4))
                                    .append(line().append(RBRACE))
                            })
                            .collect_vec(),
                        RcDoc::nil(),
                    )
                }))
                .append(semicolon()),
            ProofStep::Assume(params) => text("assume")
                .append(space())
                .append(RcDoc::intersperse(params.iter().map(|p| text(p)), space()))
                .append(semicolon()),
            ProofStep::Have(name, r#type, steps) => text("have")
                .append(space())
                .append(text(name))
                .append(colon().spaces())
                .append(r#type.to_doc())
                .append(space())
                .append(LBRACE)
                .append(line())
                .append(RcDoc::intersperse(
                    steps.into_iter().map(|s| s.to_doc()),
                    line(),
                ))
                .append(line())
                .nest(DEFAULT_INDENT)
                .append(text(RBRACE))
                .append(semicolon()),
            ProofStep::Reflexivity => text("reflexivity").append(semicolon()),
            ProofStep::Refine(func, args, subproofs) => text("refine")
                .append(space())
                .append(func.to_doc())
                .append(args.is_empty().then(|| RcDoc::nil()).unwrap_or(space()))
                .append(RcDoc::intersperse(args.iter().map(|a| a.to_doc()), space()))
                .append(subproofs.0.as_ref().map_or(RcDoc::nil(), |proofs| {
                    RcDoc::intersperse(
                        proofs
                            .into_iter()
                            .map(|p| RcDoc::braces(p.to_doc()))
                            .collect_vec(),
                        line(),
                    )
                }))
                .append(semicolon()),
        }
    }
}

impl PrettyPrint for Proof {
    fn to_doc(&self) -> RcDoc<()> {
        RcDoc::intersperse(self.0.iter().map(|step| step.to_doc()), line())
    }
}

impl PrettyPrint for Command {
    fn to_doc(&self) -> RcDoc<()> {
        match self {
            Command::RequireOpen(path) => text("require open")
                .append(space())
                .append(text(path))
                .semicolon(),
            Command::Symbol(modifier, name, params, r#text, proof) => modifier
                .as_ref()
                .map(|m| m.to_doc().append(space()))
                .unwrap_or(RcDoc::nil())
                .append(symbol())
                .append(space())
                .append(name)
                .append(params.is_empty().then(|| RcDoc::nil()).unwrap_or(
                    RcDoc::intersperse(params.into_iter().map(|p| p.to_doc()), space()).spaces(),
                ))
                .append(colon().spaces())
                .append(r#text.to_doc())
                .append(
                    proof
                        .as_ref()
                        .map_or(RcDoc::nil(), |p| is().append(p.to_doc().begin_end())),
                )
                .append(semicolon()),
            Command::Definition(name, r#type) => symbol()
                .append(space())
                .append(text(name))
                .append(space())
                .append(is())
                .append(r#type.to_doc())
                .append(semicolon()),
            Command::Rule(l, r) => text("rule")
                .append(space())
                .append(l.to_doc())
                .append(text("↪").spaces())
                .append(r.to_doc())
                .append(semicolon()),
        }
    }
}

impl PrettyPrint for LambdapiFile {
    fn to_doc(&self) -> RcDoc<()> {
        RcDoc::intersperse(self.0.iter().map(|cmd| cmd.to_doc()), line().append(line()))
    }
}
