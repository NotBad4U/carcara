use std::collections::HashMap;

use crate::ast::*;

pub struct RewritingRules(pub HashMap<String, RewriteRule>);

impl std::fmt::Debug for RewritingRules {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(f, "{:?}", self.0)
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct RewriteRule {
    pub id: String,
    pub is_rec: bool,
    pub params: Vec<Parameter>,
    pub precondition: Option<Rc<Term>>,
    pub match_expr: Rc<Term>,
    pub target_expr: Rc<Term>,
}

#[derive(Debug, PartialEq, Eq)]
pub struct Parameter {
    pub id: String,
    pub sort: Rc<Term>,
    pub attrs: Vec<Attribute>,
}

#[derive(Debug, PartialEq, Eq)]
pub enum Attribute {
    List,
}

impl From<String> for Attribute {
    // Required method
    fn from(value: String) -> Self {
        match value.as_str() {
            "list" => Attribute::List,
            s => unimplemented!("attribute {}", s),
        }
    }
}