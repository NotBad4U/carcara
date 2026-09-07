use super::Command;
use std::fmt;
use std::io;

use super::printer::PrettyPrint;

impl fmt::Display for ProofFile {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.render_fmt(f)
    }
}

pub trait Render {
    fn render<W: io::Write>(&self, f: &mut io::BufWriter<W>) -> io::Result<()>;
}

/// Lambdapi files are formed of a list of commands.
pub struct ProofFile {
    pub requires: Vec<Command>,
    pub definitions: Vec<Command>,
    pub content: Vec<Command>,
}

impl Render for ProofFile {
    fn render<W: io::Write>(&self, f: &mut io::BufWriter<W>) -> io::Result<()> {
        PrettyPrint::render(self, f)
    }
}

impl Default for ProofFile {
    fn default() -> Self {
        Self::new()
    }
}

impl ProofFile {
    pub fn new() -> ProofFile {
        Self {
            requires: Vec::new(),
            definitions: Vec::new(),
            content: Vec::new(),
        }
    }
}
