use super::*;

/// Lambdapi files are formed of a list of commands.
#[derive(Default)]
pub struct LambdapiFile(pub VecDeque<Command>);

impl fmt::Display for LambdapiFile {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.render_fmt(f)
    }
}

impl LambdapiFile {
    #[inline]
    pub fn extend(&mut self, cs: Vec<Command>) {
        self.0.extend(cs)
    }

    #[inline]
    pub fn push_back(&mut self, cs: Command) {
        self.0.push_back(cs)
    }
}