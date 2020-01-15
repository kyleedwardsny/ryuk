use ryuk_lispcore::*;

#[derive(Debug)]
struct If<T>
where
    T: ValueTypes + ?Sized,
    for<'a> &'a <T::SemverTypes as SemverTypes>::Semver: IntoIterator<Item = &'a u64>,
{
    test: Box<dyn CompilationResultType<T>>,
    then: Box<dyn CompilationResultType<T>>,
    els: Option<Box<dyn CompilationResultType<T>>>,
}

impl<T> If<T>
where
    T: ValueTypes + ?Sized,
    for<'a> &'a <T::SemverTypes as SemverTypes>::Semver: IntoIterator<Item = &'a u64>,
{
    pub fn new(
        test: Box<dyn CompilationResultType<T>>,
        then: Box<dyn CompilationResultType<T>>,
        els: Option<Box<dyn CompilationResultType<T>>>,
    ) -> Self {
        If { test, then, els }
    }
}

impl<T> CompilationResultType<T> for If<T>
where
    T: ValueTypes + ?Sized + 'static,
    for<'a> &'a <T::SemverTypes as SemverTypes>::Semver: IntoIterator<Item = &'a u64>,
{
    fn evaluate(&mut self, env: &mut dyn Environment<T>) -> Result<Value<T>> {
        use std::convert::TryInto;

        let b: ValueBool = self.test.evaluate(env)?.try_into()?;
        if b.0 {
            self.then.evaluate(env)
        } else {
            (&mut self.els)
                .as_mut()
                .map_or_else(|| Result::Ok(Value::Nil), |comp| comp.evaluate(env))
        }
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn test_evaluate_if() {
        // TODO
    }
}
