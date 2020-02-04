use super::algo::*;
use super::error::*;
use super::list::*;
use super::value::*;
use std::collections::BTreeSet;
use std::fmt::Debug;
use std::iter::FromIterator;

pub trait Environment<C, D>
where
    C: ValueTypes + ?Sized + 'static,
    D: ValueTypesMut + ?Sized + 'static,
    D::StringTypes: StringTypesMut,
    D::SemverTypes: SemverTypesMut,
{
    fn as_dyn_mut(&mut self) -> &mut (dyn Environment<C, D> + 'static);

    fn resolve_symbol_get_variable(
        &self,
        name: &ValueUnqualifiedSymbol<C::StringTypes>,
    ) -> Option<ValueQualifiedSymbol<C::StringTypes>>;

    fn compile_variable(
        &self,
        name: &ValueQualifiedSymbol<C::StringTypes>,
    ) -> Option<BTreeSet<ValueType>>;

    fn resolve_symbol_get_macro(
        &self,
        name: &ValueUnqualifiedSymbol<C::StringTypes>,
    ) -> Option<ValueQualifiedSymbol<C::StringTypes>>;

    fn compile_function(
        &self,
        name: &ValueQualifiedSymbol<C::StringTypes>,
        params: &mut dyn Iterator<Item = &BTreeSet<ValueType>>,
    ) -> Option<Result<BTreeSet<ValueType>, D>>;

    fn compile_function_from_macro(
        &mut self,
        name: &ValueQualifiedSymbol<C::StringTypes>,
        params: ValueList<C>,
    ) -> Option<Result<TryCompilationResult<C, D>, D>> {
        let mut compiled_params = Vec::new();
        for item in params.map(|v| self.compile(v)) {
            match item {
                Result::Ok(r) => compiled_params.push(r),
                Result::Err(e) => return Option::Some(Result::Err(e)),
            }
        }

        Option::Some(
            match self
                .compile_function(name, &mut (&compiled_params).into_iter().map(|p| &p.types))?
            {
                Result::Ok(r) => Result::Ok(TryCompilationResult::Compiled(CompilationResult {
                    result: Box::new(FunctionCallEvaluator::new(
                        ValueFunction(name.clone()),
                        compiled_params.into_iter().map(|p| p.result).collect(),
                    )),
                    types: r,
                })),
                Result::Err(e) => Result::Err(e),
            },
        )
    }

    fn evaluate_variable(&self, name: &ValueQualifiedSymbol<C::StringTypes>)
        -> Result<Value<D>, D>;

    fn evaluate_function(
        &mut self,
        name: &ValueQualifiedSymbol<C::StringTypes>,
        params: Vec<Value<D>>,
    ) -> Result<Value<D>, D>;

    fn compile_macro(
        &mut self,
        name: &ValueQualifiedSymbol<C::StringTypes>,
        params: ValueList<C>,
    ) -> Option<Result<TryCompilationResult<C, D>, D>>;

    fn compile(&mut self, v: Value<C>) -> Result<CompilationResult<C, D>, D> {
        let mut result = TryCompilationResult::<C, D>::Uncompiled(v);

        loop {
            match result {
                TryCompilationResult::Uncompiled(v) => {
                    result = match v {
                        Value::List(ValueList(Option::Some(l))) => {
                            let list = C::cons_ref_to_cons(&l);
                            let name = match &list.car {
                                Value::UnqualifiedSymbol(name) => {
                                    match self.resolve_symbol_get_macro(name) {
                                        Option::Some(name) => name,
                                        Option::None => {
                                            return Result::Err(e_undefined_function!(D))
                                        }
                                    }
                                }
                                Value::QualifiedSymbol(name) => (*name).clone(),
                                _ => return Result::Err(e_type_error!(D)),
                            };
                            match self.compile_macro(&name, list.cdr.clone()) {
                                Option::Some(r) => r?,
                                Option::None => return Result::Err(e_undefined_function!(D)),
                            }
                        }
                        Value::UnqualifiedSymbol(name) => {
                            match self.resolve_symbol_get_variable(&name) {
                                Option::Some(name) => match self.compile_variable(&name) {
                                    Option::Some(types) => {
                                        TryCompilationResult::Compiled(CompilationResult {
                                            result: Box::new(VariableEvaluator::new(name)),
                                            types,
                                        })
                                    }
                                    Option::None => return Result::Err(e_unbound_variable!(D)),
                                },
                                Option::None => return Result::Err(e_unbound_variable!(D)),
                            }
                        }
                        Value::QualifiedSymbol(name) => match self.compile_variable(&name) {
                            Option::Some(types) => {
                                TryCompilationResult::Compiled(CompilationResult {
                                    result: Box::new(VariableEvaluator::new(name)),
                                    types,
                                })
                            }
                            Option::None => return Result::Err(e_unbound_variable!(D)),
                        },
                        Value::Backquote(ValueBackquote(v)) => {
                            let v = C::value_ref_to_value(&v).clone();
                            TryCompilationResult::Compiled(compile_backquote(
                                self.as_dyn_mut(),
                                v,
                                BackquoteStatus::new(),
                            )?)
                        }
                        _ => {
                            let t = v.value_type();
                            TryCompilationResult::Compiled(CompilationResult {
                                result: Box::new(LiteralEvaluator::new(v)),
                                types: BTreeSet::from_iter(vec![t]),
                            })
                        }
                    }
                }
                TryCompilationResult::Compiled(r) => return Result::Ok(r),
            }
        }
    }
}

#[derive(Clone, Copy, Debug)]
struct BackquoteStatus {
    depth: u32,
    status: ListItem<()>,
}

impl BackquoteStatus {
    pub fn new() -> Self {
        Self {
            depth: 1,
            status: ListItem::List(()),
        }
    }

    pub fn backquote(&self) -> Self {
        Self {
            depth: self.depth + 1,
            status: ListItem::List(()),
        }
    }

    pub fn list_item(&self) -> Self {
        Self {
            depth: self.depth,
            status: ListItem::Item(()),
        }
    }

    pub fn comma(&self) -> Self {
        if self.depth == 0 {
            panic!("Unexpected comma");
        } else {
            Self {
                depth: self.depth - 1,
                status: ListItem::List(()),
            }
        }
    }

    pub fn splice(&self) -> Self {
        if self.depth == 0 || self.status != ListItem::Item(()) {
            panic!("Unexpected splice");
        } else {
            Self {
                depth: self.depth - 1,
                status: ListItem::List(()),
            }
        }
    }
}

fn backquote_comma_splice_push<C, D>(
    result: CompilationResult<C, D>,
    bq: BackquoteStatus,
    bcs: BackquoteCommaSplice,
) -> CompilationResult<C, D>
where
    C: ValueTypes + ?Sized + 'static,
    D: ValueTypesMut + ?Sized + 'static,
    D::StringTypes: StringTypesMut,
    D::SemverTypes: SemverTypesMut,
{
    if bq.depth > 0 {
        CompilationResult {
            result: Box::new(BackquoteCommaSplicePushEvaluator::new(bcs, result.result)),
            types: BTreeSet::from_iter(std::iter::once(match bcs {
                BackquoteCommaSplice::Backquote => ValueType::Backquote(result.types),
                BackquoteCommaSplice::Comma => ValueType::Comma(result.types),
                BackquoteCommaSplice::Splice => ValueType::Splice(result.types),
            })),
        }
    } else {
        result
    }
}

fn compile_backquote<C, D>(
    env: &mut dyn Environment<C, D>,
    v: Value<C>,
    bq: BackquoteStatus,
) -> Result<CompilationResult<C, D>, D>
where
    C: ValueTypes + ?Sized + 'static,
    D: ValueTypesMut + ?Sized + 'static,
    D::StringTypes: StringTypesMut,
    D::SemverTypes: SemverTypesMut,
{
    if bq.depth == 0 {
        env.compile(v)
    } else {
        Result::Ok(match v {
            Value::Backquote(ValueBackquote(v)) => {
                let v = C::value_ref_to_value(&v).clone();
                let bq = bq.backquote();
                backquote_comma_splice_push(
                    compile_backquote(env, v, bq)?,
                    bq,
                    BackquoteCommaSplice::Backquote,
                )
            }
            Value::Comma(ValueComma(v)) => {
                let v = C::value_ref_to_value(&v).clone();
                let bq = bq.comma();
                backquote_comma_splice_push(
                    compile_backquote(env, v, bq)?,
                    bq,
                    BackquoteCommaSplice::Comma,
                )
            }
            Value::Splice(ValueSplice(v)) => {
                let v = C::value_ref_to_value(&v).clone();
                let bq = bq.splice();
                backquote_comma_splice_push(
                    compile_backquote(env, v, bq)?,
                    bq,
                    BackquoteCommaSplice::Splice,
                )
            }
            Value::List(l) => {
                let bq = bq.list_item();
                let mut params = Vec::new();
                let mut types = BTreeSet::new();
                for item in l {
                    match item {
                        Value::Backquote(ValueBackquote(v)) => {
                            let v = C::value_ref_to_value(&v).clone();
                            let bq = bq.backquote();
                            let result = backquote_comma_splice_push(
                                compile_backquote(env, v, bq)?,
                                bq,
                                BackquoteCommaSplice::Backquote,
                            );
                            params.push(ListItem::Item(result.result));
                            types.extend(result.types);
                        }
                        Value::Comma(ValueComma(v)) => {
                            let v = C::value_ref_to_value(&v).clone();
                            let bq = bq.comma();
                            let result = backquote_comma_splice_push(
                                compile_backquote(env, v, bq)?,
                                bq,
                                BackquoteCommaSplice::Backquote,
                            );
                            params.push(ListItem::Item(result.result));
                            types.extend(result.types);
                        }
                        Value::Splice(ValueSplice(v)) => {
                            let v = C::value_ref_to_value(&v).clone();
                            let bq = bq.splice();
                            let result = backquote_comma_splice_push(
                                compile_backquote(env, v, bq)?,
                                bq,
                                BackquoteCommaSplice::Splice,
                            );
                            for t in result.types {
                                match t {
                                    ValueType::List(v) => types.extend(v),
                                    _ => return Result::Err(e_type_error!(D)),
                                }
                            }
                            params.push(ListItem::List(result.result));
                        }
                        _ => {
                            let result = compile_backquote(env, item, bq)?;
                            params.push(ListItem::Item(result.result));
                            types.extend(result.types);
                        }
                    }
                }
                CompilationResult {
                    result: Box::new(ConcatenateListsEvaluator::new(params)),
                    types: BTreeSet::from_iter(std::iter::once(ValueType::List(types))),
                }
            }
            _ => CompilationResult {
                result: Box::new(LiteralEvaluator::new(v.clone())),
                types: BTreeSet::from_iter(std::iter::once(v.value_type())),
            },
        })
    }
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum ValueType {
    List(BTreeSet<ValueType>),
    UnqualifiedSymbol,
    QualifiedSymbol,
    Bool,
    String,
    Semver,
    LanguageDirective,
    Function,
    Backquote(BTreeSet<ValueType>),
    Comma(BTreeSet<ValueType>),
    Splice(BTreeSet<ValueType>),
}

impl<T> Value<T>
where
    T: ValueTypes + ?Sized,
{
    pub fn value_type(&self) -> ValueType {
        match self {
            Value::List(l) => {
                ValueType::List(BTreeSet::from_iter(l.clone().map(|item| item.value_type())))
            }
            Value::UnqualifiedSymbol(_) => ValueType::UnqualifiedSymbol,
            Value::QualifiedSymbol(_) => ValueType::QualifiedSymbol,
            Value::Bool(_) => ValueType::Bool,
            Value::String(_) => ValueType::String,
            Value::Semver(_) => ValueType::Semver,
            Value::LanguageDirective(_) => ValueType::LanguageDirective,
            Value::Function(_) => ValueType::Function,
            Value::Backquote(b) => ValueType::Backquote(BTreeSet::from_iter(std::iter::once(
                T::value_ref_to_value(&b.0).value_type(),
            ))),
            Value::Comma(c) => ValueType::Comma(BTreeSet::from_iter(std::iter::once(
                T::value_ref_to_value(&c.0).value_type(),
            ))),
            Value::Splice(s) => ValueType::Splice(BTreeSet::from_iter(std::iter::once(
                T::value_ref_to_value(&s.0).value_type(),
            ))),
        }
    }
}

pub trait Evaluator<C, D>: Debug
where
    C: ValueTypes + ?Sized + 'static,
    D: ValueTypesMut + ?Sized + 'static,
    D::StringTypes: StringTypesMut,
    D::SemverTypes: SemverTypesMut,
{
    fn evaluate(&mut self, env: &mut dyn Environment<C, D>) -> Result<Value<D>, D>;
}

#[derive(Debug)]
pub struct LiteralEvaluator<L>(Value<L>)
where
    L: ValueTypes + ?Sized;

impl<L> LiteralEvaluator<L>
where
    L: ValueTypes + ?Sized,
{
    pub fn new(value: Value<L>) -> Self {
        Self(value)
    }
}

impl<L, C, D> Evaluator<C, D> for LiteralEvaluator<L>
where
    L: ValueTypes + ?Sized + 'static,
    C: ValueTypes + ?Sized + 'static,
    D: ValueTypesMut + ?Sized + 'static,
    D::StringTypes: StringTypesMut,
    D::SemverTypes: SemverTypesMut,
{
    fn evaluate(&mut self, _env: &mut dyn Environment<C, D>) -> Result<Value<D>, D> {
        Result::Ok(self.0.convert())
    }
}

#[derive(Debug)]
pub struct VariableEvaluator<S>(ValueQualifiedSymbol<S>)
where
    S: StringTypes + ?Sized + 'static;

impl<S> VariableEvaluator<S>
where
    S: StringTypes + ?Sized,
{
    pub fn new(name: ValueQualifiedSymbol<S>) -> Self {
        Self(name)
    }
}

impl<C, D> Evaluator<C, D> for VariableEvaluator<C::StringTypes>
where
    C: ValueTypes + ?Sized + 'static,
    D: ValueTypesMut + ?Sized + 'static,
    D::StringTypes: StringTypesMut,
    D::SemverTypes: SemverTypesMut,
{
    fn evaluate(&mut self, env: &mut dyn Environment<C, D>) -> Result<Value<D>, D> {
        env.evaluate_variable(&self.0)
    }
}

#[derive(Debug)]
pub struct FunctionCallEvaluator<C, D>
where
    C: ValueTypes + ?Sized + 'static,
    D: ValueTypesMut + ?Sized + 'static,
    D::StringTypes: StringTypesMut,
    D::SemverTypes: SemverTypesMut,
{
    name: ValueFunction<C::StringTypes>,
    params: Vec<Box<dyn Evaluator<C, D>>>,
}

impl<C, D> FunctionCallEvaluator<C, D>
where
    C: ValueTypes + ?Sized + 'static,
    D: ValueTypesMut + ?Sized + 'static,
    D::StringTypes: StringTypesMut,
    D::SemverTypes: SemverTypesMut,
{
    pub fn new(name: ValueFunction<C::StringTypes>, params: Vec<Box<dyn Evaluator<C, D>>>) -> Self {
        Self { name, params }
    }
}

impl<C, D> Evaluator<C, D> for FunctionCallEvaluator<C, D>
where
    C: ValueTypes + ?Sized + 'static,
    D: ValueTypesMut + ?Sized + 'static,
    D::StringTypes: StringTypesMut,
    D::SemverTypes: SemverTypesMut,
{
    fn evaluate(&mut self, env: &mut dyn Environment<C, D>) -> Result<Value<D>, D> {
        use std::borrow::BorrowMut;

        let params = (&mut self.params)
            .into_iter()
            .map(|p| BorrowMut::<dyn Evaluator<C, D>>::borrow_mut(p).evaluate(env))
            .collect::<Result<Vec<Value<D>>, D>>()?;
        env.evaluate_function(&self.name.0, params)
    }
}

#[derive(Debug)]
pub struct ConcatenateListsEvaluator<C, D>(Vec<ListItem<Box<dyn Evaluator<C, D>>>>)
where
    C: ValueTypes + ?Sized,
    D: ValueTypesMut + ?Sized,
    D::StringTypes: StringTypesMut,
    D::SemverTypes: SemverTypesMut;

impl<C, D> ConcatenateListsEvaluator<C, D>
where
    C: ValueTypes + ?Sized,
    D: ValueTypesMut + ?Sized,
    D::StringTypes: StringTypesMut,
    D::SemverTypes: SemverTypesMut,
{
    pub fn new(items: Vec<ListItem<Box<dyn Evaluator<C, D>>>>) -> Self {
        Self(items)
    }
}

impl<C, D> Evaluator<C, D> for ConcatenateListsEvaluator<C, D>
where
    C: ValueTypes + ?Sized + 'static,
    D: ValueTypesMut + ?Sized + 'static,
    D::StringTypes: StringTypesMut,
    D::SemverTypes: SemverTypesMut,
{
    fn evaluate(&mut self, env: &mut dyn Environment<C, D>) -> Result<Value<D>, D> {
        let mut items = Vec::new();
        for item in &mut self.0 {
            items.push(item.as_mut().map(|comp| comp.evaluate(env)).transpose()?);
        }
        Result::Ok(Value::List(concat_lists(items.into_iter())?))
    }
}

#[derive(Clone, Copy, Debug)]
pub enum BackquoteCommaSplice {
    Backquote,
    Comma,
    Splice,
}

#[derive(Debug)]
pub struct BackquoteCommaSplicePushEvaluator<C, D>
where
    C: ValueTypes + ?Sized,
    D: ValueTypesMut + ?Sized,
    D::StringTypes: StringTypesMut,
    D::SemverTypes: SemverTypesMut,
{
    push: BackquoteCommaSplice,
    wrapped: Box<dyn Evaluator<C, D>>,
}

impl<C, D> BackquoteCommaSplicePushEvaluator<C, D>
where
    C: ValueTypes + ?Sized,
    D: ValueTypesMut + ?Sized,
    D::StringTypes: StringTypesMut,
    D::SemverTypes: SemverTypesMut,
{
    pub fn new(push: BackquoteCommaSplice, wrapped: Box<dyn Evaluator<C, D>>) -> Self {
        Self { push, wrapped }
    }
}

impl<C, D> Evaluator<C, D> for BackquoteCommaSplicePushEvaluator<C, D>
where
    C: ValueTypes + ?Sized + 'static,
    D: ValueTypesMut + ?Sized + 'static,
    D::StringTypes: StringTypesMut,
    D::SemverTypes: SemverTypesMut,
{
    fn evaluate(&mut self, env: &mut dyn Environment<C, D>) -> Result<Value<D>, D> {
        let result = D::value_ref_from_value(self.wrapped.evaluate(env)?);
        Result::Ok(match self.push {
            BackquoteCommaSplice::Backquote => Value::Backquote(ValueBackquote(result)),
            BackquoteCommaSplice::Comma => Value::Comma(ValueComma(result)),
            BackquoteCommaSplice::Splice => Value::Splice(ValueSplice(result)),
        })
    }
}

#[derive(Debug)]
pub struct CompilationResult<C, D>
where
    C: ValueTypes + ?Sized,
    D: ValueTypesMut + ?Sized,
    D::StringTypes: StringTypesMut,
    D::SemverTypes: SemverTypesMut,
{
    pub result: Box<dyn Evaluator<C, D> + 'static>,
    pub types: BTreeSet<ValueType>,
}

pub enum TryCompilationResult<C, D>
where
    C: ValueTypes + ?Sized,
    D: ValueTypesMut + ?Sized,
    D::StringTypes: StringTypesMut,
    D::SemverTypes: SemverTypesMut,
{
    Compiled(CompilationResult<C, D>),
    Uncompiled(Value<C>),
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::cell::RefCell;
    use std::collections::HashSet;
    use std::rc::Rc;

    #[derive(Debug)]
    struct SideEffectEvaluator<C, D>
    where
        C: ValueTypes + ?Sized,
        D: ValueTypesMut + ?Sized,
        D::StringTypes: StringTypesMut,
        D::SemverTypes: SemverTypesMut,
    {
        eval_side_effects: Rc<RefCell<HashSet<String>>>,
        name: String,
        value: Box<dyn Evaluator<C, D>>,
    }

    impl<C, D> SideEffectEvaluator<C, D>
    where
        C: ValueTypes + ?Sized,
        D: ValueTypesMut + ?Sized,
        D::StringTypes: StringTypesMut,
        D::SemverTypes: SemverTypesMut,
    {
        pub fn new(
            eval_side_effects: Rc<RefCell<HashSet<String>>>,
            name: String,
            value: Box<dyn Evaluator<C, D>>,
        ) -> Self {
            Self {
                eval_side_effects,
                name,
                value,
            }
        }
    }

    impl<C, D> Evaluator<C, D> for SideEffectEvaluator<C, D>
    where
        C: ValueTypes + ?Sized + 'static,
        D: ValueTypesMut + ?Sized + 'static,
        D::StringTypes: StringTypesMut,
        D::SemverTypes: SemverTypesMut,
    {
        fn evaluate(&mut self, env: &mut dyn Environment<C, D>) -> Result<Value<D>, D> {
            self.eval_side_effects
                .borrow_mut()
                .insert(self.name.clone());
            self.value.evaluate(env)
        }
    }

    struct SideEffectEnvironment {
        comp_side_effects: Rc<RefCell<HashSet<String>>>,
        eval_side_effects: Rc<RefCell<HashSet<String>>>,
    }

    impl SideEffectEnvironment {
        pub fn new() -> Self {
            Self {
                comp_side_effects: Rc::new(RefCell::new(HashSet::new())),
                eval_side_effects: Rc::new(RefCell::new(HashSet::new())),
            }
        }

        fn compile_side_effect<C, D>(
            &mut self,
            mut params: ValueList<C>,
        ) -> Result<CompilationResult<C, D>, D>
        where
            C: ValueTypes + ?Sized + 'static,
            D: ValueTypesMut + ?Sized + 'static,
            D::StringTypes: StringTypesMut,
            D::SemverTypes: SemverTypesMut,
        {
            use std::convert::TryInto;

            let side_effect: ValueString<C::StringTypes> = match params.next() {
                Option::Some(s) => s,
                Option::None => return Result::Err(e_program_error!(D)),
            }
            .try_into()?;
            let side_effect_name = C::StringTypes::string_ref_to_str(&side_effect.0);

            let value = self.compile(match params.next() {
                Option::Some(v) => v,
                Option::None => return Result::Err(e_program_error!(D)),
            })?;

            let retval = match params.next() {
                Option::Some(_) => return Result::Err(e_program_error!(D)),
                Option::None => CompilationResult {
                    result: Box::new(SideEffectEvaluator::new(
                        self.eval_side_effects.clone(),
                        side_effect_name.to_string(),
                        value.result,
                    )),
                    types: value.types,
                },
            };

            self.comp_side_effects
                .borrow_mut()
                .insert(side_effect_name.to_string());

            Result::Ok(retval)
        }
    }

    impl<C, D> Environment<C, D> for SideEffectEnvironment
    where
        C: ValueTypes + ?Sized + 'static,
        D: ValueTypesMut + ?Sized + 'static,
        D::StringTypes: StringTypesMut,
        D::SemverTypes: SemverTypesMut,
    {
        fn as_dyn_mut(&mut self) -> &mut (dyn Environment<C, D> + 'static) {
            self
        }

        fn resolve_symbol_get_variable(
            &self,
            _name: &ValueUnqualifiedSymbol<C::StringTypes>,
        ) -> Option<ValueQualifiedSymbol<C::StringTypes>> {
            Option::None
        }

        fn compile_variable(
            &self,
            _name: &ValueQualifiedSymbol<C::StringTypes>,
        ) -> Option<BTreeSet<ValueType>> {
            Option::None
        }

        fn resolve_symbol_get_macro(
            &self,
            name: &ValueUnqualifiedSymbol<C::StringTypes>,
        ) -> Option<ValueQualifiedSymbol<C::StringTypes>> {
            match C::StringTypes::string_ref_to_str(&name.0) {
                "side-effect" => Option::Some(ValueQualifiedSymbol::<C::StringTypes> {
                    package: C::StringTypes::string_ref_from_static_str("test"),
                    name: name.0.clone(),
                }),
                _ => Option::None,
            }
        }

        fn compile_function(
            &self,
            _name: &ValueQualifiedSymbol<C::StringTypes>,
            _params: &mut dyn Iterator<Item = &BTreeSet<ValueType>>,
        ) -> Option<Result<BTreeSet<ValueType>, D>> {
            Option::None
        }

        fn evaluate_variable(
            &self,
            _name: &ValueQualifiedSymbol<C::StringTypes>,
        ) -> Result<Value<D>, D> {
            Result::Err(e_unbound_variable!(D))
        }

        fn evaluate_function(
            &mut self,
            _name: &ValueQualifiedSymbol<C::StringTypes>,
            _params: Vec<Value<D>>,
        ) -> Result<Value<D>, D> {
            Result::Err(e_undefined_function!(D))
        }

        fn compile_macro(
            &mut self,
            name: &ValueQualifiedSymbol<C::StringTypes>,
            params: ValueList<C>,
        ) -> Option<Result<TryCompilationResult<C, D>, D>> {
            match (
                C::StringTypes::string_ref_to_str(&name.package),
                C::StringTypes::string_ref_to_str(&name.name),
            ) {
                ("test", "side-effect") => Option::Some(match self.compile_side_effect(params) {
                    Result::Ok(r) => Result::Ok(TryCompilationResult::Compiled(r)),
                    Result::Err(e) => Result::Err(e),
                }),
                _ => Option::None,
            }
        }
    }

    #[test]
    fn test_value_type() {
        assert_eq!(
            v_list!(
                v_bool!(true),
                v_str!("str"),
                v_list!(v_uqsym!("uqsym"), v_bool!(true), v_qsym!("p", "qsym"))
            )
            .value_type(),
            ValueType::List(BTreeSet::from_iter(vec![
                ValueType::Bool,
                ValueType::String,
                ValueType::List(BTreeSet::from_iter(vec![
                    ValueType::UnqualifiedSymbol,
                    ValueType::QualifiedSymbol,
                    ValueType::Bool,
                ])),
            ]),)
        );
        assert_eq!(v_uqsym!("uqsym").value_type(), ValueType::UnqualifiedSymbol);
        assert_eq!(
            v_qsym!("p", "qsym").value_type(),
            ValueType::QualifiedSymbol
        );
        assert_eq!(v_bool!(true).value_type(), ValueType::Bool);
        assert_eq!(v_str!("str").value_type(), ValueType::String);
        assert_eq!(v_v![1, 0].value_type(), ValueType::Semver);
        assert_eq!(
            v_lang_kira![1, 0].value_type(),
            ValueType::LanguageDirective
        );
        assert_eq!(v_func!(qsym!("p", "f1")).value_type(), ValueType::Function);
        assert_eq!(
            v_bq!(v_qsym!("p", "f1")).value_type(),
            ValueType::Backquote(BTreeSet::from_iter(std::iter::once(
                ValueType::QualifiedSymbol
            )))
        );
        assert_eq!(
            v_comma!(v_qsym!("p", "f1")).value_type(),
            ValueType::Comma(BTreeSet::from_iter(std::iter::once(
                ValueType::QualifiedSymbol
            )))
        );
        assert_eq!(
            v_splice!(v_qsym!("p", "f1")).value_type(),
            ValueType::Splice(BTreeSet::from_iter(std::iter::once(
                ValueType::QualifiedSymbol
            )))
        );
    }

    struct SimpleEnvironment;

    fn simplemacro1<C, D>() -> Result<TryCompilationResult<C, D>, D>
    where
        C: ValueTypes + ?Sized + 'static,
        D: ValueTypesMut + ?Sized + 'static,
        D::StringTypes: StringTypesMut,
        D::SemverTypes: SemverTypesMut,
    {
        Result::Ok(TryCompilationResult::Compiled(CompilationResult {
            result: Box::new(LiteralEvaluator::new(v_str!("Hello world!"))),
            types: BTreeSet::from_iter(vec![ValueType::String]),
        }))
    }

    fn simplemacro2<C, D>() -> Result<TryCompilationResult<C, D>, D>
    where
        C: ValueTypes + ?Sized + 'static,
        D: ValueTypesMut + ?Sized + 'static,
        D::StringTypes: StringTypesMut,
        D::SemverTypes: SemverTypesMut,
    {
        Result::Ok(TryCompilationResult::Compiled(CompilationResult {
            result: Box::new(LiteralEvaluator::new(v_bool!(true))),
            types: BTreeSet::from_iter(vec![ValueType::Bool]),
        }))
    }

    fn compile_simplefunc1<D>(
        params: &mut dyn Iterator<Item = &BTreeSet<ValueType>>,
    ) -> Result<BTreeSet<ValueType>, D>
    where
        D: ValueTypes + ?Sized,
    {
        let result = match params.next() {
            Option::Some(p) => (*p).clone(),
            Option::None => return Result::Err(e_program_error!(D)),
        };

        match params.next() {
            Option::None => Result::Ok(result),
            Option::Some(_) => Result::Err(e_program_error!(D)),
        }
    }

    fn simplefunc1<C, D>(
        _env: &mut dyn Environment<C, D>,
        params: Vec<Value<D>>,
    ) -> Result<Value<D>, D>
    where
        C: ValueTypes + ?Sized,
        D: ValueTypesMut + ?Sized,
        D::StringTypes: StringTypesMut,
        D::SemverTypes: SemverTypesMut,
    {
        let mut params = params.into_iter();
        let result = match params.next() {
            Option::Some(p) => p,
            Option::None => return Result::Err(e_program_error!(D)),
        };

        match params.next() {
            Option::None => Result::Ok(result),
            Option::Some(_) => Result::Err(e_program_error!(D)),
        }
    }

    fn simplefunc2<C, D>(
        _env: &mut dyn Environment<C, D>,
        _params: Vec<Value<D>>,
    ) -> Result<Value<D>, D>
    where
        C: ValueTypes + ?Sized,
        D: ValueTypesMut + ?Sized,
        D::StringTypes: StringTypesMut,
        D::SemverTypes: SemverTypesMut,
    {
        Result::Ok(v_qsym!("pvar", "var3").convert())
    }

    impl<C, D> Environment<C, D> for SimpleEnvironment
    where
        C: ValueTypes + ?Sized + 'static,
        D: ValueTypesMut + ?Sized + 'static,
        D::StringTypes: StringTypesMut,
        D::SemverTypes: SemverTypesMut,
    {
        fn as_dyn_mut(&mut self) -> &mut (dyn Environment<C, D> + 'static) {
            self as &mut (dyn Environment<C, D> + 'static)
        }

        fn resolve_symbol_get_variable(
            &self,
            name: &ValueUnqualifiedSymbol<C::StringTypes>,
        ) -> Option<ValueQualifiedSymbol<C::StringTypes>> {
            Option::Some(ValueQualifiedSymbol {
                package: C::StringTypes::string_ref_from_static_str("pvar"),
                name: name.0.clone(),
            })
        }

        fn compile_variable(
            &self,
            name: &ValueQualifiedSymbol<C::StringTypes>,
        ) -> Option<BTreeSet<ValueType>> {
            match (
                C::StringTypes::string_ref_to_str(&name.package),
                C::StringTypes::string_ref_to_str(&name.name),
            ) {
                ("pvar", "var1") => Option::Some(BTreeSet::from_iter(vec![ValueType::String])),
                ("pvar", "var2") => Option::Some(BTreeSet::from_iter(vec![ValueType::Bool])),
                ("pvar", "var3") => {
                    Option::Some(BTreeSet::from_iter(vec![ValueType::QualifiedSymbol]))
                }
                ("pvar", "var4") => {
                    Option::Some(BTreeSet::from_iter(vec![ValueType::UnqualifiedSymbol]))
                }
                ("pvar", "var5") => Option::Some(BTreeSet::from_iter(vec![ValueType::List(
                    BTreeSet::from_iter(vec![ValueType::QualifiedSymbol]),
                )])),
                _ => Option::None,
            }
        }

        fn evaluate_variable(
            &self,
            name: &ValueQualifiedSymbol<C::StringTypes>,
        ) -> Result<Value<D>, D> {
            match (
                C::StringTypes::string_ref_to_str(&name.package),
                C::StringTypes::string_ref_to_str(&name.name),
            ) {
                ("pvar", "var1") => Result::Ok(v_str!("str").convert()),
                ("pvar", "var2") => Result::Ok(v_bool!(true).convert()),
                ("pvar", "var3") => Result::Ok(v_qsym!("pvar", "var4").convert()),
                ("pvar", "var4") => Result::Ok(v_uqsym!("var5").convert()),
                ("pvar", "var5") => Result::Ok(v_list!(v_qsym!("p", "simplefunc2")).convert()),
                _ => Result::Err(e_unbound_variable!(D)),
            }
        }

        fn evaluate_function(
            &mut self,
            name: &ValueQualifiedSymbol<C::StringTypes>,
            params: Vec<Value<D>>,
        ) -> Result<Value<D>, D> {
            match (
                C::StringTypes::string_ref_to_str(&name.package),
                C::StringTypes::string_ref_to_str(&name.name),
            ) {
                ("p", "simplefunc1") => simplefunc1::<C, D>(self, params),
                ("p", "simplefunc2") => simplefunc2::<C, D>(self, params),
                _ => Result::Err(e_undefined_function!(D)),
            }
        }

        fn resolve_symbol_get_macro(
            &self,
            name: &ValueUnqualifiedSymbol<C::StringTypes>,
        ) -> Option<ValueQualifiedSymbol<C::StringTypes>> {
            Option::Some(ValueQualifiedSymbol {
                package: C::StringTypes::string_ref_from_static_str("p"),
                name: name.0.clone(),
            })
        }

        fn compile_macro(
            &mut self,
            name: &ValueQualifiedSymbol<C::StringTypes>,
            params: ValueList<C>,
        ) -> Option<Result<TryCompilationResult<C, D>, D>> {
            match (
                C::StringTypes::string_ref_to_str(&name.package),
                C::StringTypes::string_ref_to_str(&name.name),
            ) {
                ("p", "simplemacro1") => Option::Some(simplemacro1()),
                ("p", "simplemacro2") => Option::Some(simplemacro2()),
                ("p", "simplefunc1") => self.compile_function_from_macro(name, params),
                _ => Option::None,
            }
        }

        fn compile_function(
            &self,
            name: &ValueQualifiedSymbol<C::StringTypes>,
            params: &mut dyn Iterator<Item = &BTreeSet<ValueType>>,
        ) -> Option<Result<BTreeSet<ValueType>, D>> {
            match (
                C::StringTypes::string_ref_to_str(&name.package),
                C::StringTypes::string_ref_to_str(&name.name),
            ) {
                ("p", "simplefunc1") => Option::Some(compile_simplefunc1(params)),
                _ => Option::None,
            }
        }
    }

    fn test_compile_and_evaluate(
        env: &mut dyn Environment<ValueTypesStatic, ValueTypesRc>,
        code: Value<ValueTypesStatic>,
        result: Value<ValueTypesStatic>,
        types: BTreeSet<ValueType>,
    ) {
        let mut comp = env.compile(code).unwrap();
        assert_eq!(comp.types, types);
        assert_eq!(comp.result.evaluate(env).unwrap(), result);
    }

    #[test]
    fn test_evaluate_literal() {
        let mut env = SimpleEnvironment;
        let env = &mut env as &mut dyn Environment<ValueTypesStatic, ValueTypesRc>;

        let mut comp = LiteralEvaluator::new(v_str!("Hello world!"));
        assert_eq!(comp.evaluate(env).unwrap(), v_str!("Hello world!"));

        let mut comp = LiteralEvaluator::new(v_bool!(true));
        assert_eq!(comp.evaluate(env).unwrap(), v_bool!(true));
    }

    #[test]
    fn test_evaluate_variable() {
        let mut env = SimpleEnvironment;
        let env = &mut env as &mut dyn Environment<ValueTypesStatic, ValueTypesRc>;

        let mut comp = VariableEvaluator::new(qsym!("pvar", "var1"));
        assert_eq!(comp.evaluate(env).unwrap(), v_str!("str"));

        let mut comp = VariableEvaluator::new(qsym!("pvar", "var2"));
        assert_eq!(comp.evaluate(env).unwrap(), v_bool!(true));

        let mut comp = VariableEvaluator::new(qsym!("pvar", "undef"));
        assert_eq!(
            comp.evaluate(env).unwrap_err(),
            e_unbound_variable!(ValueTypesRc)
        );
    }

    #[test]
    fn test_evaluate_function() {
        let mut env = SimpleEnvironment;
        let env = &mut env as &mut dyn Environment<ValueTypesStatic, ValueTypesRc>;

        let mut comp = FunctionCallEvaluator::new(
            func!(qsym!("p", "simplefunc1")),
            vec![Box::new(LiteralEvaluator::new(v_str!("Hello world!")))],
        );
        assert_eq!(comp.evaluate(env).unwrap(), v_str!("Hello world!"));

        let mut comp = FunctionCallEvaluator::new(
            func!(qsym!("p", "simplefunc1")),
            vec![Box::new(LiteralEvaluator::new(v_bool!(true)))],
        );
        assert_eq!(comp.evaluate(env).unwrap(), v_bool!(true));
    }

    #[test]
    fn test_evaluate_concatenate_lists() {
        let mut env = SimpleEnvironment;
        let env = &mut env as &mut dyn Environment<ValueTypesStatic, ValueTypesRc>;

        let mut comp = ConcatenateListsEvaluator::new(vec![
            ListItem::List(Box::new(LiteralEvaluator::new(v_list!(v_str!("str"))))),
            ListItem::List(Box::new(LiteralEvaluator::new(v_list!(v_bool!(true))))),
        ]);
        assert_eq!(
            comp.evaluate(env).unwrap(),
            v_list!(v_str!("str"), v_bool!(true))
        );

        let mut comp = ConcatenateListsEvaluator::new(vec![ListItem::List(Box::new(
            LiteralEvaluator::new(v_bool!(true)),
        ))]);
        assert_eq!(comp.evaluate(env).unwrap_err(), e_type_error!(ValueTypesRc));
    }

    #[test]
    fn test_evaluate_backquote_comma_splice_push() {
        let mut env = SimpleEnvironment;
        let env = &mut env as &mut dyn Environment<ValueTypesStatic, ValueTypesRc>;

        let mut comp = BackquoteCommaSplicePushEvaluator::new(
            BackquoteCommaSplice::Backquote,
            Box::new(LiteralEvaluator::new(v_bool!(true))),
        );
        assert_eq!(comp.evaluate(env).unwrap(), v_bq!(v_bool!(true)));

        let mut comp = BackquoteCommaSplicePushEvaluator::new(
            BackquoteCommaSplice::Comma,
            Box::new(LiteralEvaluator::new(v_bool!(true))),
        );
        assert_eq!(comp.evaluate(env).unwrap(), v_comma!(v_bool!(true)));

        let mut comp = BackquoteCommaSplicePushEvaluator::new(
            BackquoteCommaSplice::Splice,
            Box::new(LiteralEvaluator::new(v_bool!(true))),
        );
        assert_eq!(comp.evaluate(env).unwrap(), v_splice!(v_bool!(true)));
    }

    #[test]
    fn test_compile_and_evaluate_literal() {
        let mut env = SimpleEnvironment;
        let env = &mut env as &mut dyn Environment<ValueTypesStatic, ValueTypesRc>;

        test_compile_and_evaluate(
            env,
            v_list!(),
            v_list!(),
            BTreeSet::from_iter(vec![ValueType::List(BTreeSet::new())]),
        );
        test_compile_and_evaluate(
            env,
            v_bool!(true),
            v_bool!(true),
            BTreeSet::from_iter(vec![ValueType::Bool]),
        );
        test_compile_and_evaluate(
            env,
            v_str!("Hello world!"),
            v_str!("Hello world!"),
            BTreeSet::from_iter(vec![ValueType::String]),
        );
        test_compile_and_evaluate(
            env,
            v_v![1, 0],
            v_v![1, 0],
            BTreeSet::from_iter(vec![ValueType::Semver]),
        );
    }

    #[test]
    fn test_compile_and_evaluate_variable() {
        let mut env = SimpleEnvironment;
        let env = &mut env as &mut dyn Environment<ValueTypesStatic, ValueTypesRc>;

        test_compile_and_evaluate(
            env,
            v_uqsym!("var1"),
            v_str!("str"),
            BTreeSet::from_iter(vec![ValueType::String]),
        );
        test_compile_and_evaluate(
            env,
            v_uqsym!("var2"),
            v_bool!(true),
            BTreeSet::from_iter(vec![ValueType::Bool]),
        );
        assert_eq!(
            env.compile(v_uqsym!("undef")).unwrap_err(),
            e_unbound_variable!(ValueTypesRc)
        );

        test_compile_and_evaluate(
            env,
            v_qsym!("pvar", "var1"),
            v_str!("str"),
            BTreeSet::from_iter(vec![ValueType::String]),
        );
        test_compile_and_evaluate(
            env,
            v_qsym!("pvar", "var2"),
            v_bool!(true),
            BTreeSet::from_iter(vec![ValueType::Bool]),
        );
        assert_eq!(
            env.compile(v_qsym!("pvar", "undef")).unwrap_err(),
            e_unbound_variable!(ValueTypesRc)
        );
    }

    #[test]
    fn test_compile_and_evaluate_macro() {
        let mut env = SimpleEnvironment;
        let env = &mut env as &mut dyn Environment<ValueTypesStatic, ValueTypesRc>;

        test_compile_and_evaluate(
            env,
            v_list!(v_uqsym!("simplemacro1")),
            v_str!("Hello world!"),
            BTreeSet::from_iter(vec![ValueType::String]),
        );
        test_compile_and_evaluate(
            env,
            v_list!(v_uqsym!("simplemacro2")),
            v_bool!(true),
            BTreeSet::from_iter(vec![ValueType::Bool]),
        );
        assert_eq!(
            env.compile(v_list!(v_uqsym!("simplemacro3"))).unwrap_err(),
            e_undefined_function!(ValueTypesRc)
        );

        test_compile_and_evaluate(
            env,
            v_list!(v_qsym!("p", "simplemacro1")),
            v_str!("Hello world!"),
            BTreeSet::from_iter(vec![ValueType::String]),
        );
        test_compile_and_evaluate(
            env,
            v_list!(v_qsym!("p", "simplemacro2")),
            v_bool!(true),
            BTreeSet::from_iter(vec![ValueType::Bool]),
        );
        assert_eq!(
            env.compile(v_list!(v_qsym!("p", "simplemacro3")))
                .unwrap_err(),
            e_undefined_function!(ValueTypesRc)
        );
    }

    #[test]
    fn test_compile_and_evaluate_function() {
        let mut env = SimpleEnvironment;
        let env = &mut env as &mut dyn Environment<ValueTypesStatic, ValueTypesRc>;

        test_compile_and_evaluate(
            env,
            v_list!(v_uqsym!("simplefunc1"), v_str!("Hello world!")),
            v_str!("Hello world!"),
            BTreeSet::from_iter(vec![ValueType::String]),
        );
        test_compile_and_evaluate(
            env,
            v_list!(v_uqsym!("simplefunc1"), v_bool!(true)),
            v_bool!(true),
            BTreeSet::from_iter(vec![ValueType::Bool]),
        );
        assert_eq!(
            env.compile(v_list!(v_uqsym!("simplefunc1"))).unwrap_err(),
            e_program_error!(ValueTypesRc)
        );

        test_compile_and_evaluate(
            env,
            v_list!(v_qsym!("p", "simplefunc1"), v_str!("Hello world!")),
            v_str!("Hello world!"),
            BTreeSet::from_iter(vec![ValueType::String]),
        );
        test_compile_and_evaluate(
            env,
            v_list!(v_qsym!("p", "simplefunc1"), v_bool!(true)),
            v_bool!(true),
            BTreeSet::from_iter(vec![ValueType::Bool]),
        );
        assert_eq!(
            env.compile(v_list!(v_qsym!("p", "simplefunc1")))
                .unwrap_err(),
            e_program_error!(ValueTypesRc)
        );
    }

    #[test]
    fn test_compile_and_evaluate_backquote() {
        let mut env = SimpleEnvironment;
        let env = &mut env as &mut dyn Environment<ValueTypesStatic, ValueTypesRc>;

        test_compile_and_evaluate(
            env,
            v_bq!(v_uqsym!("a")),
            v_uqsym!("a"),
            BTreeSet::from_iter(std::iter::once(ValueType::UnqualifiedSymbol)),
        );
        test_compile_and_evaluate(
            env,
            v_bq!(v_comma!(v_qsym!("pvar", "var3"))),
            v_qsym!("pvar", "var4"),
            BTreeSet::from_iter(std::iter::once(ValueType::QualifiedSymbol)),
        );
        test_compile_and_evaluate(
            env,
            v_bq!(v_bq!(v_comma!(v_qsym!("pvar", "var3")))),
            v_bq!(v_comma!(v_qsym!("pvar", "var3"))),
            BTreeSet::from_iter(std::iter::once(ValueType::Backquote(BTreeSet::from_iter(
                std::iter::once(ValueType::Comma(BTreeSet::from_iter(std::iter::once(
                    ValueType::QualifiedSymbol,
                )))),
            )))),
        );
        test_compile_and_evaluate(
            env,
            v_bq!(v_list!(v_splice!(v_qsym!("pvar", "var5")))),
            v_list!(v_qsym!("p", "simplefunc2")),
            BTreeSet::from_iter(std::iter::once(ValueType::List(BTreeSet::from_iter(
                std::iter::once(ValueType::QualifiedSymbol),
            )))),
        );
        assert_eq!(
            env.compile(v_bq!(v_list!(v_splice!(v_qsym!("pvar", "var4")))))
                .unwrap_err(),
            e_type_error!(ValueTypesRc)
        );
        test_compile_and_evaluate(
            env,
            v_bq!(v_list!(v_bq!(v_qsym!("pvar", "var5")))),
            v_list!(v_bq!(v_qsym!("pvar", "var5"))),
            BTreeSet::from_iter(std::iter::once(ValueType::List(BTreeSet::from_iter(
                std::iter::once(ValueType::Backquote(BTreeSet::from_iter(std::iter::once(
                    ValueType::QualifiedSymbol,
                )))),
            )))),
        );
        test_compile_and_evaluate(
            env,
            v_bq!(v_list!(v_comma!(v_qsym!("pvar", "var5")))),
            v_list!(v_list!(v_qsym!("p", "simplefunc2"))),
            BTreeSet::from_iter(std::iter::once(ValueType::List(BTreeSet::from_iter(
                std::iter::once(ValueType::List(BTreeSet::from_iter(std::iter::once(
                    ValueType::QualifiedSymbol,
                )))),
            )))),
        );
        test_compile_and_evaluate(
            env,
            v_bq!(v_list!(v_qsym!("pvar", "var5"))),
            v_list!(v_qsym!("pvar", "var5")),
            BTreeSet::from_iter(std::iter::once(ValueType::List(BTreeSet::from_iter(
                std::iter::once(ValueType::QualifiedSymbol),
            )))),
        );
        test_compile_and_evaluate(
            env,
            v_bq!(v_list!(v_list!(v_splice!(v_qsym!("pvar", "var5"))))),
            v_list!(v_list!(v_qsym!("p", "simplefunc2"))),
            BTreeSet::from_iter(std::iter::once(ValueType::List(BTreeSet::from_iter(
                std::iter::once(ValueType::List(BTreeSet::from_iter(std::iter::once(
                    ValueType::QualifiedSymbol,
                )))),
            )))),
        );
    }

    #[test]
    #[should_panic]
    fn test_compile_and_evaluate_backquote_bad_splice_backquote() {
        let mut env = SimpleEnvironment;
        let env = &mut env as &mut dyn Environment<ValueTypesStatic, ValueTypesRc>;

        test_compile_and_evaluate(
            env,
            v_bq!(v_splice!(v_uqsym!("a"))),
            v_list!(),       // Doesn't matter
            BTreeSet::new(), // Doesn't matter
        );
    }

    #[test]
    #[should_panic]
    fn test_compile_and_evaluate_backquote_bad_splice_comma() {
        let mut env = SimpleEnvironment;
        let env = &mut env as &mut dyn Environment<ValueTypesStatic, ValueTypesRc>;

        test_compile_and_evaluate(
            env,
            v_bq!(v_bq!(v_comma!(v_splice!(v_uqsym!("a"))))),
            v_list!(),       // Doesn't matter
            BTreeSet::new(), // Doesn't matter
        );
    }

    #[test]
    #[should_panic]
    fn test_compile_and_evaluate_backquote_bad_splice_backquote_nested() {
        let mut env = SimpleEnvironment;
        let env = &mut env as &mut dyn Environment<ValueTypesStatic, ValueTypesRc>;

        test_compile_and_evaluate(
            env,
            v_bq!(v_list!(v_bq!(v_splice!(v_uqsym!("a"))))),
            v_list!(),       // Doesn't matter
            BTreeSet::new(), // Doesn't matter
        );
    }

    #[test]
    fn test_side_effect_environment() {
        let mut env = SideEffectEnvironment::new();
        assert_eq!(*env.comp_side_effects.borrow(), HashSet::new());
        assert_eq!(*env.eval_side_effects.borrow(), HashSet::new());

        let mut comp: CompilationResult<_, ValueTypesRc> = env
            .compile(v_list!(v_uqsym!("side-effect"), v_str!("a"), v_bool!(true)))
            .unwrap();
        assert_eq!(
            comp.types,
            BTreeSet::from_iter(std::iter::once(ValueType::Bool))
        );
        assert_eq!(
            *env.comp_side_effects.borrow(),
            HashSet::from_iter(std::iter::once("a".to_string()))
        );
        assert_eq!(*env.eval_side_effects.borrow(), HashSet::new());

        assert_eq!(comp.result.evaluate(&mut env).unwrap(), v_bool!(true));
        assert_eq!(
            *env.comp_side_effects.borrow(),
            HashSet::from_iter(std::iter::once("a".to_string()))
        );
        assert_eq!(
            *env.eval_side_effects.borrow(),
            HashSet::from_iter(std::iter::once("a".to_string()))
        );

        let mut comp: CompilationResult<_, ValueTypesRc> = env
            .compile(v_list!(
                v_qsym!("test", "side-effect"),
                v_str!("b"),
                v_str!("str")
            ))
            .unwrap();
        assert_eq!(
            comp.types,
            BTreeSet::from_iter(std::iter::once(ValueType::String))
        );
        assert_eq!(
            *env.comp_side_effects.borrow(),
            HashSet::from_iter(vec!["a".to_string(), "b".to_string()])
        );
        assert_eq!(
            *env.eval_side_effects.borrow(),
            HashSet::from_iter(std::iter::once("a".to_string()))
        );

        assert_eq!(comp.result.evaluate(&mut env).unwrap(), v_str!("str"));
        assert_eq!(
            *env.comp_side_effects.borrow(),
            HashSet::from_iter(vec!["a".to_string(), "b".to_string()])
        );
        assert_eq!(
            *env.eval_side_effects.borrow(),
            HashSet::from_iter(vec!["a".to_string(), "b".to_string()])
        );
    }
}
