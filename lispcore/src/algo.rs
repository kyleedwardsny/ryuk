use super::error::*;
use super::list::*;
use super::value::*;

fn concat_lists_recursive<T, I>(list_item: ListItem<Value<T>>, mut rest: I) -> Result<Value<T>>
where
    T: ValueTypes + ?Sized,
    for<'a> &'a <T::SemverTypes as SemverTypes>::Semver: IntoIterator<Item = &'a u64>,
    Cons<T>: Into<T::ConsRef>,
    I: Iterator<Item = ListItem<Value<T>>>,
{
    match list_item {
        ListItem::Item(item) => Result::Ok(Value::Cons(ValueCons(
            Cons {
                car: item,
                cdr: concat_lists(rest)?,
            }
            .into(),
        ))),
        ListItem::List(mut list) => match list.next() {
            Option::Some(ListItem::Item(item)) => Result::Ok(Value::Cons(ValueCons(
                Cons {
                    car: item,
                    cdr: concat_lists_recursive(ListItem::List(list), rest)?,
                }
                .into(),
            ))),
            Option::Some(ListItem::List(tail)) => match rest.next() {
                Option::None => Result::Ok(tail),
                _ => Result::Err(Error::new(ErrorKind::IncorrectType, "Incorrect type")),
            },
            Option::None => match rest.next() {
                Option::None => Result::Ok(Value::Nil),
                Option::Some(list) => concat_lists_recursive(list, rest),
            },
        },
    }
}

pub fn concat_lists<T, I>(mut lists: I) -> Result<Value<T>>
where
    T: ValueTypes + ?Sized,
    for<'a> &'a <T::SemverTypes as SemverTypes>::Semver: IntoIterator<Item = &'a u64>,
    Cons<T>: Into<T::ConsRef>,
    I: Iterator<Item = ListItem<Value<T>>>,
{
    match lists.next() {
        Option::Some(v) => concat_lists_recursive(v, lists),
        Option::None => Result::Ok(Value::Nil),
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn test_concat_lists() {
        use super::*;

        let v = concat_lists::<ValueTypesRc, _>(
            vec![
                ListItem::List(v_list!(v_str!("str"), v_bool!(true)).convert()),
                ListItem::Item(v_list!(v_str!("str"), v_bool!(true)).convert()),
                ListItem::List(v_uqsym!("uqsym").convert()),
            ]
            .into_iter(),
        )
        .unwrap();
        assert_eq!(
            v,
            v_tlist!(
                v_str!("str"),
                v_bool!(true),
                v_list!(v_str!("str"), v_bool!(true)),
                v_uqsym!("uqsym")
            )
        );

        let v = concat_lists::<ValueTypesRc, _>(
            vec![
                ListItem::Item(v_bool!(true).convert()),
                ListItem::Item(v_bool!(false).convert()),
            ]
            .into_iter(),
        )
        .unwrap();
        assert_eq!(v, v_list!(v_bool!(true), v_bool!(false)));

        let v = concat_lists::<ValueTypesRc, _>(
            vec![ListItem::List(v_bool!(true).convert())].into_iter(),
        )
        .unwrap();
        assert_eq!(v, v_bool!(true));

        let v = concat_lists::<ValueTypesRc, _>(vec![].into_iter()).unwrap();
        assert_eq!(v, v_nil!());

        assert_eq!(
            concat_lists::<ValueTypesRc, _>(
                vec![
                    ListItem::List(v_bool!(true).convert()),
                    ListItem::List(v_bool!(true).convert()),
                ]
                .into_iter(),
            )
            .unwrap_err()
            .kind,
            ErrorKind::IncorrectType
        );
    }
}
