use super::error::*;
use super::list::*;
use super::value::*;

fn concat_lists_recursive<T, I>(list_item: ListItem<Value<T>>, mut rest: I) -> Result<ValueList<T>>
where
    T: ValueTypesMut + ?Sized,
    T::StringTypes: StringTypesMut,
    T::SemverTypes: SemverTypesMut,
    I: Iterator<Item = ListItem<Value<T>>>,
{
    match list_item {
        ListItem::Item(item) => Result::Ok(ValueList(Option::Some(T::cons_ref_from_cons(Cons {
            car: item,
            cdr: concat_lists(rest)?,
        })))),
        ListItem::List(Value::List(mut list)) => match list.next() {
            Option::Some(item) => {
                Result::Ok(ValueList(Option::Some(T::cons_ref_from_cons(Cons {
                    car: item,
                    cdr: concat_lists_recursive(ListItem::List(Value::List(list)), rest)?,
                }))))
            }
            Option::None => match rest.next() {
                Option::None => Result::Ok(ValueList(Option::None)),
                Option::Some(list) => concat_lists_recursive(list, rest),
            },
        },
        _ => Result::Err(Error::new(ErrorKind::IncorrectType, "Incorrect type")),
    }
}

pub fn concat_lists<T, I>(mut lists: I) -> Result<ValueList<T>>
where
    T: ValueTypesMut + ?Sized,
    T::StringTypes: StringTypesMut,
    T::SemverTypes: SemverTypesMut,
    I: Iterator<Item = ListItem<Value<T>>>,
{
    match lists.next() {
        Option::Some(v) => concat_lists_recursive(v, lists),
        Option::None => Result::Ok(ValueList(Option::None)),
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn test_concat_lists() {
        use super::*;

        let l = concat_lists::<ValueTypesRc, _>(
            vec![
                ListItem::List(v_list!(v_str!("str"), v_bool!(true)).convert()),
                ListItem::Item(v_list!(v_str!("str"), v_bool!(true)).convert()),
                ListItem::Item(v_uqsym!("uqsym").convert()),
            ]
            .into_iter(),
        )
        .unwrap();
        assert_eq!(
            l,
            list!(
                v_str!("str"),
                v_bool!(true),
                v_list!(v_str!("str"), v_bool!(true)),
                v_uqsym!("uqsym")
            )
        );

        let l = concat_lists::<ValueTypesRc, _>(
            vec![
                ListItem::Item(v_bool!(true).convert()),
                ListItem::Item(v_bool!(false).convert()),
            ]
            .into_iter(),
        )
        .unwrap();
        assert_eq!(l, list!(v_bool!(true), v_bool!(false)));

        let l = concat_lists::<ValueTypesRc, _>(vec![].into_iter()).unwrap();
        assert_eq!(l, list!());

        assert_eq!(
            concat_lists::<ValueTypesRc, _>(
                vec![ListItem::List(v_bool!(true).convert()),].into_iter(),
            )
            .unwrap_err()
            .kind,
            ErrorKind::IncorrectType
        );
    }
}
