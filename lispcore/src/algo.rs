use super::error::*;
use super::list::*;
use super::value::*;

fn concat_lists_recursive<I>(list_item: ListItem<Value>, mut rest: I) -> Result<ValueList>
where
    I: Iterator<Item = ListItem<Value>>,
{
    match list_item {
        ListItem::Item(item) => Result::Ok(ValueList(Option::Some(
            Cons {
                car: item,
                cdr: concat_lists(rest)?,
            }
            .into(),
        ))),
        ListItem::List(Value::List(mut list)) => match list.next() {
            Option::Some(item) => Result::Ok(ValueList(Option::Some(
                Cons {
                    car: item,
                    cdr: concat_lists_recursive(ListItem::List(Value::List(list)), rest)?,
                }
                .into(),
            ))),
            Option::None => match rest.next() {
                Option::None => Result::Ok(ValueList(Option::None)),
                Option::Some(list) => concat_lists_recursive(list, rest),
            },
        },
        _ => Result::Err(e_type_error!()),
    }
}

pub fn concat_lists<I>(mut lists: I) -> Result<ValueList>
where
    I: Iterator<Item = ListItem<Value>>,
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

        let l = concat_lists(
            vec![
                ListItem::List(v_list!(v_str!("str"), v_bool!(true))),
                ListItem::Item(v_list!(v_str!("str"), v_bool!(true))),
                ListItem::Item(v_uqsym!("uqsym")),
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

        let l = concat_lists(
            vec![
                ListItem::Item(v_bool!(true)),
                ListItem::Item(v_bool!(false)),
            ]
            .into_iter(),
        )
        .unwrap();
        assert_eq!(l, list!(v_bool!(true), v_bool!(false)));

        let l = concat_lists(vec![].into_iter()).unwrap();
        assert_eq!(l, list!());

        assert_eq!(
            concat_lists(vec![ListItem::List(v_bool!(true))].into_iter(),).unwrap_err(),
            e_type_error!()
        );
    }
}
