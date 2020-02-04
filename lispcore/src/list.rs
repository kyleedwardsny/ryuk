use super::error::*;
use super::value::ValueTypes;

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum ListItem<T> {
    Item(T),
    List(T),
}

impl<T> ListItem<T> {
    pub fn try_unwrap_item<ET>(self) -> Result<T, ET>
    where
        ET: ValueTypes + ?Sized,
    {
        match self {
            Self::Item(item) => Result::Ok(item),
            _ => Result::Err(e_type_error!(ET)),
        }
    }

    pub fn unwrap_item(self) -> T {
        match self {
            Self::Item(item) => item,
            _ => panic!("Expected ListItem::Item"),
        }
    }

    pub fn unwrap_list(self) -> T {
        match self {
            Self::List(list) => list,
            _ => panic!("Expected ListItem::List"),
        }
    }

    pub fn as_ref(&self) -> ListItem<&T> {
        match self {
            Self::Item(item) => ListItem::Item(item),
            Self::List(list) => ListItem::List(list),
        }
    }

    pub fn as_mut(&mut self) -> ListItem<&mut T> {
        match self {
            Self::Item(item) => ListItem::Item(item),
            Self::List(list) => ListItem::List(list),
        }
    }

    pub fn map<U>(self, f: impl FnOnce(T) -> U) -> ListItem<U> {
        match self {
            Self::Item(item) => ListItem::Item(f(item)),
            Self::List(list) => ListItem::List(f(list)),
        }
    }
}

impl<T, E> ListItem<std::result::Result<T, E>> {
    pub fn transpose(self) -> std::result::Result<ListItem<T>, E> {
        std::result::Result::Ok(match self {
            Self::Item(item) => ListItem::Item(item?),
            Self::List(list) => ListItem::List(list?),
        })
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn test_list_item_map() {
        use super::*;

        let item = ListItem::<i32>::Item(1);
        assert_eq!(item.map(|v| v == 0), ListItem::<bool>::Item(false));

        let item = ListItem::<i32>::List(0);
        assert_eq!(item.map(|v| v == 0), ListItem::<bool>::List(true));
    }

    #[test]
    fn test_list_item_transpose() {
        use super::*;

        let item = ListItem::<std::result::Result<bool, ()>>::Item(std::result::Result::Ok(true));
        assert_eq!(item.transpose().unwrap(), ListItem::Item(true));

        let item = ListItem::<std::result::Result<bool, ()>>::Item(std::result::Result::Err(()));
        assert_eq!(item.transpose().unwrap_err(), ());

        let list = ListItem::<std::result::Result<bool, ()>>::List(std::result::Result::Ok(true));
        assert_eq!(list.transpose().unwrap(), ListItem::List(true));

        let list = ListItem::<std::result::Result<bool, ()>>::List(std::result::Result::Err(()));
        assert_eq!(list.transpose().unwrap_err(), ());
    }
}
