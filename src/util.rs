#[derive(Clone, Debug)]
pub struct LinkedList<T> {
    head: T,
    length: usize,
    next: Option<Box<LinkedList<T>>>,
}

impl<T> LinkedList<T> {
    pub fn new(head: T, next: LinkedList<T>) -> LinkedList<T> {
        Self {
            head,
            length: next.length + 1,
            next: Some(Box::new(next)),
        }
    }

    pub fn singleton(head: T) -> Self {
        Self {
            head,
            length: 1,
            next: None,
        }
    }

    pub fn push(self, head: T) -> Self {
        Self::new(head, self)
    }

    pub fn pop(self) -> (T, Option<Box<Self>>) {
        let Self {
            head,
            next,
            length: _,
        } = self;
        (head, next)
    }

    pub fn peek(&self) -> (&T, Option<&Self>) {
        let Self {
            head,
            next,
            length: _,
        } = self;
        (head, next.as_deref())
    }

    pub fn cons(head: T, next: Box<LinkedList<T>>) -> Box<LinkedList<T>> {
        Box::new(Self {
            head,
            length: next.length + 1,
            next: Some(next),
        })
    }

    pub fn len(&self) -> usize {
        self.length
    }

    pub fn is_empty(&self) -> bool {
        false
    }

    pub fn iter<'a>(&'a self) -> LinkedListIter<'a, T> {
        LinkedListIter {
            current: Some(self),
        }
    }

    pub fn from_iter<I>(iter: I) -> Option<Self>
    where
        I: IntoIterator<Item = T>,
    {
        let mut it = iter.into_iter();
        let first = it.next()?;
        let mut out = LinkedList::singleton(first);
        for x in it {
            out = LinkedList::new(x, out);
        }
        Some(out)
    }
}

impl<'a, T: Clone + 'a> LinkedList<T> {
    pub fn from_iter_owned<I>(iter: I) -> Option<Self>
    where
        I: IntoIterator<Item = &'a T>,
    {
        Self::from_iter(iter.into_iter().cloned())
    }
}

impl<'a, T> LinkedList<&'a T> {
    pub fn from_iter_ref<I>(iter: I) -> Option<Self>
    where
        I: IntoIterator<Item = &'a T>,
    {
        let mut it = iter.into_iter();
        let first = it.next()?;
        let mut out = LinkedList::singleton(first);
        for x in it {
            out = LinkedList::new(x, out);
        }
        Some(out)
    }
}

impl<T> TryFrom<Vec<T>> for LinkedList<T> {
    type Error = ();

    fn try_from(mut value: Vec<T>) -> Result<Self, Self::Error> {
        let last = value.pop().ok_or(())?;
        let mut out = LinkedList::singleton(last);
        while let Some(last) = value.pop() {
            out = LinkedList::new(last, out);
        }
        Ok(out)
    }
}

pub struct LinkedListIter<'a, T> {
    current: Option<&'a LinkedList<T>>,
}

impl<'a, T> Iterator for LinkedListIter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        let current = self.current?;
        let (out, next) = current.peek();
        self.current = next;
        Some(out)
    }
}

impl<'a, T> IntoIterator for &'a LinkedList<T> {
    type Item = &'a T;

    type IntoIter = LinkedListIter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}
