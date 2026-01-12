use nonempty::NonEmpty;

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

    pub fn push_back(self, last: Self) -> Self {
        let (head, tail) = self.pop();
        let tail = match tail {
            Some(tail) => tail.push_back(last),
            None => last,
        };
        Self::new(head, tail)
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

    pub fn peek_mut(&mut self) -> (&mut T, Option<&mut Self>) {
        let Self {
            head,
            next,
            length: _,
        } = self;
        (head, next.as_deref_mut())
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

    pub fn iter_mut<'a>(&'a mut self) -> LinkedListIterMut<'a, T> {
        LinkedListIterMut {
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

impl<T> From<NonEmpty<T>> for LinkedList<T> {
    fn from(value: NonEmpty<T>) -> Self {
        let NonEmpty { head, tail } = value;
        let tail = tail.try_into();
        match tail {
            Ok(tail) => LinkedList::new(head, tail),
            Err(_) => LinkedList::singleton(head),
        }
    }
}

impl<T> From<NonEmpty<T>> for Box<LinkedList<T>> {
    fn from(value: NonEmpty<T>) -> Self {
        let NonEmpty { head, tail } = value;
        let tail = tail.try_into();
        match tail {
            Ok(tail) => Box::new(LinkedList::new(head, tail)),
            Err(_) => Box::new(LinkedList::singleton(head)),
        }
    }
}

impl<T> LinkedList<&T> {
    pub fn unpeek<'a, 'b>(head: &'a T, tail: &'b LinkedList<&T>) -> LinkedList<&'a T>
    where
        'b: 'a,
    {
        LinkedList::new(head, tail.into())
    }
}

impl<'a, T> From<&'a LinkedList<T>> for LinkedList<&'a T> {
    fn from(value: &'a LinkedList<T>) -> Self {
        let (head, tail) = value.peek();
        match tail {
            None => LinkedList::singleton(head),
            Some(tail) => LinkedList::new(head, tail.into()),
        }
    }
}

impl<'a, T> From<&'a LinkedList<&T>> for LinkedList<&'a T> {
    fn from(value: &'a LinkedList<&T>) -> Self {
        let (head, tail) = value.peek();
        match tail {
            None => LinkedList::singleton(head),
            Some(tail) => LinkedList::new(head, tail.into()),
        }
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

pub struct LinkedListIterMut<'a, T> {
    current: Option<&'a mut LinkedList<T>>,
}

impl<'a, T> Iterator for LinkedListIterMut<'a, T> {
    type Item = &'a mut T;

    fn next(&mut self) -> Option<Self::Item> {
        let current = self.current.take()?;
        let (out, next) = current.peek_mut();
        self.current = next;
        Some(out)
    }
}

impl<'a, T> IntoIterator for &'a mut LinkedList<T> {
    type Item = &'a mut T;

    type IntoIter = LinkedListIterMut<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}
