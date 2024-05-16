

pub trait Borrow<Borrowed> {
    fn borrow(&self) -> &Borrowed;
}

pub trait BorrowMut<Borrowed>: Borrow<Borrowed> {
    fn borrow_mut(&mut self) -> &mut Borrowed;
}




impl<T> Borrow<T> for T {
    //#[rr::args("")]
    fn borrow(&self) -> &T {
        self
    }
}

impl<T> BorrowMut<T> for T {
    fn borrow_mut(&mut self) -> &mut T {
        self
    }
}

impl<T> Borrow<T> for &T {
    fn borrow(&self) -> &T {
        &**self
    }
}

impl<T> Borrow<T> for &mut T {
    fn borrow(&self) -> &T {
        &**self
    }
}

impl<T> BorrowMut<T> for &mut T {
    fn borrow_mut(&mut self) -> &mut T {
        &mut **self
    }
}
