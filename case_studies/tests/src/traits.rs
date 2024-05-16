
/*
trait MyAdd {
    #[rr::args("x", "y")]
    #[rr::args("x", "y")]
    #[rr::exists("z")]
    #[rr::returns("z")]
    fn my_add(x: Self, y: Self) -> Self;
}

impl MyAdd for usize {
    #[rr::trust_me]
    #[rr::params("x", "y")]
    #[rr::args("x", "y")]
    #[rr::returns("x + y")]
    fn my_add(x: Self, y: Self) -> Self {
        x + y
    }
}

//#[rr::returns("()")]
//fn test_add() {
    //MyAdd::my_add(5usize, 5usize);
//}

// TODO: implement trait invocation for Param
#[rr::returns("()")]
fn test_add_2<T>(x: T, y: T) where T: MyAdd {
    MyAdd::my_add(x, y);
}
*/


//pub trait Bla {
    //type Output;

    //fn bla(&self) -> &Self::Output;
//}

//impl<T> Bla for Option<T> {
    //type Output = Option<T>;

    //#[rr::params("x")]
    //#[rr::args("#x")]
    //#[rr::returns("#x")]
    //fn bla(&self) -> &Option<T> {
        //self
    //}
//}

//#[rr::returns("()")]
//fn test_bla() {
    //let x = Some(3);
    //let _bla = x.bla();
//}

/*
trait XX {

}

trait Foo<T> where Self: XX {
    type Output;
    
    #[rr::params("a", "b")]
    #[rr::args("#a", "b")]
    #[rr::exists("y")]
    #[rr::returns("y")]
    fn bar<U> (&self, x: U) -> (Self::Output, T, U);
}

impl XX for i32 {

}

impl Foo<u32> for i32 {
    
    type Output = i32;
    
    #[rr::params("a", "b")]
    #[rr::args("#a", "b")]
    #[rr::exists("y")]
    #[rr::returns("y")]
    fn bar<U> (&self, x: U) -> (i32, u32, U) {
        ( *self, 42, x)
    }
}

#[rr::params("w")]
#[rr::args("#w")]
fn foobar2<W, T> (x: &W) where W: Foo<T> {
    // NOTE: for this, we need to look up the Alias type in the trait registry.
    x.bar(true);
}

#[rr::returns("()")]
fn call_foobar2() {
    let a = 0;
    foobar2(&a);
}
*/

// Note: this is invalid!
/*
trait FooB<T> 
    where Self : FooB<T>
{
    type Output;
}
*/


trait Foo<T> 
{
    type Output;
    
    #[rr::params("a", "b")]
    #[rr::args("#a", "b")]
    #[rr::exists("y")]
    #[rr::returns("y")]
    fn bar<U> (&self, x: U) -> (Self::Output, T, U);
}

impl Foo<u32> for i32 {
    
    type Output = i32;
    
    #[rr::params("a", "b")]
    #[rr::args("#a", "b")]
    #[rr::exists("y")]
    #[rr::returns("y")]
    fn bar<U> (&self, x: U) -> (i32, u32, U) {
        ( *self, 42, x)
    }
}

// So, I can also do requirements which might only be fulfilled later.
// (i.e. the requirement on T might be fulfilled by another instance).
impl<T> Foo<i32> for T 
    where T : Foo<i32>
{
    type Output = i32;

    fn bar<U>(&self, x : U ) -> (Self::Output, i32, U) {
        unimplemented!();
    }
}

#[rr::params("w")]
#[rr::args("#w")]
fn foobar<W, T> (x: &W) where W: Foo<T> {
    // NOTE: for this, we need to look up the Alias type in the trait registry.
    x.bar(true);
}

#[rr::returns("()")]
fn call_foobar() {
    let a = 0;
    foobar(&a);
}
