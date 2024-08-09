
mod add {
    trait MyAdd {
        #[rr::params("x", "y")]
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

    #[rr::verify]
    fn test_add() {
        MyAdd::my_add(5usize, 5usize);
    }

    #[rr::params("x", "y")]
    #[rr::args("x", "y")]
    fn test_add_2<T>(x: T, y: T) where T: MyAdd {
        MyAdd::my_add(x, y);
    }
}

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


// TODO: support skip for modules
//#[rr::skip]
mod foo {
    pub trait Foo<T> 
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

        // TODO
        fn bar<U>(&self, x : U ) -> (Self::Output, i32, U) {
            unimplemented!();
        }
    }

    #[rr::params("w")]
    #[rr::args("#w")]
    fn foobar<W, T> (x: &W) where W: Foo<T> {
        x.bar(true);
    }

    #[rr::params("w")]
    #[rr::args("#w")]
    fn call_foobar2<W>(x: &W) where W: Foo<i32> {
        foobar(x); 
    }

    #[rr::verify]
    fn call_foobar() {
        let a = 0;
        foobar(&a);
    }
}

/*
mod extend {
    use crate::traits::foo;

    trait Bar<T> : foo::Foo<T> {
        fn mybar(&self) -> Self::Output;
    }

    // TODO: if I show a different spec for an impl, show that it implies the base spec as a
    // sanity check.
    // We could also register that as hints for when we need to subsume on instantiation
    // TODO: by default, use the trait spec for impls of traits, if we don't provide a more
    // specific spec
    // TODO: also generate a spec record for more specific specs

    impl Bar<u32> for i32 {
        //#[rr::]
        fn mybar(&self) -> Self::Output {
           42  
        }
    }


    // TODO: if I translate a trait, also introduce all the assoc types of dependencies
    

    // Point with the assumption on the spec: it's weird to fix a particular spec in the base spec.
    // For any more specific spec, it might make sense. 
    // Or rather: any impl of the trait is going to assume a particular spec
    // Which spec is that?
    // Well, this might depend on what is declared, in particular for closures
    // So I have to give it the particular spec I actually have. 
    //
    // Conclusion for now:
    // - the base spec should not be parametric
    // - more specific specs should be

    // 

    // TODO: emit warning when number of args isn't matching
    #[rr::params("x")]
    #[rr::args("#x")]
    fn foobar<W>(x: &W) where W : Bar<i32> {
        // should the dependency be parametric in the spec of Foo?
        // 
        // I guess I should be able to resolve the dependency at link time.
        // i.e. I have to show at link time that my implementation of Bar can use my implementation
        // of Foo in terms of specification. 
        //
        // What if my impl of Bar assumes a stronger spec for Foo?
        // Two sides:
        // - the implementation proves a particular specification, and this relies on the
        // implementation of Foo having a particular specification
        // - at the using side of Bar, I just want to assume that there's a particular
        // specification for Bar. 
        //
        // when I then call into this function, I need to provide the necessary trait assumptions
        // i.e. I have to determine a particular spec (from the set of impls I have), and then show
        // that it subsumes the assumed spec. 
        //
        // what happens 
        //
        // When I link everything together, I also need to show that I can actually materialize
        // this spec, 
        // Then 
        let a = x.mybar();
        let b = x.bar(42);
    }
}
*/

mod assoc_dep {
    /// Dependencies between associated types should be resolved correctly.
    
    trait Foo {
        type Output;

    }

    #[rr::params("x", "y")]
    #[rr::args("x", "y")]
    fn bla<T, U>(x: T, y: U) 
        where T: Foo, U: Foo<Output = T::Output>
    {

    }

    #[rr::params("x", "y")]
    #[rr::args("x", "y")]
    fn bla2<T, U>(x: T, y: U) 
        where T: Foo, U: Foo<Output = i32>
    {

    }

}

mod data {
    trait Magic {
        
    }

    trait DS<T> where T: Magic {

    }

    //impl Magic for DS<T> {
        
    //}
}

mod iter {
    trait Iter {
        type Elem;

        fn next(&mut self) -> Option<Self::Elem>;
    }

    struct Counter {
        cur: i32,
        max: i32,
    }

    impl Iter for Counter {
        type Elem = i32;

        fn next(&mut self) -> Option<i32> {
            None
        }
    }

}


mod rec {
    // What if we have an impl of a trait which is mutually recursive with another function (also
    // as part of a trait impl)?
    // - then, which spec do we assume? 
    //   + if we parameterize it, 
    //   + if it's another method within the same impl (i.e. we can definitely statically resolve
    //     it to the same impl):
    //     we just treat it the same as any other method, and should not generate a trait
    //     parameterization
    //   + 


    // What if a trait method impl is recursive?
    // I guess in that case we should also be able to figure out that we go into the same method
    // and this is a true recursive call?
    // TODO test this

}
