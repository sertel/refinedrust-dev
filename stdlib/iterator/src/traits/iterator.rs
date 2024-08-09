
//use core::iter::Map;
use crate::adapters::map::Map;


// Coq model for an iterator:
// - it has a state 
// - f : state → option (state * next_element)

// Currently, we'll need to specify that every time again. Could we have a common spec attribute we
// declare for a trait? 
// When instantiating an instance, we should instantiate that attribute.
//
// Could we maybe encode this via Coq typeclasses? Then this would go via the refinement type
// - the trait defines a typeclass that implementer types of the trait need to implement
// - i.e. we would define a new type (record) for the refinement of an instance
// - then we implement the trait's typeclass. 
//
// This is probably the easiest way to make that association. 
// We could probably automatically generate it.


fn test() {
    let mut x = vec![1, 2, 3];

    x.iter_mut().map(|x| *x *= 2).count();
}


// Iterator for Vec:
// - it_state = (elements_to_follow, elements_already_processed)



#[rr::export_as(core::iter::traits::Iterator)]
/// Implementers of the `Iterator` trait also have to implement the `Iterator` typeclass for the `Self` type. 


// Point: since spec attributes are not solely determined by the involved refinement type, (there
// might be several different impls under different preconditions which have the same refinement
// type), we should probably make these part of the spec record
#[rr::spec_attr("iterator_it" : "Iterator {rt_of Self} {rt_of Item}")]
pub trait Iterator {
    type Item;

    #[rr::params("it_state" : "{rt_of Self}", "γ")]
    #[rr::args("(#it_state, γ)")]
    /// Postcondition: There exists an optional next item and the successor state of the iterator.
    #[rr::exists("x" : "option {rt_of Item}", "new_it_state" : "{rt_of Self}")]
    /// Postcondition: If there is a next item, it obeys the iterator's relation, and similarly the
    /// successor state is determined.
    #[rr::ensures("if (decide (iterator_done it_state)) then new_it_state = it_state
        else ∃ y, x = Some y ∧ iterator_next it_state y new_it_state")]
    /// Postcondition: The state of the iterator has been updated.
    #[rr::observe("γ": "new_it_state")]
    /// Postcondition: We return the optional next element.
    #[rr::returns("<#>@{option} x")]
    fn next(&mut self) -> Option<Self::Item>;


    #[rr::params("it_state" : "{rt_of Self}", "clos_state" : "{rt_of F}")]
    #[rr::args("it_state", "clos_state")] 
    // TODO: wire the state of the closure up correctly
    #[rr::returns("")]
    fn map<B, F>(self, 
        #[rr::bla]
        f: F) -> Map<Self, F>
    where
        Self: Sized,
        F: FnMut(Self::Item) -> B,
    {
        Map::new(self, f)
    }

    // TODO: more methods
    // Basically, we should have a common interface for types implementing the Iterator trait, and
    // when we generate a specific instantiation, we want to instantiate that interface.
}


