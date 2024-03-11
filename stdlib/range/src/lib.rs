#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]

#![rr::coq_prefix("stdlib.range")]
#![rr::include("option")]
#![rr::include("iterator")]

#![feature(step_trait)]
use std::iter::Step;

#[rr::refined_by("start" : "{rt_of Idx}", "end" : "{rt_of Idx}")]
#[rr::export_as(std::ops::Range)]
pub struct Range<Idx> {
    /// The lower bound of the range (inclusive).
    #[rr::field("start")]
    pub start: Idx,
    /// The upper bound of the range (exclusive).
    #[rr::field("end")]
    pub end: Idx,
}


#[rr::context()]
impl<A: Step> Iterator for Range<A> {
    type Item = A;

    fn next(&mut self) -> Option<A> {
        unimplemented!();
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        unimplemented!();
    }

    fn count(self) -> usize {
        unimplemented!();
    }

    fn nth(&mut self, n: usize) -> Option<A> {
        unimplemented!();
    }

    fn last(mut self) -> Option<A> {
        unimplemented!();
    }

    fn min(mut self) -> Option<A> where A: Ord {
        unimplemented!();
    }

    //#[rr::args("(start, end)")]
    //#[rr::returns("")]
    fn max(mut self) -> Option<A> where A: Ord {
        unimplemented!();
    }

    //#[inline]
    //fn is_sorted(self) -> bool {
        //true
    //}

    //#[inline]
    //fn advance_by(&mut self, n: usize) -> Result<(), NonZeroUsize> {
        //self.spec_advance_by(n)
    //}

    /*
    #[inline]
    unsafe fn __iterator_get_unchecked(&mut self, idx: usize) -> Self::Item
    where
        Self: TrustedRandomAccessNoCoerce,
    {
        // SAFETY: The TrustedRandomAccess contract requires that callers only pass an index
        // that is in bounds.
        // Additionally Self: TrustedRandomAccess is only implemented for Copy types
        // which means even repeated reads of the same index would be safe.
        unsafe { Step::forward_unchecked(self.start.clone(), idx) }
    }
    */
}


