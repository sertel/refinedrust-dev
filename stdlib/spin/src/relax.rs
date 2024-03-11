

#[rr::export_as(spin::relax::RelaxStrategy)]
pub trait RelaxStrategy { #[rr::returns("()")]
    fn relax();
}

#[rr::export_as(spin::relax::Spin)]
pub struct Spin { }

#[rr::only_spec]
impl RelaxStrategy for Spin {
    #[rr::returns("()")]
    fn relax() {
        unimplemented!();
    }
}
