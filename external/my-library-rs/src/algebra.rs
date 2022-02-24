// ac-library-rs と同じ形式
pub trait Monoid {
    type S: Clone;
    fn identity() -> Self::S;
    fn binary_operation(a: &Self::S, b: &Self::S) -> Self::S;
}
pub trait MapMonoid {
    type M: Monoid;
    type F: Clone;
    // type S = <Self::M as Monoid>::S;
    fn identity_element() -> <Self::M as Monoid>::S {
        Self::M::identity()
    }
    fn binary_operation(
        a: &<Self::M as Monoid>::S,
        b: &<Self::M as Monoid>::S,
    ) -> <Self::M as Monoid>::S {
        Self::M::binary_operation(a, b)
    }
    fn identity_map() -> Self::F;
    fn mapping(f: &Self::F, x: &<Self::M as Monoid>::S) -> <Self::M as Monoid>::S;
    fn composition(f: &Self::F, g: &Self::F) -> Self::F;
}
