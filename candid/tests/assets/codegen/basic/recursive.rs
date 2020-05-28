#[derive(Clone)]
pub struct List {
    pub head: u32,
    pub tail: Box<List>,
}
#[derive(Clone)]
pub struct DoubleRecursion {
    pub a: DoubleRecursionA,
}
pub type DoubleRecursionA = Option<Box<DoubleRecursion>>;
