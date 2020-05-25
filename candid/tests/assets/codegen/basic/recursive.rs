pub struct List {
    pub head: u32,
    pub tail: Box<List>,
}
pub struct DoubleRecursion {
    pub a: DoubleRecursionA,
}
pub type DoubleRecursionA = Option<Box<DoubleRecursion>>;
