pub trait Actor {
    fn fn1(arg0: u32) -> std::pin::Pin<std::boxed::Box<impl std::future::Future<Output = ()>>>;
    fn fn2() -> u8;
    fn fn3(arg0: u128) -> i128;
    fn fn4(arg0: bool) -> !;
}
