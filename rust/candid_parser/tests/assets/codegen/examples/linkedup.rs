pub type UserId_2 = UserId;
pub type UserId = principal;
#[derive(Clone)]
pub struct Profile_2 {
    pub id: UserId,
    pub imgUrl: String,
    pub title: String,
    pub education: String,
    pub experience: String,
    pub company: String,
    pub lastName: String,
    pub firstName: String,
}
pub type Profile = Profile_2;
#[derive(Clone)]
pub struct NewProfile_2 {
    pub imgUrl: String,
    pub title: String,
    pub education: String,
    pub experience: String,
    pub company: String,
    pub lastName: String,
    pub firstName: String,
}
pub type NewProfile = NewProfile_2;
pub trait Actor {
    fn get(arg0: UserId_2) -> Profile;
    fn getConnections(
        arg0: UserId_2,
    ) -> std::pin::Pin<std::boxed::Box<impl std::future::Future<Output = Vec<Profile>>>>;    
    fn connect(
        arg0: UserId_2,
    ) -> std::pin::Pin<std::boxed::Box<impl std::future::Future<Output = ()>>>;
    fn search(arg0: String) -> Vec<Profile>;
    fn create(
        arg0: NewProfile,
    ) -> std::pin::Pin<std::boxed::Box<impl std::future::Future<Output = ()>>>;
    fn isConnected(
        arg0: UserId_2,
    ) -> std::pin::Pin<std::boxed::Box<impl std::future::Future<Output = bool>>>;
    fn update(
        arg0: Profile,
    ) -> std::pin::Pin<std::boxed::Box<impl std::future::Future<Output = ()>>>;
    fn getOwnId() -> UserId_2;
    fn healthcheck() -> std::pin::Pin<std::boxed::Box<impl std::future::Future<Output = bool>>>;
}
