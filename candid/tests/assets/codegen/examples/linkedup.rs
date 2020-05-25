pub type UserId_2 = UserId;
pub type UserId = principal;
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
    fn connect(arg0: UserId_2) -> impl std::future::Future<Output = ()>;
    fn create(arg0: NewProfile) -> impl std::future::Future<Output = ()>;
    fn get(arg0: UserId_2) -> Profile;
    fn getConnections(arg0: UserId_2) -> impl std::future::Future<Output = Vec<Profile>>;
    fn getOwnId() -> UserId_2;
    fn healthcheck() -> impl std::future::Future<Output = bool>;
    fn isConnected(arg0: UserId_2) -> impl std::future::Future<Output = bool>;
    fn search(arg0: String) -> Vec<Profile>;
    fn update(arg0: Profile) -> impl std::future::Future<Output = ()>;
}
