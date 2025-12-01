#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ExponentState {
    Normal(i64),
    Overflow,
    Underflow,
}

impl ExponentState {
    pub(super) fn get_exponent(&self) -> i64 {
        match self {
            ExponentState::Normal(e) => *e,
            _ => panic!("Special value doesn't have exponent"),
        }
    }
}
