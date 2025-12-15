#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ExponentState {
    Normal(i64),
    Overflow,
    Underflow,
}

impl ExponentState {
    #[inline]
    pub(super) fn get_exponent(&self) -> i64 {
        match self {
            ExponentState::Normal(e) => *e,
            _ => panic!("Special value doesn't have exponent"),
        }
    }

    #[inline]
    pub(super) fn sum_exponents(exponents: &[i64]) -> Self {
        let sum: i128 = exponents.iter().map(|&x| x as i128).sum();

        if sum > i64::MAX as i128 {
            Self::Overflow
        } else if sum < i64::MIN as i128 {
            Self::Underflow
        } else {
            Self::Normal(sum as i64)
        }
    }
}
