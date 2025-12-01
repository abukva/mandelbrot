mod regular_number;

use regular_number::Number;
use std::{
    cmp::Ordering,
    ops::{Add, Sub},
};

#[derive(Debug, Clone)]
pub(super) enum Internal<const PRECISION: usize> {
    Value(Number<PRECISION>),
    Zero { sign: bool },
    Infinity { sign: bool },
    NaN,
}

impl<const PRECISION: usize> Add for Internal<PRECISION> {
    type Output = Self;

    fn add(self, other: Self) -> Self {
        match (self, other) {
            (Self::NaN, _) | (_, Self::NaN) => Self::NaN,
            (Self::Infinity { sign: sign_lhs }, Self::Infinity { sign: sign_rhs }) => {
                if sign_lhs == sign_rhs {
                    Self::Infinity { sign: sign_rhs }
                } else {
                    Self::NaN
                }
            }
            (inf @ Self::Infinity { .. }, _) | (_, inf @ Self::Infinity { .. }) => inf,
            (Self::Zero { sign: sign_lhs }, Self::Zero { sign: sign_rhs }) => Self::Zero {
                sign: sign_rhs && sign_lhs,
            },
            (Self::Zero { .. }, num @ Self::Value(_))
            | (num @ Self::Value(_), Self::Zero { .. }) => num,
            (Self::Value(lhs), Self::Value(rhs)) => {
                let result = match (lhs.get_sign(), rhs.get_sign()) {
                    (false, false) => lhs.add_magnitudes(rhs, false),
                    (true, true) => lhs.add_magnitudes(rhs, true),
                    (false, true) => lhs.sub_magnitudes(rhs, false),
                    (true, false) => rhs.sub_magnitudes(lhs, false),
                };

                if result.is_zero() || result.is_underflow() {
                    Self::Zero {
                        sign: result.get_sign(),
                    }
                } else if result.is_overflow() {
                    Self::Infinity {
                        sign: result.get_sign(),
                    }
                } else {
                    Self::Value(result)
                }
            }
        }
    }
}

impl<const PRECISION: usize> Sub for Internal<PRECISION> {
    type Output = Self;

    fn sub(self, other: Self) -> Self {
        match (self, other) {
            (Self::NaN, _) | (_, Self::NaN) => Self::NaN,

            (Self::Infinity { sign: sign_lhs }, Self::Infinity { sign: sign_rhs }) => {
                if sign_lhs == sign_rhs {
                    Self::NaN
                } else {
                    Self::Infinity { sign: sign_lhs }
                }
            }

            (inf @ Self::Infinity { .. }, _) => inf,
            (_, Self::Infinity { sign }) => Self::Infinity { sign: !sign },
            (Self::Zero { sign: sign_lhs }, Self::Zero { sign: sign_rhs }) => Self::Zero {
                sign: sign_lhs && sign_rhs,
            },
            (Self::Zero { .. }, Self::Value(num)) => Self::Value(-num),
            (num @ Self::Value(_), Self::Zero { .. }) => num,
            (Self::Value(lhs), Self::Value(rhs)) => {
                let result = match (lhs.get_sign(), rhs.get_sign()) {
                    (false, false) => lhs.sub_magnitudes(rhs, false),
                    (true, true) => rhs.sub_magnitudes(lhs, false),
                    (false, true) => lhs.add_magnitudes(rhs, false),
                    (true, false) => lhs.add_magnitudes(rhs, true),
                };

                if result.is_zero() || result.is_underflow() {
                    Self::Zero {
                        sign: result.get_sign(),
                    }
                } else if result.is_overflow() {
                    Self::Infinity {
                        sign: result.get_sign(),
                    }
                } else {
                    Self::Value(result)
                }
            }
        }
    }
}

impl<const PRECISION: usize> PartialEq for Internal<PRECISION> {
    fn eq(&self, other: &Self) -> bool {
        match (&self, &other) {
            (Self::NaN, Self::NaN) => false,
            (Self::Infinity { sign: sign_lhs }, Self::Infinity { sign: sign_rhs }) => {
                sign_rhs == sign_lhs
            }
            (Self::Zero { .. }, Self::Zero { .. }) => true,
            (Self::Value(lhs), Self::Value(rhs)) => lhs == rhs,
            _ => false,
        }
    }
}

impl<const PRECISION: usize> PartialOrd for Internal<PRECISION> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        match (&self, &other) {
            (Self::NaN, _) | (_, Self::NaN) => None,
            (Self::Infinity { sign: sign_lhs }, Self::Infinity { sign: sign_rhs }) => {
                match (sign_lhs, sign_rhs) {
                    (true, true) => Some(Ordering::Equal),
                    (false, false) => Some(Ordering::Equal),
                    (true, false) => Some(Ordering::Less),
                    (false, true) => Some(Ordering::Greater),
                }
            }
            (Self::Infinity { sign }, _) => {
                if *sign {
                    Some(Ordering::Less)
                } else {
                    Some(Ordering::Greater)
                }
            }
            (_, Self::Infinity { sign }) => {
                if *sign {
                    Some(Ordering::Greater)
                } else {
                    Some(Ordering::Less)
                }
            }
            (Self::Zero { .. }, Self::Zero { .. }) => Some(Ordering::Equal),
            (Self::Zero { .. }, Self::Value(num)) => {
                if num.get_sign() {
                    Some(Ordering::Greater)
                } else {
                    Some(Ordering::Less)
                }
            }
            (Self::Value(num), Self::Zero { .. }) => {
                if num.get_sign() {
                    Some(Ordering::Less)
                } else {
                    Some(Ordering::Greater)
                }
            }
            (Self::Value(lhs), Self::Value(rhs)) => lhs.partial_cmp(rhs),
        }
    }
}

// Implementing Add for Number
impl<const PRECISION: usize> Add<&Internal<PRECISION>> for &Internal<PRECISION> {
    type Output = Internal<PRECISION>;

    fn add(self, other: &Internal<PRECISION>) -> Internal<PRECISION> {
        self.clone() + other.clone()
    }
}

impl<const PRECISION: usize> Add<&Internal<PRECISION>> for Internal<PRECISION> {
    type Output = Internal<PRECISION>;

    fn add(self, other: &Internal<PRECISION>) -> Internal<PRECISION> {
        self + other.clone()
    }
}

impl<const PRECISION: usize> Add<Internal<PRECISION>> for &Internal<PRECISION> {
    type Output = Internal<PRECISION>;

    fn add(self, other: Internal<PRECISION>) -> Internal<PRECISION> {
        self.clone() + other
    }
}

// Implementing Sub for Number
impl<const PRECISION: usize> Sub<&Internal<PRECISION>> for &Internal<PRECISION> {
    type Output = Internal<PRECISION>;

    fn sub(self, other: &Internal<PRECISION>) -> Internal<PRECISION> {
        self.clone() - other.clone()
    }
}

impl<const PRECISION: usize> Sub<&Internal<PRECISION>> for Internal<PRECISION> {
    type Output = Internal<PRECISION>;

    fn sub(self, other: &Internal<PRECISION>) -> Internal<PRECISION> {
        self - other.clone()
    }
}

impl<const PRECISION: usize> Sub<Internal<PRECISION>> for &Internal<PRECISION> {
    type Output = Internal<PRECISION>;

    fn sub(self, other: Internal<PRECISION>) -> Internal<PRECISION> {
        self.clone() - other
    }
}

impl<const PRECISION: usize> From<u64> for Internal<PRECISION> {
    fn from(value: u64) -> Self {
        match value {
            0 => Self::Zero { sign: false },
            _ => Self::Value(Number::from(value)),
        }
    }
}

impl<const PRECISION: usize> From<i64> for Internal<PRECISION> {
    fn from(value: i64) -> Self {
        match value {
            0 => Self::Zero { sign: false },
            _ => Self::Value(Number::from(value)),
        }
    }
}

impl<const PRECISION: usize> From<u32> for Internal<PRECISION> {
    fn from(value: u32) -> Self {
        Self::from(value as u64)
    }
}

impl<const PRECISION: usize> From<i32> for Internal<PRECISION> {
    fn from(value: i32) -> Self {
        Self::from(value as i64)
    }
}
