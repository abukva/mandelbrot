mod regular_number;

use core::f64;
use regex::Regex;
use regular_number::Number;
use std::{
    cmp::Ordering,
    ops::{Add, Div, Mul, Sub},
    sync::OnceLock,
};

#[derive(Debug, Clone, Copy)]
pub(super) enum Internal<const LIMBS: usize> {
    Value(Number<LIMBS>),
    Zero { sign: bool },
    Infinity { sign: bool },
    NaN,
}

#[derive(Debug, Clone)]
struct StringNumberParts<'a> {
    sign: bool,
    integer: &'a str,
    decimal: Option<&'a str>,
}

impl StringNumberParts<'_> {
    fn parse(s: &str) -> Option<StringNumberParts<'_>> {
        static RE: OnceLock<Regex> = OnceLock::new();
        let re = RE.get_or_init(|| Regex::new(r"^([+-]?)(\d+)(?:\.(\d+))?$").unwrap());

        re.captures(s).map(|caps| {
            let sign = matches!(caps.get(1).map(|m| m.as_str()), Some("-"));

            StringNumberParts {
                sign,
                integer: caps.get(2).unwrap().as_str(),
                decimal: caps.get(3).map(|m| m.as_str()),
            }
        })
    }
}

impl<const LIMBS: usize> Internal<LIMBS> {
    pub fn powi(&self, exponenet: i64) -> Self {
        let one = Self::Value(Number::from(1));

        match (self, exponenet) {
            (Self::NaN, _) => Self::NaN,
            (val, _) if val == &one => one,
            (_, 0) => one,
            (Self::Zero { sign }, exp) => {
                let result_sign = if exp % 2 != 0 { *sign } else { false };
                if exp > 0 {
                    Self::Zero { sign: result_sign }
                } else {
                    Self::Infinity { sign: result_sign }
                }
            }
            (Self::Infinity { sign: true }, exp) => {
                let result_sign = exp % 2 != 0;
                if exp < 0 {
                    Self::Zero { sign: result_sign }
                } else {
                    Self::Infinity { sign: result_sign }
                }
            }
            (Self::Infinity { sign: false }, exp) => {
                if exp < 0 {
                    Self::Zero { sign: false }
                } else {
                    Self::Infinity { sign: false }
                }
            }
            (num @ Self::Value(_), exp) => {
                let mut result = *num;
                for _ in 1..exp.abs() {
                    result = result * (*num);
                }
                if exp > 0 {
                    result
                } else {
                    Self::Value(Number::from(1)) / result
                }
            }
        }
    }
}

impl<const LIMBS: usize> Internal<LIMBS> {
    pub fn parse(text: &str) -> Self {
        let str_number = StringNumberParts::parse(text).expect("Improper number format");
        let mut result = Self::Zero { sign: false };

        let full_digits = match str_number.decimal {
            Some(decimal_str) => format!("{}{}", str_number.integer, decimal_str),
            None => str_number.integer.to_string(),
        };

        for (exp, c) in full_digits.chars().rev().enumerate() {
            let digit = c.to_digit(10).unwrap() as u64;
            if digit != 0 {
                result = result
                    + Self::Value(Number::from(digit))
                        * Self::Value(Number::from(10)).powi(exp as i64);
            }
        }

        if let Some(decimal_str) = str_number.decimal {
            let decimal_places = decimal_str.len() as i64;
            result = result / Self::Value(Number::from(10)).powi(decimal_places);
        }

        match result {
            Self::Value(mut num) => {
                num.set_sign(str_number.sign);
                Self::Value(num)
            }
            val => val,
        }
    }
}

impl<const LIMBS: usize> Add for Internal<LIMBS> {
    type Output = Self;

    #[inline]
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

impl<const LIMBS: usize> Sub for Internal<LIMBS> {
    type Output = Self;

    #[inline]
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

impl<const LIMBS: usize> Mul for Internal<LIMBS> {
    type Output = Self;

    #[inline]
    fn mul(self, other: Self) -> Self {
        match (self, other) {
            (Self::NaN, _) | (_, Self::NaN) => Self::NaN,

            (Self::Zero { sign: sign_lhs }, Self::Zero { sign: sign_rhs }) => Self::Zero {
                sign: sign_lhs != sign_rhs,
            },

            (Self::Zero { sign }, Self::Value(num)) | (Self::Value(num), Self::Zero { sign }) => {
                Self::Zero {
                    sign: sign != num.get_sign(),
                }
            }

            (Self::Zero { .. }, Self::Infinity { .. })
            | (Self::Infinity { .. }, Self::Zero { .. }) => Self::NaN,

            (Self::Infinity { sign: sign_lhs }, Self::Infinity { sign: sign_rhs }) => {
                Self::Infinity {
                    sign: sign_lhs != sign_rhs,
                }
            }

            (Self::Infinity { sign: sign_inf }, Self::Value(num))
            | (Self::Value(num), Self::Infinity { sign: sign_inf }) => Self::Infinity {
                sign: sign_inf != num.get_sign(),
            },

            (Self::Value(lhs), Self::Value(rhs)) => {
                let lhs_exp = lhs.get_exponent();
                let rhs_exp = rhs.get_exponent();

                match lhs_exp.checked_add(rhs_exp) {
                    None => {
                        if (lhs_exp > 0 && rhs_exp > 0) || (lhs_exp < 0 && rhs_exp < 0) {
                            Self::Infinity {
                                sign: lhs.get_sign() != rhs.get_sign(),
                            }
                        } else {
                            Self::Zero {
                                sign: lhs.get_sign() != rhs.get_sign(),
                            }
                        }
                    }
                    Some(_) => {
                        let result = lhs.mul_magnitudes(rhs);

                        if result.is_underflow() {
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
    }
}

impl<const LIMBS: usize> Div for Internal<LIMBS> {
    type Output = Self;

    #[inline]
    fn div(self, other: Self) -> Self {
        match (self, other) {
            (Self::NaN, _) | (_, Self::NaN) => Self::NaN,
            (Self::Infinity { .. }, Self::Infinity { .. }) => Self::NaN,
            (Self::Zero { .. }, Self::Zero { .. }) => Self::NaN,
            (Self::Zero { sign: sign_z }, Self::Infinity { sign: sign_i }) => Self::Zero {
                sign: sign_z != sign_i,
            },
            (Self::Infinity { sign: sign_i }, Self::Zero { sign: sign_z }) => Self::Infinity {
                sign: sign_i != sign_z,
            },
            (Self::Zero { sign }, Self::Value(num)) => Self::Zero {
                sign: sign != num.get_sign(),
            },
            (Self::Value(num), Self::Infinity { sign }) => Self::Zero {
                sign: num.get_sign() != sign,
            },
            (Self::Infinity { sign }, Self::Value(num)) => Self::Infinity {
                sign: num.get_sign() != sign,
            },
            (Self::Value(num), Self::Zero { sign }) => Self::Infinity {
                sign: num.get_sign() != sign,
            },
            (Self::Value(dividend), Self::Value(divisor)) => {
                let dividend_exp = dividend.get_exponent();
                let divisor_exp = divisor.get_exponent();

                match dividend_exp.checked_sub(divisor_exp) {
                    None => {
                        if (dividend_exp > 0 && divisor_exp < 0)
                            || (dividend_exp < 0 && divisor_exp > 0)
                        {
                            Self::Infinity {
                                sign: dividend.get_sign() != divisor.get_sign(),
                            }
                        } else {
                            Self::Zero {
                                sign: dividend.get_sign() != divisor.get_sign(),
                            }
                        }
                    }
                    Some(_) => {
                        let result = dividend.div_magnitudes(divisor);

                        if result.is_underflow() {
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
    }
}

impl<const LIMBS: usize> PartialEq for Internal<LIMBS> {
    #[inline]
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

impl<const LIMBS: usize> PartialOrd for Internal<LIMBS> {
    #[inline]
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

impl<const LIMBS: usize> From<u64> for Internal<LIMBS> {
    #[inline]
    fn from(value: u64) -> Self {
        match value {
            0 => Self::Zero { sign: false },
            _ => Self::Value(Number::from(value)),
        }
    }
}

impl<const LIMBS: usize> From<i64> for Internal<LIMBS> {
    #[inline]
    fn from(value: i64) -> Self {
        match value {
            0 => Self::Zero { sign: false },
            _ => Self::Value(Number::from(value)),
        }
    }
}

impl<const LIMBS: usize> From<u32> for Internal<LIMBS> {
    #[inline]
    fn from(value: u32) -> Self {
        Self::from(value as u64)
    }
}

impl<const LIMBS: usize> From<i32> for Internal<LIMBS> {
    #[inline]
    fn from(value: i32) -> Self {
        Self::from(value as i64)
    }
}

impl<const LIMBS: usize> From<f64> for Internal<LIMBS> {
    #[inline]
    fn from(value: f64) -> Self {
        if value.is_nan() {
            Self::NaN
        } else if value.is_infinite() {
            Self::Infinity {
                sign: value.is_sign_negative(),
            }
        } else if value == 0.0 {
            Self::Zero {
                sign: value.is_sign_negative(),
            }
        } else {
            Self::Value(Number::from(value))
        }
    }
}

impl<const LIMBS: usize> From<f32> for Internal<LIMBS> {
    #[inline]
    fn from(value: f32) -> Self {
        Self::from(value as f64)
    }
}
