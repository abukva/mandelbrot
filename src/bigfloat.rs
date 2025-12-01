#![allow(dead_code)]

mod internal;

use internal::Internal;
use std::{
    cmp::Ordering,
    ops::{Add, Sub},
};

#[derive(Debug, Clone)]
pub struct BigFloat<const PRECISION: usize>(Internal<PRECISION>);

impl<const PRECISION: usize> BigFloat<PRECISION> {
    pub fn zero() -> Self {
        Self(Internal::<PRECISION>::Zero { sign: false })
    }

    pub fn zero_negative(sign: bool) -> Self {
        Self(Internal::<PRECISION>::Zero { sign })
    }

    pub fn infinity() -> Self {
        Self(Internal::<PRECISION>::Infinity { sign: false })
    }

    pub fn infinity_negative() -> Self {
        Self(Internal::Infinity { sign: true })
    }

    pub fn nan() -> Self {
        Self(Internal::<PRECISION>::NaN)
    }

    pub fn is_nan(&self) -> bool {
        matches!(self.0, Internal::NaN)
    }
}

impl<const PRECISION: usize> Add for BigFloat<PRECISION> {
    type Output = Self;

    fn add(self, other: Self) -> Self {
        Self(self.0 + other.0)
    }
}

impl<const PRECISION: usize> Sub for BigFloat<PRECISION> {
    type Output = Self;

    fn sub(self, other: Self) -> Self {
        Self(self.0 - other.0)
    }
}

impl<const PRECISION: usize> PartialEq for BigFloat<PRECISION> {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl<const PRECISION: usize> PartialOrd for BigFloat<PRECISION> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.0.partial_cmp(&other.0)
    }
}

impl<const PRECISION: usize> From<u64> for BigFloat<PRECISION> {
    fn from(value: u64) -> Self {
        Self(Internal::from(value))
    }
}

impl<const PRECISION: usize> From<i64> for BigFloat<PRECISION> {
    fn from(value: i64) -> Self {
        Self(Internal::from(value))
    }
}

impl<const PRECISION: usize> From<u32> for BigFloat<PRECISION> {
    fn from(value: u32) -> Self {
        Self::from(value as u64)
    }
}

impl<const PRECISION: usize> From<i32> for BigFloat<PRECISION> {
    fn from(value: i32) -> Self {
        Self::from(value as i64)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_subtract_larger_from_smaller() {
        let a = BigFloat::<64>::from(1);
        let b = BigFloat::<64>::from(2);
        let result = a - b;
        assert_eq!(result, BigFloat::<64>::from(-1))
    }

    #[test]
    fn test_subtract_same_numbers() {
        let a = BigFloat::<64>::from(5);
        let b = BigFloat::<64>::from(5);
        assert_eq!(a - b, BigFloat::<64>::zero());
    }

    #[test]
    fn test_subtract_with_zero() {
        let a = BigFloat::<64>::from(5);
        let zero = BigFloat::<64>::zero();
        assert_eq!(a.clone() - zero, a);
    }

    #[test]
    fn test_subtract_with_nan() {
        let a = BigFloat::<64>::from(5);
        let nan = BigFloat::<64>::nan();
        assert!((a - nan).is_nan());
    }

    #[test]
    fn test_subtract_with_infinity() {
        let one = BigFloat::<128>::from(1);
        let inf = BigFloat::<128>::infinity();
        let inf_neg = BigFloat::<128>::infinity_negative();

        assert_eq!(one.clone() - inf.clone(), inf_neg.clone());
        assert_eq!(one.clone() - inf_neg.clone(), inf.clone());
    }

    #[test]
    fn test_subtract_infinity_from_infinity() {
        let inf = BigFloat::<128>::infinity();
        assert!((inf.clone() - inf).is_nan());
    }

    #[test]
    fn test_add_negative_numbers() {
        let a = BigFloat::<64>::from(-2);
        let b = BigFloat::<64>::from(-3);
        assert_eq!(a + b, BigFloat::<64>::from(-5));
    }

    #[test]
    fn test_add_positive_and_negative() {
        let a = BigFloat::<64>::from(5);
        let b = BigFloat::<64>::from(-3);
        assert_eq!(a + b, BigFloat::<64>::from(2));
    }

    #[test]
    fn test_add_negative_and_positive() {
        let a = BigFloat::<64>::from(-5);
        let b = BigFloat::<64>::from(3);
        assert_eq!(a + b, BigFloat::<64>::from(-2));
    }

    #[test]
    fn test_infinity_plus_infinity_same_sign() {
        let inf = BigFloat::<128>::infinity();
        assert_eq!(inf.clone() + inf.clone(), inf);

        let neg_inf = BigFloat::<128>::infinity_negative();
        assert_eq!(neg_inf.clone() + neg_inf.clone(), neg_inf);
    }

    #[test]
    fn test_infinity_plus_infinity_opposite_sign() {
        let inf = BigFloat::<128>::infinity();
        let neg_inf = BigFloat::<128>::infinity_negative();
        assert!((inf + neg_inf).is_nan());
    }

    #[test]
    fn test_nan_equality() {
        let nan1 = BigFloat::<128>::nan();
        let nan2 = BigFloat::<128>::nan();
        assert_ne!(nan1, nan2);
    }

    #[test]
    fn test_zero_with_different_signs() {
        let zero_pos = BigFloat::<128>::zero();
        let zero_neg = BigFloat::<128>::zero_negative(true);
        assert_eq!(zero_pos, zero_neg);
    }

    #[test]
    fn test_comparison_with_nan() {
        let a = BigFloat::<64>::from(5);
        let nan = BigFloat::<64>::nan();
        assert_eq!(a.partial_cmp(&nan), None);
        assert_eq!(nan.partial_cmp(&a), None);
    }

    #[test]
    fn test_comparison_basic() {
        let a = BigFloat::<64>::from(5);
        let b = BigFloat::<64>::from(10);
        assert!(a < b);
        assert!(b > a);
    }

    #[test]
    fn test_comparison_with_infinity() {
        let num = BigFloat::<64>::from(1000000);
        let inf = BigFloat::<64>::infinity();
        let neg_inf = BigFloat::<64>::infinity_negative();

        assert!(num < inf);
        assert!(num > neg_inf);
    }

    #[test]
    fn test_comparison_with_zero() {
        let positive = BigFloat::<64>::from(5);
        let negative = BigFloat::<64>::from(-5);
        let zero = BigFloat::<64>::zero();

        assert!(positive > zero);
        assert!(negative < zero);
    }

    #[test]
    fn test_add_large_numbers() {
        let a = BigFloat::<128>::from(u64::MAX);
        let b = BigFloat::<128>::from(u64::MAX);
        let result = a + b;
        assert!(!result.is_nan());
    }

    #[test]
    fn test_max_values() {
        let max_u64 = BigFloat::<64>::from(u64::MAX);
        let one = BigFloat::<64>::from(1);
        let result = max_u64 + one;
        assert!(!result.is_nan());
    }

    #[test]
    fn test_different_precision_values() {
        let a_64 = BigFloat::<64>::from(42);
        let a_128 = BigFloat::<128>::from(42);
        let a_256 = BigFloat::<256>::from(42);

        assert_eq!(a_64.clone() + a_64, BigFloat::<64>::from(84));
        assert_eq!(a_128.clone() + a_128, BigFloat::<128>::from(84));
        assert_eq!(a_256.clone() + a_256, BigFloat::<256>::from(84));
    }

    #[test]
    fn test_addition_commutative() {
        let a = BigFloat::<64>::from(3);
        let b = BigFloat::<64>::from(7);
        assert_eq!(a.clone() + b.clone(), b + a);
    }

    #[test]
    fn test_addition_associative() {
        let a = BigFloat::<64>::from(2);
        let b = BigFloat::<64>::from(3);
        let c = BigFloat::<64>::from(5);
        assert_eq!((a.clone() + b.clone()) + c.clone(), a + (b + c));
    }

    #[test]
    fn test_subtraction_inverse_of_addition() {
        let a = BigFloat::<64>::from(10);
        let b = BigFloat::<64>::from(3);
        assert_eq!((a.clone() + b.clone()) - b, a);
    }
}
