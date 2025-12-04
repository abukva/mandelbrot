#![allow(dead_code)]

mod internal;

use internal::Internal;
use std::{
    cmp::Ordering,
    ops::{Add, Div, Mul, Sub},
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

impl<const PRECISION: usize> Mul for BigFloat<PRECISION> {
    type Output = Self;

    fn mul(self, other: Self) -> Self {
        Self(self.0 * other.0)
    }
}

impl<const PRECISION: usize> Div for BigFloat<PRECISION> {
    type Output = Self;

    fn div(self, other: Self) -> Self {
        Self(self.0 / other.0)
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

    fn is_within_ulps_simple<const PRECISION: usize>(
        first: &BigFloat<PRECISION>,
        second: &BigFloat<PRECISION>,
        max_ulps: u64,
    ) -> bool {
        match (&first.0, &second.0) {
            (Internal::NaN, _) | (_, Internal::NaN) => false,
            (Internal::Zero { .. }, Internal::Zero { .. }) => true,
            (Internal::Infinity { sign: s1 }, Internal::Infinity { sign: s2 }) => s1 == s2,
            (Internal::Value(a), Internal::Value(b)) => a.is_within_ulsp(b, max_ulps),
            _ => false,
        }
    }

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

    #[test]
    fn test_mul_simple() {
        let a = BigFloat::<128>::from(3);
        let b = BigFloat::<128>::from(4);
        assert_eq!(a * b, BigFloat::<128>::from(12));
    }

    #[test]
    fn test_mul_with_zero() {
        let a = BigFloat::<128>::from(42);
        let zero = BigFloat::<128>::zero();
        assert_eq!(a.clone() * zero.clone(), BigFloat::<128>::zero());
        assert_eq!(zero * a, BigFloat::<128>::zero());
    }

    #[test]
    fn test_mul_with_one() {
        let a = BigFloat::<128>::from(42);
        let one = BigFloat::<128>::from(1);
        assert_eq!(a.clone() * one, a);
    }

    #[test]
    fn test_mul_with_nan() {
        let a = BigFloat::<128>::from(5);
        let nan = BigFloat::<128>::nan();
        assert!((a * nan).is_nan());
    }

    #[test]
    fn test_mul_with_infinity() {
        let num = BigFloat::<128>::from(5);
        let inf = BigFloat::<128>::infinity();
        let result = num * inf;

        assert_eq!(result, BigFloat::<128>::infinity());
    }

    #[test]
    fn test_mul_zero_with_infinity() {
        let zero = BigFloat::<128>::zero();
        let inf = BigFloat::<128>::infinity();

        assert!((zero * inf).is_nan());
    }

    #[test]
    fn test_mul_infinity_with_infinity() {
        let inf1 = BigFloat::<128>::infinity();
        let inf2 = BigFloat::<128>::infinity();

        assert_eq!(inf1 * inf2, BigFloat::<128>::infinity());
    }

    #[test]
    fn test_mul_negative_infinities() {
        let inf_pos = BigFloat::<128>::infinity();
        let inf_neg = BigFloat::<128>::infinity_negative();

        assert_eq!(inf_pos * inf_neg, BigFloat::<128>::infinity_negative());
    }

    #[test]
    fn test_mul_negative_numbers() {
        let a = BigFloat::<128>::from(-3);
        let b = BigFloat::<128>::from(-4);
        assert_eq!(a * b, BigFloat::<128>::from(12));
    }

    #[test]
    fn test_mul_positive_and_negative() {
        let a = BigFloat::<128>::from(5);
        let b = BigFloat::<128>::from(-7);
        assert_eq!(a * b, BigFloat::<128>::from(-35));
    }

    #[test]
    fn test_mul_negative_and_positive() {
        let a = BigFloat::<128>::from(-6);
        let b = BigFloat::<128>::from(8);
        assert_eq!(a * b, BigFloat::<128>::from(-48));
    }

    #[test]
    fn test_mul_large_numbers() {
        let a = BigFloat::<256>::from(u64::MAX);
        let b = BigFloat::<256>::from(2);
        let result = a * b;

        assert!(!result.is_nan());
    }

    #[test]
    fn test_mul_commutative() {
        let a = BigFloat::<128>::from(7);
        let b = BigFloat::<128>::from(11);
        assert_eq!(a.clone() * b.clone(), b * a);
    }

    #[test]
    fn test_mul_associative() {
        let a = BigFloat::<128>::from(2);
        let b = BigFloat::<128>::from(3);
        let c = BigFloat::<128>::from(5);

        assert_eq!((a.clone() * b.clone()) * c.clone(), a * (b * c));
    }

    #[test]
    fn test_mul_distributive() {
        let a = BigFloat::<128>::from(2);
        let b = BigFloat::<128>::from(3);
        let c = BigFloat::<128>::from(5);

        let left = a.clone() * (b.clone() + c.clone());
        let right = (a.clone() * b) + (a * c);

        assert_eq!(left, right);
    }

    #[test]
    fn test_mul_identity() {
        let a = BigFloat::<128>::from(42);
        let one = BigFloat::<128>::from(1);
        assert_eq!(a.clone() * one, a);
    }

    #[test]
    fn test_mul_zero_property() {
        let a = BigFloat::<128>::from(999);
        let zero = BigFloat::<128>::zero();
        assert_eq!(a * zero, BigFloat::<128>::zero());
    }

    #[test]
    fn test_mul_signs_zero() {
        let pos = BigFloat::<128>::from(5);
        let neg = BigFloat::<128>::from(-5);
        let zero = BigFloat::<128>::zero();

        assert_eq!(pos * zero.clone(), BigFloat::<128>::zero());

        let result = neg * zero;
        assert_eq!(result, BigFloat::<128>::zero());
    }

    #[test]
    fn test_mul_powers_of_two() {
        let a = BigFloat::<128>::from(8);
        let b = BigFloat::<128>::from(16);
        assert_eq!(a * b, BigFloat::<128>::from(128));
    }

    #[test]
    fn test_mul_different_precision() {
        let a_64 = BigFloat::<64>::from(6);
        let b_64 = BigFloat::<64>::from(7);
        assert_eq!(a_64 * b_64, BigFloat::<64>::from(42));

        let a_256 = BigFloat::<256>::from(6);
        let b_256 = BigFloat::<256>::from(7);
        assert_eq!(a_256 * b_256, BigFloat::<256>::from(42));
    }

    #[test]
    fn test_mul_negative_infinity_with_positive() {
        let neg_inf = BigFloat::<128>::infinity_negative();
        let pos = BigFloat::<128>::from(5);

        assert_eq!(neg_inf * pos, BigFloat::<128>::infinity_negative());
    }

    #[test]
    fn test_mul_negative_infinity_with_negative() {
        let neg_inf = BigFloat::<128>::infinity_negative();
        let neg = BigFloat::<128>::from(-5);

        assert_eq!(neg_inf * neg, BigFloat::<128>::infinity());
    }

    #[test]
    fn test_div_simple() {
        let a = BigFloat::<128>::from(12);
        let b = BigFloat::<128>::from(4);
        assert_eq!(a / b, BigFloat::<128>::from(3));
    }

    #[test]
    fn test_div_one_by_one() {
        let a = BigFloat::<128>::from(1);
        let b = BigFloat::<128>::from(1);
        assert_eq!(a / b, BigFloat::<128>::from(1));
    }

    #[test]
    fn test_div_by_one() {
        let a = BigFloat::<128>::from(42);
        let one = BigFloat::<128>::from(1);
        assert_eq!(a.clone() / one, a);
    }

    #[test]
    fn test_div_same_numbers() {
        let a = BigFloat::<128>::from(7);
        let b = BigFloat::<128>::from(7);
        assert_eq!(a / b, BigFloat::<128>::from(1));
    }

    #[test]
    fn test_div_larger_by_smaller() {
        let a = BigFloat::<128>::from(100);
        let b = BigFloat::<128>::from(10);
        assert_eq!(a / b, BigFloat::<128>::from(10));
    }

    #[test]
    fn test_div_zero_by_number() {
        let zero = BigFloat::<128>::zero();
        let a = BigFloat::<128>::from(5);
        assert_eq!(zero / a, BigFloat::<128>::zero());
    }

    #[test]
    fn test_div_by_zero() {
        let a = BigFloat::<128>::from(5);
        let zero = BigFloat::<128>::zero();
        assert_eq!(a / zero, BigFloat::<128>::infinity());
    }

    #[test]
    fn test_div_negative_by_zero() {
        let a = BigFloat::<128>::from(-5);
        let zero = BigFloat::<128>::zero();
        assert_eq!(a / zero, BigFloat::<128>::infinity_negative());
    }

    #[test]
    fn test_div_zero_by_zero() {
        let zero1 = BigFloat::<128>::zero();
        let zero2 = BigFloat::<128>::zero();
        assert!((zero1 / zero2).is_nan());
    }

    #[test]
    fn test_div_with_nan() {
        let a = BigFloat::<128>::from(5);
        let nan = BigFloat::<128>::nan();
        assert!((a / nan).is_nan());
    }

    #[test]
    fn test_div_nan_by_number() {
        let nan = BigFloat::<128>::nan();
        let a = BigFloat::<128>::from(5);
        assert!((nan / a).is_nan());
    }

    #[test]
    fn test_div_nan_by_nan() {
        let nan1 = BigFloat::<128>::nan();
        let nan2 = BigFloat::<128>::nan();
        assert!((nan1 / nan2).is_nan());
    }

    #[test]
    fn test_div_infinity_by_number() {
        let inf = BigFloat::<128>::infinity();
        let a = BigFloat::<128>::from(5);
        assert_eq!(inf / a, BigFloat::<128>::infinity());
    }

    #[test]
    fn test_div_number_by_infinity() {
        let a = BigFloat::<128>::from(5);
        let inf = BigFloat::<128>::infinity();
        assert_eq!(a / inf, BigFloat::<128>::zero());
    }

    #[test]
    fn test_div_infinity_by_infinity() {
        let inf1 = BigFloat::<128>::infinity();
        let inf2 = BigFloat::<128>::infinity();
        assert!((inf1 / inf2).is_nan());
    }

    #[test]
    fn test_div_infinity_by_negative_infinity() {
        let inf_pos = BigFloat::<128>::infinity();
        let inf_neg = BigFloat::<128>::infinity_negative();
        assert!((inf_pos / inf_neg).is_nan());
    }

    #[test]
    fn test_div_negative_infinity_by_number() {
        let inf_neg = BigFloat::<128>::infinity_negative();
        let a = BigFloat::<128>::from(5);
        assert_eq!(inf_neg / a, BigFloat::<128>::infinity_negative());
    }

    #[test]
    fn test_div_negative_infinity_by_negative() {
        let inf_neg = BigFloat::<128>::infinity_negative();
        let a = BigFloat::<128>::from(-5);
        assert_eq!(inf_neg / a, BigFloat::<128>::infinity());
    }

    #[test]
    fn test_div_number_by_negative_infinity() {
        let a = BigFloat::<128>::from(5);
        let inf_neg = BigFloat::<128>::infinity_negative();
        assert_eq!(a / inf_neg, BigFloat::<128>::zero());
    }

    #[test]
    fn test_div_negative_by_positive() {
        let a = BigFloat::<128>::from(-12);
        let b = BigFloat::<128>::from(4);
        assert_eq!(a / b, BigFloat::<128>::from(-3));
    }

    #[test]
    fn test_div_positive_by_negative() {
        let a = BigFloat::<128>::from(12);
        let b = BigFloat::<128>::from(-4);
        assert_eq!(a / b, BigFloat::<128>::from(-3));
    }

    #[test]
    fn test_div_negative_by_negative() {
        let a = BigFloat::<128>::from(-12);
        let b = BigFloat::<128>::from(-4);
        assert_eq!(a / b, BigFloat::<128>::from(3));
    }

    #[test]
    fn test_div_powers_of_two() {
        let a = BigFloat::<128>::from(128);
        let b = BigFloat::<128>::from(8);
        assert_eq!(a / b, BigFloat::<128>::from(16));
    }

    #[test]
    fn test_div_by_power_of_two() {
        let a = BigFloat::<128>::from(64);
        let b = BigFloat::<128>::from(2);
        assert_eq!(a / b, BigFloat::<128>::from(32));
    }

    #[test]
    fn test_div_large_numbers() {
        let a = BigFloat::<256>::from(u64::MAX);
        let b = BigFloat::<256>::from(u64::MAX);
        assert_eq!(a / b, BigFloat::<256>::from(1));
    }

    #[test]
    fn test_div_large_by_small() {
        let a = BigFloat::<128>::from(u64::MAX);
        let b = BigFloat::<128>::from(1);
        assert_eq!(a / b, BigFloat::<128>::from(u64::MAX));
    }

    #[test]
    fn test_div_different_precision() {
        let a_64 = BigFloat::<64>::from(20);
        let b_64 = BigFloat::<64>::from(4);
        assert_eq!(a_64 / b_64, BigFloat::<64>::from(5));

        let a_256 = BigFloat::<256>::from(20);
        let b_256 = BigFloat::<256>::from(4);
        assert_eq!(a_256 / b_256, BigFloat::<256>::from(5));
    }

    #[test]
    fn test_div_inverse_of_mul() {
        let a = BigFloat::<128>::from(6);
        let b = BigFloat::<128>::from(3);
        assert_eq!((a.clone() * b.clone()) / b, a);
    }

    #[test]
    fn test_div_then_mul() {
        let a = BigFloat::<128>::from(12);
        let b = BigFloat::<128>::from(4);
        assert_eq!((a.clone() / b.clone()) * b, a);
    }

    #[test]
    fn test_div_by_self_is_one() {
        let a = BigFloat::<128>::from(42);
        assert_eq!(a.clone() / a, BigFloat::<128>::from(1));
    }

    #[test]
    fn test_div_one_by_number() {
        let one = BigFloat::<128>::from(1);
        let a = BigFloat::<128>::from(4);
        let result = one / a;

        let check = result * BigFloat::<128>::from(4);
        assert_eq!(check, BigFloat::<128>::from(1));
    }

    #[test]
    fn test_div_non_integer_result() {
        let a = BigFloat::<128>::from(3);
        let b = BigFloat::<128>::from(2);
        let result = a.clone() / b.clone();

        assert_eq!(result * b, a);
    }

    #[test]
    fn test_div_one_by_two() {
        let one = BigFloat::<128>::from(1);
        let two = BigFloat::<128>::from(2);
        let half = one.clone() / two.clone();

        assert_eq!(half * two, one);
    }

    #[test]
    fn test_div_chain() {
        let a = BigFloat::<128>::from(24);
        let two = BigFloat::<128>::from(2);
        let three = BigFloat::<128>::from(3);

        let result = ((a / two.clone()) / three) / two;
        assert_eq!(result, BigFloat::<128>::from(2));
    }

    #[test]
    fn test_div_distributive_over_addition() {
        let a = BigFloat::<128>::from(12);
        let b = BigFloat::<128>::from(8);
        let c = BigFloat::<128>::from(4);

        let left = (a.clone() + b.clone()) / c.clone();
        let right = (a / c.clone()) + (b / c);

        assert_eq!(left, right);
    }

    #[test]
    fn test_div_small_by_large() {
        let a = BigFloat::<128>::from(1);
        let b = BigFloat::<128>::from(1000);
        let result = a / b;

        let check = result * BigFloat::<128>::from(1000);
        assert_eq!(check, BigFloat::<128>::from(1));
    }

    #[test]
    fn test_div_exact_cases() {
        assert_eq!(
            BigFloat::<128>::from(12) / BigFloat::<128>::from(4) * BigFloat::<128>::from(4),
            BigFloat::<128>::from(12)
        );
        assert_eq!(
            BigFloat::<128>::from(100) / BigFloat::<128>::from(10) * BigFloat::<128>::from(10),
            BigFloat::<128>::from(100)
        );
    }

    #[test]
    fn test_div_one_by_three_times_three() {
        let one = BigFloat::<128>::from(1);
        let three = BigFloat::<128>::from(3);
        let result = (one.clone() / three.clone()) * three;

        assert!(
            is_within_ulps_simple(&result, &one, 1),
            "Expected within 1 ULP: result={:?}, expected={:?}",
            result,
            one
        );
    }
}
