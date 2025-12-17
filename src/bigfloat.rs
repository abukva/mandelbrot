mod internal;

use internal::Internal;
use std::{
    cmp::Ordering,
    ops::{Add, Div, Mul, Sub},
};

#[derive(Debug, Clone, Copy)]
pub struct BigFloat<const LIMBS: usize>(Internal<LIMBS>);

impl<const LIMBS: usize> BigFloat<LIMBS> {
    pub fn zero() -> Self {
        Self(Internal::<LIMBS>::Zero { sign: false })
    }

    pub fn zero_negative(sign: bool) -> Self {
        Self(Internal::<LIMBS>::Zero { sign })
    }

    pub fn infinity() -> Self {
        Self(Internal::<LIMBS>::Infinity { sign: false })
    }

    pub fn infinity_negative() -> Self {
        Self(Internal::Infinity { sign: true })
    }

    pub fn nan() -> Self {
        Self(Internal::<LIMBS>::NaN)
    }

    pub fn is_nan(&self) -> bool {
        matches!(self.0, Internal::NaN)
    }

    pub fn parse(text: &str) -> Self {
        Self(Internal::parse(text))
    }

    pub fn powi(&self, exponenet: i64) -> Self {
        Self(self.0.powi(exponenet))
    }
}

// Operations with standard types

// Add
// F64
impl<const LIMBS: usize> Add<f64> for BigFloat<LIMBS> {
    type Output = Self;

    fn add(self, other: f64) -> Self {
        self + BigFloat::<LIMBS>::from(other)
    }
}

// U64
impl<const LIMBS: usize> Add<u64> for BigFloat<LIMBS> {
    type Output = Self;

    fn add(self, other: u64) -> Self {
        self + BigFloat::<LIMBS>::from(other)
    }
}

// Sub
// F64
impl<const LIMBS: usize> Sub<f64> for BigFloat<LIMBS> {
    type Output = Self;

    fn sub(self, other: f64) -> Self {
        self - BigFloat::<LIMBS>::from(other)
    }
}

// U64
impl<const LIMBS: usize> Sub<u64> for BigFloat<LIMBS> {
    type Output = Self;

    fn sub(self, other: u64) -> Self {
        self - BigFloat::<LIMBS>::from(other)
    }
}

// Mul
// F64
impl<const LIMBS: usize> Mul<f64> for BigFloat<LIMBS> {
    type Output = Self;

    fn mul(self, other: f64) -> Self {
        self * BigFloat::<LIMBS>::from(other)
    }
}

// U64
impl<const LIMBS: usize> Mul<u64> for BigFloat<LIMBS> {
    type Output = Self;

    fn mul(self, other: u64) -> Self {
        self * BigFloat::<LIMBS>::from(other)
    }
}

// Div
// F64
impl<const LIMBS: usize> Div<f64> for BigFloat<LIMBS> {
    type Output = Self;

    fn div(self, other: f64) -> Self {
        self / BigFloat::<LIMBS>::from(other)
    }
}

// U64
impl<const LIMBS: usize> Div<u64> for BigFloat<LIMBS> {
    type Output = Self;

    fn div(self, other: u64) -> Self {
        self / BigFloat::<LIMBS>::from(other)
    }
}

impl<const LIMBS: usize> Add for BigFloat<LIMBS> {
    type Output = Self;

    #[inline]
    fn add(self, other: Self) -> Self {
        Self(self.0 + other.0)
    }
}

impl<const LIMBS: usize> Sub for BigFloat<LIMBS> {
    type Output = Self;

    #[inline]
    fn sub(self, other: Self) -> Self {
        Self(self.0 - other.0)
    }
}

impl<const LIMBS: usize> Mul for BigFloat<LIMBS> {
    type Output = Self;

    #[inline]
    fn mul(self, other: Self) -> Self {
        Self(self.0 * other.0)
    }
}

impl<const LIMBS: usize> Div for BigFloat<LIMBS> {
    type Output = Self;

    #[inline]
    fn div(self, other: Self) -> Self {
        Self(self.0 / other.0)
    }
}

impl<const LIMBS: usize> PartialEq for BigFloat<LIMBS> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl<const LIMBS: usize> PartialEq<f64> for BigFloat<LIMBS> {
    #[inline]
    fn eq(&self, other: &f64) -> bool {
        self.0 == Internal::from(*other)
    }
}

impl<const LIMBS: usize> PartialOrd for BigFloat<LIMBS> {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.0.partial_cmp(&other.0)
    }
}

impl<const LIMBS: usize> PartialOrd<f64> for BigFloat<LIMBS> {
    #[inline]
    fn partial_cmp(&self, other: &f64) -> Option<Ordering> {
        self.0.partial_cmp(&Internal::from(*other))
    }
}

impl<const LIMBS: usize> From<u64> for BigFloat<LIMBS> {
    #[inline]
    fn from(value: u64) -> Self {
        Self(Internal::from(value))
    }
}

impl<const LIMBS: usize> From<i64> for BigFloat<LIMBS> {
    #[inline]
    fn from(value: i64) -> Self {
        Self(Internal::from(value))
    }
}

impl<const LIMBS: usize> From<u32> for BigFloat<LIMBS> {
    #[inline]
    fn from(value: u32) -> Self {
        Self::from(value as u64)
    }
}

impl<const LIMBS: usize> From<i32> for BigFloat<LIMBS> {
    #[inline]
    fn from(value: i32) -> Self {
        Self::from(value as i64)
    }
}

impl<const LIMBS: usize> From<f64> for BigFloat<LIMBS> {
    #[inline]
    fn from(value: f64) -> Self {
        Self(Internal::from(value))
    }
}

impl<const LIMBS: usize> From<f32> for BigFloat<LIMBS> {
    #[inline]
    fn from(value: f32) -> Self {
        Self::from(value as f64)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    type BF = BigFloat<2>;

    fn are_same<const LIMBS: usize>(a: &BigFloat<LIMBS>, b: &BigFloat<LIMBS>) {
        let diff = if a > b { *a - *b } else { *b - *a };

        let epsilon = BigFloat::<LIMBS>::from(1e-10);

        assert!(
            diff < epsilon,
            "Expected very close: result={:?}, diff={:?}",
            a,
            b
        );
    }

    #[test]
    fn test_subtract_larger_from_smaller() {
        let a = BigFloat::<1>::from(1);
        let b = BigFloat::<1>::from(2);
        let result = a - b;
        assert_eq!(result, BigFloat::<1>::from(-1))
    }

    #[test]
    fn test_subtract_same_numbers() {
        let a = BigFloat::<1>::from(5);
        let b = BigFloat::<1>::from(5);
        assert_eq!(a - b, BigFloat::<1>::zero());
    }

    #[test]
    fn test_subtract_with_zero() {
        let a = BigFloat::<1>::from(5);
        let zero = BigFloat::<1>::zero();
        assert_eq!(a - zero, a);
    }

    #[test]
    fn test_subtract_with_nan() {
        let a = BigFloat::<1>::from(5);
        let nan = BigFloat::<1>::nan();
        assert!((a - nan).is_nan());
    }

    #[test]
    fn test_subtract_with_infinity() {
        let one = BigFloat::<2>::from(1);
        let inf = BigFloat::<2>::infinity();
        let inf_neg = BigFloat::<2>::infinity_negative();

        assert_eq!(one - inf, inf_neg);
        assert_eq!(one - inf_neg, inf);
    }

    #[test]
    fn test_subtract_infinity_from_infinity() {
        let inf = BigFloat::<2>::infinity();
        assert!((inf - inf).is_nan());
    }

    #[test]
    fn test_add_negative_numbers() {
        let a = BigFloat::<1>::from(-2);
        let b = BigFloat::<1>::from(-3);
        assert_eq!(a + b, BigFloat::<1>::from(-5));
    }

    #[test]
    fn test_add_positive_and_negative() {
        let a = BigFloat::<1>::from(5);
        let b = BigFloat::<1>::from(-3);
        assert_eq!(a + b, BigFloat::<1>::from(2));
    }

    #[test]
    fn test_add_negative_and_positive() {
        let a = BigFloat::<1>::from(-5);
        let b = BigFloat::<1>::from(3);
        assert_eq!(a + b, BigFloat::<1>::from(-2));
    }

    #[test]
    fn test_infinity_plus_infinity_same_sign() {
        let inf = BigFloat::<2>::infinity();
        assert_eq!(inf + inf, inf);

        let neg_inf = BigFloat::<2>::infinity_negative();
        assert_eq!(neg_inf + neg_inf, neg_inf);
    }

    #[test]
    fn test_infinity_plus_infinity_opposite_sign() {
        let inf = BigFloat::<2>::infinity();
        let neg_inf = BigFloat::<2>::infinity_negative();
        assert!((inf + neg_inf).is_nan());
    }

    #[test]
    fn test_nan_equality() {
        let nan1 = BigFloat::<2>::nan();
        let nan2 = BigFloat::<2>::nan();
        assert_ne!(nan1, nan2);
    }

    #[test]
    fn test_zero_with_different_signs() {
        let zero_pos = BigFloat::<2>::zero();
        let zero_neg = BigFloat::<2>::zero_negative(true);
        assert_eq!(zero_pos, zero_neg);
    }

    #[test]
    fn test_comparison_with_nan() {
        let a = BigFloat::<1>::from(5);
        let nan = BigFloat::<1>::nan();
        assert_eq!(a.partial_cmp(&nan), None);
        assert_eq!(nan.partial_cmp(&a), None);
    }

    #[test]
    fn test_comparison_basic() {
        let a = BigFloat::<1>::from(5);
        let b = BigFloat::<1>::from(10);
        assert!(a < b);
        assert!(b > a);
    }

    #[test]
    fn test_comparison_with_infinity() {
        let num = BigFloat::<1>::from(1000000);
        let inf = BigFloat::<1>::infinity();
        let neg_inf = BigFloat::<1>::infinity_negative();

        assert!(num < inf);
        assert!(num > neg_inf);
    }

    #[test]
    fn test_comparison_with_zero() {
        let positive = BigFloat::<1>::from(5);
        let negative = BigFloat::<1>::from(-5);
        let zero = BigFloat::<1>::zero();

        assert!(positive > zero);
        assert!(negative < zero);
    }

    #[test]
    fn test_add_large_numbers() {
        let a = BigFloat::<2>::from(u64::MAX);
        let b = BigFloat::<2>::from(u64::MAX);
        let result = a + b;
        assert!(!result.is_nan());
    }

    #[test]
    fn test_max_values() {
        let max_u64 = BigFloat::<1>::from(u64::MAX);
        let one = BigFloat::<1>::from(1);
        let result = max_u64 + one;
        assert!(!result.is_nan());
    }

    #[test]
    fn test_different_precision_values() {
        let a_64 = BigFloat::<1>::from(42);
        let a_128 = BigFloat::<2>::from(42);
        let a_256 = BigFloat::<4>::from(42);

        assert_eq!(a_64 + a_64, BigFloat::<1>::from(84));
        assert_eq!(a_128 + a_128, BigFloat::<2>::from(84));
        assert_eq!(a_256 + a_256, BigFloat::<4>::from(84));
    }

    #[test]
    fn test_addition_commutative() {
        let a = BigFloat::<1>::from(3);
        let b = BigFloat::<1>::from(7);
        assert_eq!(a + b, b + a);
    }

    #[test]
    fn test_addition_associative() {
        let a = BigFloat::<1>::from(2);
        let b = BigFloat::<1>::from(3);
        let c = BigFloat::<1>::from(5);
        assert_eq!((a + b) + c, a + (b + c));
    }

    #[test]
    fn test_subtraction_inverse_of_addition() {
        let a = BigFloat::<1>::from(10);
        let b = BigFloat::<1>::from(3);
        assert_eq!((a + b) - b, a);
    }

    #[test]
    fn test_mul_simple() {
        let a = BigFloat::<2>::from(3);
        let b = BigFloat::<2>::from(4);
        assert_eq!(a * b, BigFloat::<2>::from(12));
    }

    #[test]
    fn test_mul_with_zero() {
        let a = BigFloat::<2>::from(42);
        let zero = BigFloat::<2>::zero();
        assert_eq!(a * zero, BigFloat::<2>::zero());
        assert_eq!(zero * a, BigFloat::<2>::zero());
    }

    #[test]
    fn test_mul_with_one() {
        let a = BigFloat::<2>::from(42);
        let one = BigFloat::<2>::from(1);
        assert_eq!(a * one, a);
    }

    #[test]
    fn test_mul_with_nan() {
        let a = BigFloat::<2>::from(5);
        let nan = BigFloat::<2>::nan();
        assert!((a * nan).is_nan());
    }

    #[test]
    fn test_mul_with_infinity() {
        let num = BigFloat::<2>::from(5);
        let inf = BigFloat::<2>::infinity();
        let result = num * inf;

        assert_eq!(result, BigFloat::<2>::infinity());
    }

    #[test]
    fn test_mul_zero_with_infinity() {
        let zero = BigFloat::<2>::zero();
        let inf = BigFloat::<2>::infinity();

        assert!((zero * inf).is_nan());
    }

    #[test]
    fn test_mul_infinity_with_infinity() {
        let inf1 = BigFloat::<2>::infinity();
        let inf2 = BigFloat::<2>::infinity();

        assert_eq!(inf1 * inf2, BigFloat::<2>::infinity());
    }

    #[test]
    fn test_mul_negative_infinities() {
        let inf_pos = BigFloat::<2>::infinity();
        let inf_neg = BigFloat::<2>::infinity_negative();

        assert_eq!(inf_pos * inf_neg, BigFloat::<2>::infinity_negative());
    }

    #[test]
    fn test_mul_negative_numbers() {
        let a = BigFloat::<2>::from(-3);
        let b = BigFloat::<2>::from(-4);
        assert_eq!(a * b, BigFloat::<2>::from(12));
    }

    #[test]
    fn test_mul_positive_and_negative() {
        let a = BigFloat::<2>::from(5);
        let b = BigFloat::<2>::from(-7);
        assert_eq!(a * b, BigFloat::<2>::from(-35));
    }

    #[test]
    fn test_mul_negative_and_positive() {
        let a = BigFloat::<2>::from(-6);
        let b = BigFloat::<2>::from(8);
        assert_eq!(a * b, BigFloat::<2>::from(-48));
    }

    #[test]
    fn test_mul_large_numbers() {
        let a = BigFloat::<4>::from(u64::MAX);
        let b = BigFloat::<4>::from(2);
        let result = a * b;

        assert!(!result.is_nan());
    }

    #[test]
    fn test_mul_commutative() {
        let a = BigFloat::<2>::from(7);
        let b = BigFloat::<2>::from(11);
        assert_eq!(a * b, b * a);
    }

    #[test]
    fn test_mul_associative() {
        let a = BigFloat::<2>::from(2);
        let b = BigFloat::<2>::from(3);
        let c = BigFloat::<2>::from(5);

        assert_eq!((a * b) * c, a * (b * c));
    }

    #[test]
    fn test_mul_distributive() {
        let a = BigFloat::<2>::from(2);
        let b = BigFloat::<2>::from(3);
        let c = BigFloat::<2>::from(5);

        let left = a * (b + c);
        let right = (a * b) + (a * c);

        assert_eq!(left, right);
    }

    #[test]
    fn test_mul_identity() {
        let a = BigFloat::<2>::from(42);
        let one = BigFloat::<2>::from(1);
        assert_eq!(a * one, a);
    }

    #[test]
    fn test_mul_zero_property() {
        let a = BigFloat::<2>::from(999);
        let zero = BigFloat::<2>::zero();
        assert_eq!(a * zero, BigFloat::<2>::zero());
    }

    #[test]
    fn test_mul_signs_zero() {
        let pos = BigFloat::<2>::from(5);
        let neg = BigFloat::<2>::from(-5);
        let zero = BigFloat::<2>::zero();

        assert_eq!(pos * zero, BigFloat::<2>::zero());

        let result = neg * zero;
        assert_eq!(result, BigFloat::<2>::zero());
    }

    #[test]
    fn test_mul_powers_of_two() {
        let a = BigFloat::<2>::from(8);
        let b = BigFloat::<2>::from(16);
        assert_eq!(a * b, BigFloat::<2>::from(128));
    }

    #[test]
    fn test_mul_different_precision() {
        let a_64 = BigFloat::<1>::from(6);
        let b_64 = BigFloat::<1>::from(7);
        assert_eq!(a_64 * b_64, BigFloat::<1>::from(42));

        let a_256 = BigFloat::<4>::from(6);
        let b_256 = BigFloat::<4>::from(7);
        assert_eq!(a_256 * b_256, BigFloat::<4>::from(42));
    }

    #[test]
    fn test_mul_negative_infinity_with_positive() {
        let neg_inf = BigFloat::<2>::infinity_negative();
        let pos = BigFloat::<2>::from(5);

        assert_eq!(neg_inf * pos, BigFloat::<2>::infinity_negative());
    }

    #[test]
    fn test_mul_negative_infinity_with_negative() {
        let neg_inf = BigFloat::<2>::infinity_negative();
        let neg = BigFloat::<2>::from(-5);

        assert_eq!(neg_inf * neg, BigFloat::<2>::infinity());
    }

    #[test]
    fn test_div_simple() {
        let a = BigFloat::<2>::from(12);
        let b = BigFloat::<2>::from(4);
        assert_eq!(a / b, BigFloat::<2>::from(3));
    }

    #[test]
    fn test_div_one_by_one() {
        let a = BigFloat::<2>::from(1);
        let b = BigFloat::<2>::from(1);
        assert_eq!(a / b, BigFloat::<2>::from(1));
    }

    #[test]
    fn test_div_by_one() {
        let a = BigFloat::<2>::from(42);
        let one = BigFloat::<2>::from(1);
        assert_eq!(a / one, a);
    }

    #[test]
    fn test_div_same_numbers() {
        let a = BigFloat::<2>::from(7);
        let b = BigFloat::<2>::from(7);
        assert_eq!(a / b, BigFloat::<2>::from(1));
    }

    #[test]
    fn test_div_larger_by_smaller() {
        let a = BigFloat::<2>::from(100);
        let b = BigFloat::<2>::from(10);
        assert_eq!(a / b, BigFloat::<2>::from(10));
    }

    #[test]
    fn test_div_zero_by_number() {
        let zero = BigFloat::<2>::zero();
        let a = BigFloat::<2>::from(5);
        assert_eq!(zero / a, BigFloat::<2>::zero());
    }

    #[test]
    fn test_div_by_zero() {
        let a = BigFloat::<2>::from(5);
        let zero = BigFloat::<2>::zero();
        assert_eq!(a / zero, BigFloat::<2>::infinity());
    }

    #[test]
    fn test_div_negative_by_zero() {
        let a = BigFloat::<2>::from(-5);
        let zero = BigFloat::<2>::zero();
        assert_eq!(a / zero, BigFloat::<2>::infinity_negative());
    }

    #[test]
    fn test_div_zero_by_zero() {
        let zero1 = BigFloat::<2>::zero();
        let zero2 = BigFloat::<2>::zero();
        assert!((zero1 / zero2).is_nan());
    }

    #[test]
    fn test_div_with_nan() {
        let a = BigFloat::<2>::from(5);
        let nan = BigFloat::<2>::nan();
        assert!((a / nan).is_nan());
    }

    #[test]
    fn test_div_nan_by_number() {
        let nan = BigFloat::<2>::nan();
        let a = BigFloat::<2>::from(5);
        assert!((nan / a).is_nan());
    }

    #[test]
    fn test_div_nan_by_nan() {
        let nan1 = BigFloat::<2>::nan();
        let nan2 = BigFloat::<2>::nan();
        assert!((nan1 / nan2).is_nan());
    }

    #[test]
    fn test_div_infinity_by_number() {
        let inf = BigFloat::<2>::infinity();
        let a = BigFloat::<2>::from(5);
        assert_eq!(inf / a, BigFloat::<2>::infinity());
    }

    #[test]
    fn test_div_number_by_infinity() {
        let a = BigFloat::<2>::from(5);
        let inf = BigFloat::<2>::infinity();
        assert_eq!(a / inf, BigFloat::<2>::zero());
    }

    #[test]
    fn test_div_infinity_by_infinity() {
        let inf1 = BigFloat::<2>::infinity();
        let inf2 = BigFloat::<2>::infinity();
        assert!((inf1 / inf2).is_nan());
    }

    #[test]
    fn test_div_infinity_by_negative_infinity() {
        let inf_pos = BigFloat::<2>::infinity();
        let inf_neg = BigFloat::<2>::infinity_negative();
        assert!((inf_pos / inf_neg).is_nan());
    }

    #[test]
    fn test_div_negative_infinity_by_number() {
        let inf_neg = BigFloat::<2>::infinity_negative();
        let a = BigFloat::<2>::from(5);
        assert_eq!(inf_neg / a, BigFloat::<2>::infinity_negative());
    }

    #[test]
    fn test_div_negative_infinity_by_negative() {
        let inf_neg = BigFloat::<2>::infinity_negative();
        let a = BigFloat::<2>::from(-5);
        assert_eq!(inf_neg / a, BigFloat::<2>::infinity());
    }

    #[test]
    fn test_div_number_by_negative_infinity() {
        let a = BigFloat::<2>::from(5);
        let inf_neg = BigFloat::<2>::infinity_negative();
        assert_eq!(a / inf_neg, BigFloat::<2>::zero());
    }

    #[test]
    fn test_div_negative_by_positive() {
        let a = BigFloat::<2>::from(-12);
        let b = BigFloat::<2>::from(4);
        assert_eq!(a / b, BigFloat::<2>::from(-3));
    }

    #[test]
    fn test_div_positive_by_negative() {
        let a = BigFloat::<2>::from(12);
        let b = BigFloat::<2>::from(-4);
        assert_eq!(a / b, BigFloat::<2>::from(-3));
    }

    #[test]
    fn test_div_negative_by_negative() {
        let a = BigFloat::<2>::from(-12);
        let b = BigFloat::<2>::from(-4);
        assert_eq!(a / b, BigFloat::<2>::from(3));
    }

    #[test]
    fn test_div_powers_of_two() {
        let a = BigFloat::<2>::from(128);
        let b = BigFloat::<2>::from(8);
        assert_eq!(a / b, BigFloat::<2>::from(16));
    }

    #[test]
    fn test_div_by_power_of_two() {
        let a = BigFloat::<2>::from(64);
        let b = BigFloat::<2>::from(2);
        assert_eq!(a / b, BigFloat::<2>::from(32));
    }

    #[test]
    fn test_div_large_numbers() {
        let a = BigFloat::<4>::from(u64::MAX);
        let b = BigFloat::<4>::from(u64::MAX);
        assert_eq!(a / b, BigFloat::<4>::from(1));
    }

    #[test]
    fn test_div_large_by_small() {
        let a = BigFloat::<2>::from(u64::MAX);
        let b = BigFloat::<2>::from(1);
        assert_eq!(a / b, BigFloat::<2>::from(u64::MAX));
    }

    #[test]
    fn test_div_different_precision() {
        let a_64 = BigFloat::<1>::from(20);
        let b_64 = BigFloat::<1>::from(4);
        assert_eq!(a_64 / b_64, BigFloat::<1>::from(5));

        let a_256 = BigFloat::<4>::from(20);
        let b_256 = BigFloat::<4>::from(4);
        assert_eq!(a_256 / b_256, BigFloat::<4>::from(5));
    }

    #[test]
    fn test_div_inverse_of_mul() {
        let a = BigFloat::<2>::from(6);
        let b = BigFloat::<2>::from(3);
        assert_eq!((a * b) / b, a);
    }

    #[test]
    fn test_div_then_mul() {
        let a = BigFloat::<2>::from(12);
        let b = BigFloat::<2>::from(4);
        assert_eq!((a / b) * b, a);
    }

    #[test]
    fn test_div_by_self_is_one() {
        let a = BigFloat::<2>::from(42);
        assert_eq!(a / a, BigFloat::<2>::from(1));
    }

    #[test]
    fn test_div_one_by_number() {
        let one = BigFloat::<2>::from(1);
        let a = BigFloat::<2>::from(4);
        let result = one / a;

        let check = result * BigFloat::<2>::from(4);
        assert_eq!(check, BigFloat::<2>::from(1));
    }

    #[test]
    fn test_div_non_integer_result() {
        let a = BigFloat::<2>::from(3);
        let b = BigFloat::<2>::from(2);
        let result = a / b;

        assert_eq!(result * b, a);
    }

    #[test]
    fn test_div_one_by_two() {
        let one = BigFloat::<2>::from(1);
        let two = BigFloat::<2>::from(2);
        let half = one / two;

        assert_eq!(half * two, one);
    }

    #[test]
    fn test_div_chain() {
        let a = BigFloat::<2>::from(24);
        let two = BigFloat::<2>::from(2);
        let three = BigFloat::<2>::from(3);

        let result = ((a / two) / three) / two;
        assert_eq!(result, BigFloat::<2>::from(2));
    }

    #[test]
    fn test_div_distributive_over_addition() {
        let a = BigFloat::<2>::from(12);
        let b = BigFloat::<2>::from(8);
        let c = BigFloat::<2>::from(4);

        let left = (a + b) / c;
        let right = (a / c) + (b / c);

        assert_eq!(left, right);
    }

    #[test]
    fn test_div_small_by_large() {
        let a = BigFloat::<2>::from(1);
        let b = BigFloat::<2>::from(1000);
        let result = a / b;

        let check = result * BigFloat::<2>::from(1000);
        assert_eq!(check, BigFloat::<2>::from(1));
    }

    #[test]
    fn test_div_exact_cases() {
        assert_eq!(
            BigFloat::<2>::from(12) / BigFloat::<2>::from(4) * BigFloat::<2>::from(4),
            BigFloat::<2>::from(12)
        );
        assert_eq!(
            BigFloat::<2>::from(100) / BigFloat::<2>::from(10) * BigFloat::<2>::from(10),
            BigFloat::<2>::from(100)
        );
    }

    #[test]
    fn test_div_one_by_three_times_three() {
        let one = BigFloat::<2>::from(1);
        let three = BigFloat::<2>::from(3);
        let result = (one / three) * three;

        are_same(&result, &one);
    }

    #[test]
    fn test_powi_nan_propagation() {
        let nan = BF::nan();

        assert!(nan.powi(0).is_nan());
        assert!(nan.powi(5).is_nan());
        assert!(nan.powi(-5).is_nan());
        assert!(nan.powi(100).is_nan());
    }

    #[test]
    fn test_powi_exponent_zero() {
        assert_eq!(BF::from(5).powi(0), BF::from(1));
        assert_eq!(BF::from(-5).powi(0), BF::from(1));
        assert_eq!(BF::from(0).powi(0), BF::from(1));
        assert_eq!(BF::zero().powi(0), BF::from(1));
        assert_eq!(BF::zero_negative(true).powi(0), BF::from(1));
        assert_eq!(BF::infinity().powi(0), BF::from(1));
        assert_eq!(BF::infinity_negative().powi(0), BF::from(1));
    }

    #[test]
    fn test_powi_base_one() {
        let one = BF::from(1);

        assert_eq!(one.powi(0), BF::from(1));
        assert_eq!(one.powi(1), BF::from(1));
        assert_eq!(one.powi(100), BF::from(1));
        assert_eq!(one.powi(-100), BF::from(1));
        assert_eq!(one.powi(12345), BF::from(1));
    }

    #[test]
    fn test_powi_zero_base_positive_odd_exponent() {
        assert_eq!(BF::zero().powi(1), BF::zero());
        assert_eq!(BF::zero().powi(3), BF::zero());
        assert_eq!(BF::zero().powi(5), BF::zero());
        assert_eq!(BF::zero().powi(99), BF::zero());

        assert_eq!(BF::zero_negative(true).powi(1), BF::zero_negative(true));
        assert_eq!(BF::zero_negative(true).powi(3), BF::zero_negative(true));
        assert_eq!(BF::zero_negative(true).powi(5), BF::zero_negative(true));
    }

    #[test]
    fn test_powi_zero_base_positive_even_exponent() {
        assert_eq!(BF::zero().powi(2), BF::zero());
        assert_eq!(BF::zero().powi(4), BF::zero());
        assert_eq!(BF::zero().powi(100), BF::zero());

        assert_eq!(BF::zero_negative(true).powi(2), BF::zero());
        assert_eq!(BF::zero_negative(true).powi(4), BF::zero());
        assert_eq!(BF::zero_negative(true).powi(100), BF::zero());
    }

    #[test]
    fn test_powi_zero_base_negative_odd_exponent() {
        assert_eq!(BF::zero().powi(-1), BF::infinity());
        assert_eq!(BF::zero().powi(-3), BF::infinity());
        assert_eq!(BF::zero().powi(-5), BF::infinity());
        assert_eq!(BF::zero().powi(-99), BF::infinity());

        assert_eq!(BF::zero_negative(true).powi(-1), BF::infinity_negative());
        assert_eq!(BF::zero_negative(true).powi(-3), BF::infinity_negative());
        assert_eq!(BF::zero_negative(true).powi(-5), BF::infinity_negative());
    }

    #[test]
    fn test_powi_zero_base_negative_even_exponent() {
        assert_eq!(BF::zero().powi(-2), BF::infinity());
        assert_eq!(BF::zero().powi(-4), BF::infinity());
        assert_eq!(BF::zero().powi(-100), BF::infinity());

        assert_eq!(BF::zero_negative(true).powi(-2), BF::infinity());
        assert_eq!(BF::zero_negative(true).powi(-4), BF::infinity());
        assert_eq!(BF::zero_negative(true).powi(-100), BF::infinity());
    }

    #[test]
    fn test_powi_positive_infinity_positive_exponent() {
        assert_eq!(BF::infinity().powi(1), BF::infinity());
        assert_eq!(BF::infinity().powi(2), BF::infinity());
        assert_eq!(BF::infinity().powi(3), BF::infinity());
        assert_eq!(BF::infinity().powi(100), BF::infinity());
    }

    #[test]
    fn test_powi_positive_infinity_negative_exponent() {
        assert_eq!(BF::infinity().powi(-1), BF::zero());
        assert_eq!(BF::infinity().powi(-2), BF::zero());
        assert_eq!(BF::infinity().powi(-3), BF::zero());
        assert_eq!(BF::infinity().powi(-100), BF::zero());
    }

    #[test]
    fn test_powi_negative_infinity_positive_odd_exponent() {
        assert_eq!(BF::infinity_negative().powi(1), BF::infinity_negative());
        assert_eq!(BF::infinity_negative().powi(3), BF::infinity_negative());
        assert_eq!(BF::infinity_negative().powi(5), BF::infinity_negative());
        assert_eq!(BF::infinity_negative().powi(99), BF::infinity_negative());
    }

    #[test]
    fn test_powi_negative_infinity_positive_even_exponent() {
        assert_eq!(BF::infinity_negative().powi(2), BF::infinity());
        assert_eq!(BF::infinity_negative().powi(4), BF::infinity());
        assert_eq!(BF::infinity_negative().powi(6), BF::infinity());
        assert_eq!(BF::infinity_negative().powi(100), BF::infinity());
    }

    #[test]
    fn test_powi_negative_infinity_negative_odd_exponent() {
        assert_eq!(BF::infinity_negative().powi(-1), BF::zero_negative(true));
        assert_eq!(BF::infinity_negative().powi(-3), BF::zero_negative(true));
        assert_eq!(BF::infinity_negative().powi(-5), BF::zero_negative(true));
        assert_eq!(BF::infinity_negative().powi(-99), BF::zero_negative(true));
    }

    #[test]
    fn test_powi_negative_infinity_negative_even_exponent() {
        assert_eq!(BF::infinity_negative().powi(-2), BF::zero());
        assert_eq!(BF::infinity_negative().powi(-4), BF::zero());
        assert_eq!(BF::infinity_negative().powi(-6), BF::zero());
        assert_eq!(BF::infinity_negative().powi(-100), BF::zero());
    }

    #[test]
    fn test_powi_positive_base_positive_exponent() {
        assert_eq!(BF::from(2).powi(1), BF::from(2));
        assert_eq!(BF::from(2).powi(2), BF::from(4));
        assert_eq!(BF::from(2).powi(3), BF::from(8));
        assert_eq!(BF::from(2).powi(4), BF::from(16));
        assert_eq!(BF::from(2).powi(10), BF::from(1024));

        assert_eq!(BF::from(3).powi(2), BF::from(9));
        assert_eq!(BF::from(3).powi(3), BF::from(27));
        assert_eq!(BF::from(3).powi(4), BF::from(81));

        assert_eq!(BF::from(5).powi(2), BF::from(25));
        assert_eq!(BF::from(5).powi(3), BF::from(125));

        assert_eq!(BF::from(10).powi(3), BF::from(1000));
        assert_eq!(BF::from(10).powi(6), BF::from(1_000_000));
    }

    #[test]
    fn test_powi_negative_base_odd_exponent() {
        assert_eq!(BF::from(-2).powi(1), BF::from(-2));
        assert_eq!(BF::from(-2).powi(3), BF::from(-8));
        assert_eq!(BF::from(-2).powi(5), BF::from(-32));

        assert_eq!(BF::from(-3).powi(3), BF::from(-27));
        assert_eq!(BF::from(-5).powi(3), BF::from(-125));
    }

    #[test]
    fn test_powi_negative_base_even_exponent() {
        assert_eq!(BF::from(-2).powi(2), BF::from(4));
        assert_eq!(BF::from(-2).powi(4), BF::from(16));
        assert_eq!(BF::from(-2).powi(6), BF::from(64));

        assert_eq!(BF::from(-3).powi(2), BF::from(9));
        assert_eq!(BF::from(-5).powi(2), BF::from(25));
        assert_eq!(BF::from(-10).powi(2), BF::from(100));
    }

    #[test]
    fn test_powi_negative_one_special_case() {
        assert_eq!(BF::from(-1).powi(2), BF::from(1));
        assert_eq!(BF::from(-1).powi(4), BF::from(1));
        assert_eq!(BF::from(-1).powi(100), BF::from(1));
        assert_eq!(BF::from(-1).powi(1000), BF::from(1));

        assert_eq!(BF::from(-1).powi(1), BF::from(-1));
        assert_eq!(BF::from(-1).powi(3), BF::from(-1));
        assert_eq!(BF::from(-1).powi(99), BF::from(-1));
        assert_eq!(BF::from(-1).powi(999), BF::from(-1));
    }

    #[test]
    fn test_powi_large_exponents() {
        assert_eq!(BF::from(2).powi(20), BF::from(1_048_576));
        assert_eq!(BF::from(2).powi(30), BF::from(1_073_741_824));

        assert_eq!(BF::from(3).powi(10), BF::from(59_049));
    }

    #[test]
    fn test_powi_exponent_one() {
        assert_eq!(BF::from(5).powi(1), BF::from(5));
        assert_eq!(BF::from(-7).powi(1), BF::from(-7));
        assert_eq!(BF::from(100).powi(1), BF::from(100));
        assert_eq!(BF::from(-999).powi(1), BF::from(-999));
    }

    #[test]
    fn test_powi_negative_exponents() {
        let result = BF::from(2).powi(-1);
        let expected = BF::from(1) / BF::from(2);
        assert_eq!(result, expected);

        let result = BF::from(2).powi(-2);
        let expected = BF::from(1) / BF::from(4);
        assert_eq!(result, expected);

        let result = BF::from(10).powi(-3);
        let expected = BF::from(1) / BF::from(1000);
        assert_eq!(result, expected);

        let result = BF::from(5).powi(-2);
        let expected = BF::from(1) / BF::from(25);
        assert_eq!(result, expected);
    }

    #[test]
    fn test_powi_edge_cases() {
        assert_eq!(BF::zero().powi(1), BF::zero());

        assert_eq!(BF::from(1000).powi(2), BF::from(1_000_000));

        assert_eq!(BF::from(1).powi(1000), BF::from(1));
    }

    #[test]
    fn test_integer_from_string() {
        assert_eq!(BF::parse("1389"), BF::from(1389));
        assert_eq!(BF::parse("1389.0"), BF::from(1389.0));
    }

    #[test]
    fn test_decimal_from_string() {
        are_same(&BF::parse("1389.1389"), &BF::from(1389.1389));
        assert_eq!(BF::parse("1389.5"), BF::from(1389.5));
    }

    #[test]
    fn test_decimal_from_string_multiplication() {
        let a = BF::parse("0.5");
        let b = BF::parse("2");

        assert_eq!(a * b, BF::from(1.0));
    }
}
