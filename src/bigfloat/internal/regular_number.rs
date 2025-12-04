mod bitshift;
mod exponent_state;
mod limb_ops;

use bitshift::BitShift;
use limb_ops::*;
use std::{cmp::Ordering, ops::Neg};

use exponent_state::ExponentState;

type DivResult = (
    (Vec<u64>, ExponentState, bool),
    (Vec<u64>, ExponentState, bool),
);

#[derive(Debug, Clone)]
pub(in crate::bigfloat) struct Number<const PRECISION: usize> {
    limbs: Box<[u64]>,
    exponent: ExponentState,
    sign: bool,
}

impl<const PRECISION: usize> Number<PRECISION> {
    pub(super) fn get_sign(&self) -> bool {
        self.sign
    }

    // This only works on numbers that have the same exponent!
    pub fn is_within_ulsp(&self, other: &Self, max_ulps: u64) -> bool {
        if self.get_sign() != other.get_sign() {
            return false;
        }
        if self.get_exponent() != other.get_exponent() {
            return false;
        }

        let limbs_a = &self.limbs;
        let limbs_b = &self.limbs;

        if limbs_a[1..] != limbs_b[1..] {
            return false;
        }

        let diff = limbs_a[0].abs_diff(limbs_b[0]);
        diff <= max_ulps
    }

    pub(super) fn get_exponent(&self) -> i64 {
        self.exponent.get_exponent()
    }

    fn empty(exponent: i64, sign: bool) -> Self {
        // Must have same sign and exponent
        Self {
            limbs: vec![0; PRECISION.div_ceil(64)].into_boxed_slice(),
            exponent: ExponentState::Normal(exponent),
            sign,
        }
    }

    pub(super) fn from_components(limbs: Vec<u64>, exponent: ExponentState, sign: bool) -> Self {
        Self {
            limbs: limbs.into_boxed_slice(),
            exponent,
            sign,
        }
    }

    fn get_num_limbs(&self) -> usize {
        self.limbs.len()
    }

    pub(super) fn is_zero(&self) -> bool {
        self.limbs.iter().all(|&x| x == 0)
    }

    pub(super) fn is_overflow(&self) -> bool {
        matches!(self.exponent, ExponentState::Overflow)
    }

    pub(super) fn is_underflow(&self) -> bool {
        matches!(self.exponent, ExponentState::Underflow)
    }

    fn normalize(&mut self, other: &mut Self) {
        let self_exp = self.exponent.get_exponent();

        let other_exp = other.exponent.get_exponent();

        let diff = self_exp - other_exp;

        match diff.cmp(&0) {
            Ordering::Equal => {}
            Ordering::Greater => {
                other.change_exponent(diff);
            }
            Ordering::Less => {
                self.change_exponent(-diff);
            }
        }
    }

    fn change_exponent(&mut self, diff: i64) {
        if diff == 0 {
            return;
        }
        if let ExponentState::Normal(current_exp) = self.exponent {
            match current_exp.checked_add(diff) {
                Some(new_exp) => {
                    self.exponent = ExponentState::Normal(new_exp);
                    self.shift_bits(BitShift::new(diff));
                }
                None => {
                    if diff > 0 {
                        self.exponent = ExponentState::Overflow;
                    } else {
                        self.exponent = ExponentState::Underflow;
                    }
                }
            }
        }
    }

    // Negative value means to shift to left, positive to the right
    fn shift_bits(&mut self, bit_shift: BitShift) {
        let BitShift { amount, direction } = bit_shift;

        let limb_shift = (amount / 64) as usize;
        let bit_shift = amount % 64;

        if limb_shift > 0 {
            shift_limbs(&mut self.limbs, limb_shift, &direction);
        }

        if bit_shift > 0 {
            shift_bits_internal(&mut self.limbs, bit_shift, &direction);
        }
    }

    pub(super) fn add_magnitudes(mut self, mut other: Self, result_sign: bool) -> Self {
        self.normalize(&mut other);

        let (limbs, carry) = add_limbs(&self.limbs, &other.limbs, false);
        let result_exponent = self.exponent.get_exponent();
        let mut result =
            Self::from_components(limbs, ExponentState::Normal(result_exponent), result_sign);

        if carry {
            result.change_exponent(1);
            if let ExponentState::Normal(_) = result.exponent {
                let idx_last = result.get_num_limbs() - 1;
                result.limbs[idx_last] |= 1u64 << 63;
            }
        }

        result
    }

    pub(super) fn sub_magnitudes(mut self, mut other: Self, force_sign: bool) -> Self {
        self.normalize(&mut other);

        let self_larger = self
            .limbs
            .iter()
            .rev()
            .zip(other.limbs.iter().rev())
            .find(|(a, b)| a != b)
            .map(|(a, b)| a > b)
            .unwrap_or(true);

        let (larger, smaller, result_sign) = if self_larger {
            (self, other, force_sign)
        } else {
            (other, self, !force_sign)
        };

        let (limbs, _) = sub_limbs(&larger.limbs, &smaller.limbs, false);
        let result_exponent = larger.exponent.get_exponent();
        let mut result =
            Self::from_components(limbs, ExponentState::Normal(result_exponent), result_sign);

        result.normalize_leading_zeros();
        result
    }

    pub(super) fn mul_magnitudes(self, other: Self) -> Self {
        let result_sign = self.get_sign() != other.get_sign();
        let (limbs, shift_amount) = mul_limbs(&self.limbs, &other.limbs);

        let result_exponent = ExponentState::sum_exponents(vec![
            self.get_exponent(),
            other.get_exponent(),
            shift_amount,
            (self.limbs.len() as i64 * 64),
        ]);

        let mut result = Self::from_components(limbs, result_exponent, result_sign);
        result.normalize_leading_zeros();
        result
    }

    fn algorithm_q(u: &[u64], v: &[u64]) -> u64 {
        let b: u128 = 1 << 64;

        let n_u = u.len();
        let n_v = v.len();

        let u_top = u[n_u - 1] as u128;
        let u_mid = u[n_u - 2] as u128;
        let u_low = u[n_u - 3] as u128;
        let v_top = v[n_v - 1] as u128;
        let v_mid = v[n_v - 2] as u128;

        let mut q = (u_top * b + u_mid) / v_top;
        let mut r = (u_top * b + u_mid) % v_top;

        if q == b {
            q -= 1;
            r += v_top;
        }

        while r < b && q * v_mid > r * b + u_low {
            q -= 1;
            r += v_top;
        }

        q as u64
    }

    fn knuth_div_rem(self, other: Self) -> DivResult {
        let n = self.get_num_limbs();

        let mut u = vec![0; 2 * n + 1];
        u[n..2 * n].copy_from_slice(&self.limbs);

        let v = &other.limbs;
        let mut q = vec![0; n + 1];

        for k in (0..=n).rev() {
            let mut q_k = Self::algorithm_q(&u[k..k + n + 1], v);

            let q_k_times_v = mul_limbs_by_single(v, q_k);

            let (diff, borrow) = sub_limbs(&u[k..k + n + 1], &q_k_times_v, false);

            u[k..k + n + 1].copy_from_slice(&diff);

            if borrow {
                q_k -= 1;
                let (sum, _) = add_limbs(&u[k..k + n + 1], v, false);
                u[k..k + n + 1].copy_from_slice(&sum);
            }
            q[k] = q_k;
        }

        let mut r = u[0..n].to_vec();

        let overflow = round_limbs(&mut q, v, &r);

        let q_shift = normalize_and_shift_limbs(&mut q);
        let overflow_adjustemnt = if overflow { 1i64 } else { 0i64 };

        let q_exp = ExponentState::sum_exponents(vec![
            self.get_exponent(),
            -other.get_exponent(),
            -((n - 1) as i64 * 64),
            -(q_shift as i64),
            overflow_adjustemnt,
        ]);

        let r_shift = normalize_and_shift_limbs(&mut r);
        let r_exp = ExponentState::sum_exponents(vec![
            self.get_exponent(),
            -(n as i64 * 64),
            -(r_shift as i64),
        ]);

        (
            (q[1..].to_vec(), q_exp, self.get_sign() != other.get_sign()),
            (r, r_exp, self.get_sign()),
        )
    }

    // For my normalized representation of numbers this is actual floating-point division
    // where reminder is just the error I introduced by doing a truncation to certain bit PRECISION
    pub(super) fn single_limb_div_rem(self, other: Self) -> DivResult {
        let dividend = (self.limbs[0] as u128) << 64;
        let divisor = other.limbs[0] as u128;

        let mut quotient = dividend / divisor;
        let remainder = (dividend % divisor) as u64;

        // Rounding logic
        if (remainder as u128 * 2 > divisor)
            || (remainder as u128 * 2 == divisor && (quotient & 1) == 1)
        {
            quotient += 1;
        }

        let (r_mantissa, r_exp) = if remainder == 0 {
            (0, ExponentState::Normal(0))
        } else {
            let lz_r = remainder.leading_zeros();
            (
                remainder << lz_r,
                ExponentState::sum_exponents(vec![self.get_exponent(), -64, -(lz_r as i64)]),
            )
        };

        let lz = quotient.leading_zeros();
        let normalized = quotient << lz;
        let mantissa = (normalized >> 64) as u64;
        let exponent = ExponentState::sum_exponents(vec![
            self.get_exponent(),
            -other.get_exponent(),
            -(lz as i64),
        ]);

        (
            (
                vec![mantissa],
                exponent,
                self.get_sign() != other.get_sign(),
            ),
            (vec![r_mantissa], r_exp, self.get_sign()),
        )
    }

    pub(super) fn div_magnitudes(self, other: Self) -> Self {
        match self.get_num_limbs() {
            1 => {
                let ((q_m, q_e, q_s), _) = self.single_limb_div_rem(other);
                Self::from_components(q_m, q_e, q_s)
            }
            _ => {
                let ((q_m, q_e, q_s), _) = self.knuth_div_rem(other);
                Self::from_components(q_m, q_e, q_s)
            }
        }
    }

    fn normalize_leading_zeros(&mut self) {
        let total_shift = get_normalization_leading_zeros_limb(&mut self.limbs);
        if total_shift != 0 {
            self.change_exponent(-(total_shift as i64));
        }
    }

    fn set_sign(&mut self, sign: bool) {
        self.sign = sign;
    }
}

impl<const PRECISION: usize> Neg for Number<PRECISION> {
    type Output = Self;

    fn neg(mut self) -> Self {
        self.set_sign(!self.get_sign());
        self
    }
}

impl<const PRECISION: usize> PartialEq for Number<PRECISION> {
    fn eq(&self, other: &Self) -> bool {
        self.exponent.get_exponent() == other.exponent.get_exponent()
            && self.get_sign() == other.get_sign()
            && self.limbs == other.limbs
    }
}

impl<const PRECISION: usize> PartialOrd for Number<PRECISION> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        match self.sign.cmp(&other.sign) {
            Ordering::Equal => {}
            ord => return Some(ord.reverse()),
        }

        let self_exp = self.exponent.get_exponent();
        let other_exp = other.exponent.get_exponent();

        let exp_cmp = self_exp.cmp(&other_exp);

        if exp_cmp != Ordering::Equal {
            return if self.get_sign() {
                Some(exp_cmp.reverse())
            } else {
                Some(exp_cmp)
            };
        }

        let limb_cmp = self.limbs.last().cmp(&other.limbs.last());
        if self.get_sign() {
            Some(limb_cmp.reverse())
        } else {
            Some(limb_cmp)
        }
    }
}

impl<const PRECISION: usize> From<u64> for Number<PRECISION> {
    fn from(value: u64) -> Self {
        let limbs_needed = PRECISION.div_ceil(64);
        let leading_zeros = value.leading_zeros();

        let msb_position = 63 - leading_zeros;

        let normalized = value << leading_zeros;

        let mut limbs = vec![0; limbs_needed].into_boxed_slice();
        limbs[limbs_needed - 1] = normalized;

        Self {
            limbs,
            exponent: ExponentState::Normal(msb_position as i64 + 1 - (limbs_needed as i64) * 64),
            sign: false,
        }
    }
}

impl<const PRECISION: usize> From<i64> for Number<PRECISION> {
    fn from(value: i64) -> Self {
        if value >= 0 {
            Self::from(value as u64)
        } else {
            let abs_value = value.wrapping_neg() as u64;
            let mut result = Self::from(abs_value);
            result.set_sign(true);
            result
        }
    }
}

impl<const PRECISION: usize> From<u32> for Number<PRECISION> {
    fn from(value: u32) -> Self {
        Self::from(value as u64)
    }
}

impl<const PRECISION: usize> From<i32> for Number<PRECISION> {
    fn from(value: i32) -> Self {
        Self::from(value as i64)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // Helper functions
    fn to_value(limbs: &[u64], exponent: ExponentState, sign: bool) -> f64 {
        match exponent {
            ExponentState::Normal(exp) => {
                let mut mag = 0.0f64;
                for (i, &limb) in limbs.iter().enumerate() {
                    mag += (limb as f64) * 2_f64.powi((i as i32) * 64 + exp as i32);
                }
                if sign { -mag } else { mag }
            }
            _ => panic!("Float can't be constructed from special values"),
        }
    }

    fn to_value_tuple(t: &(Vec<u64>, ExponentState, bool)) -> f64 {
        to_value(&t.0, t.1, t.2)
    }

    // end of helper functions

    #[test]
    fn test_normalize_leading_zeros_all_zeros() {
        let mut number: Number<128> = Number::empty(0, false);
        let original_exponent = number.exponent.get_exponent();

        number.normalize_leading_zeros();

        assert_eq!(number.exponent.get_exponent(), original_exponent);
        assert!(number.is_zero());
    }

    #[test]
    fn test_normalize_leading_zeros_no_leading_zeros() {
        let mut number: Number<128> = Number::empty(10, false);
        let num_limbs = number.limbs.len();
        number.limbs[num_limbs - 1] = 0x8000_0000_0000_0000;

        number.normalize_leading_zeros();

        assert_eq!(number.exponent.get_exponent(), 10);
        assert_eq!(number.limbs[num_limbs - 1], 0x8000_0000_0000_0000);
    }

    #[test]
    fn test_normalize_leading_zeros_single_bit_shift() {
        let mut number: Number<128> = Number::empty(10, false);
        let num_limbs = number.limbs.len();
        number.limbs[num_limbs - 1] = 0x4000_0000_0000_0000;

        number.normalize_leading_zeros();

        assert_eq!(number.exponent.get_exponent(), 9);
        fn to_value(limbs: &[u64], exponent: i64, sign: bool) -> f64 {
            let mut mag = 0.0f64;
            for (i, &limb) in limbs.iter().enumerate() {
                mag += (limb as f64) * 2_f64.powi((i as i32) * 64 + exponent as i32);
            }
            if sign { -mag } else { mag }
        }
        assert_eq!(number.limbs[num_limbs - 1], 0x8000_0000_0000_0000);
    }

    #[test]
    fn test_normalize_leading_zeros_multiple_bits() {
        let mut number: Number<128> = Number::empty(20, false);
        let num_limbs = number.limbs.len();
        number.limbs[num_limbs - 1] = 0x0010_0000_0000_0000;

        number.normalize_leading_zeros();

        assert_eq!(number.exponent.get_exponent(), 9);
        assert_eq!(number.limbs[num_limbs - 1], 0x8000_0000_0000_0000);
    }

    #[test]
    fn test_normalize_leading_zeros_one_full_limb() {
        let mut number: Number<128> = Number::empty(100, false);
        let num_limbs = number.limbs.len();
        number.limbs[num_limbs - 1] = 0;
        number.limbs[num_limbs - 2] = 0x8000_0000_0000_0000;

        number.normalize_leading_zeros();

        assert_eq!(number.exponent.get_exponent(), 36);
        assert_eq!(number.limbs[num_limbs - 1], 0x8000_0000_0000_0000);
    }

    #[test]
    fn test_normalize_leading_zeros_full_limb_plus_bits() {
        let mut number: Number<128> = Number::empty(100, false);
        let num_limbs = number.limbs.len();
        number.limbs[num_limbs - 1] = 0;
        number.limbs[num_limbs - 2] = 0x0100_0000_0000_0000;

        number.normalize_leading_zeros();

        assert_eq!(number.exponent.get_exponent(), 29);
        assert_eq!(number.limbs[num_limbs - 1], 0x8000_0000_0000_0000);
    }

    #[test]
    fn test_normalize_leading_zeros_preserves_sign() {
        let mut positive_number: Number<128> = Number::empty(10, false);
        let mut negative_number: Number<128> = Number::empty(10, true);

        let num_limbs = positive_number.limbs.len();
        positive_number.limbs[num_limbs - 1] = 0x4000_0000_0000_0000;
        negative_number.limbs[num_limbs - 1] = 0x4000_0000_0000_0000;

        positive_number.normalize_leading_zeros();
        negative_number.normalize_leading_zeros();

        assert!(!positive_number.get_sign());
        assert!(negative_number.get_sign());
    }

    #[test]
    fn test_normalize_leading_zeros_with_carry_bits() {
        let mut number: Number<256> = Number::empty(50, false);
        let num_limbs = number.limbs.len();
        number.limbs[num_limbs - 1] = 0x0000_0000_0000_0001;
        number.limbs[num_limbs - 2] = 0xFFFF_FFFF_FFFF_FFFF;

        number.normalize_leading_zeros();

        assert_eq!(number.exponent.get_exponent(), -13);
        assert_eq!(number.limbs[num_limbs - 1], 0xFFFF_FFFF_FFFF_FFFF);
        assert_eq!(number.limbs[num_limbs - 2], 0x8000_0000_0000_0000);
    }

    #[test]
    fn test_normalize_leading_zeros_exponent_underflow() {
        let mut number: Number<128> = Number::empty(-100, false);
        let num_limbs = number.limbs.len();
        number.limbs[num_limbs - 1] = 0x0000_0000_0000_0001;

        number.normalize_leading_zeros();

        let expected_exp = (-100i64).checked_sub(63);

        if let Some(exp) = expected_exp {
            assert_eq!(number.exponent.get_exponent(), exp);
        } else {
            assert!(number.is_underflow());
        }
    }

    #[test]
    fn test_normalize_leading_zeros_small_value() {
        let mut number: Number<128> = Number::empty(5, false);
        number.limbs[0] = 0x0000_0000_0000_0001;

        number.normalize_leading_zeros();

        let num_limbs = number.limbs.len();
        let expected_shift = (num_limbs - 1) * 64 + 63;
        assert_eq!(number.exponent.get_exponent(), 5 - expected_shift as i64);
    }

    #[test]
    fn test_mul_magnitudes_simple() {
        let a: Number<128> = Number::from(2u64);
        let b: Number<128> = Number::from(3u64);
        let result = a.mul_magnitudes(b);
        let expected: Number<128> = Number::from(6u64);

        assert_eq!(result, expected);
    }

    #[test]
    fn test_mul_magnitudes_powers_of_two() {
        let a: Number<128> = Number::from(4u64);
        let b: Number<128> = Number::from(8u64);
        let result = a.mul_magnitudes(b);
        let expected: Number<128> = Number::from(32u64);

        assert_eq!(result, expected);
    }

    #[test]
    fn test_mul_magnitudes_one() {
        let a: Number<128> = Number::from(42u64);
        let b: Number<128> = Number::from(1u64);
        let result = a.clone().mul_magnitudes(b);

        assert_eq!(result, a);
    }

    #[test]
    fn test_mul_magnitudes_large_values() {
        let a: Number<256> = Number::from(u64::MAX);
        let b: Number<256> = Number::from(u64::MAX);
        let result = a.mul_magnitudes(b);

        assert!(!result.is_overflow());
        assert!(!result.is_underflow());
    }

    #[test]
    fn test_mul_magnitudes_exponent_addition() {
        let a: Number<128> = Number::from(16u64);
        let b: Number<128> = Number::from(32u64);
        let result = a.mul_magnitudes(b);

        let expected: Number<128> = Number::from(512u64);
        assert_eq!(result, expected);
    }

    #[test]
    fn test_mul_magnitudes_different_sizes() {
        let a: Number<128> = Number::from(1000u64);
        let b: Number<128> = Number::from(5u64);
        let result = a.mul_magnitudes(b);
        let expected: Number<128> = Number::from(5000u64);

        assert_eq!(result, expected);
    }

    #[test]
    fn test_mul_magnitudes_max_precision() {
        let a: Number<256> = Number::from((1u64 << 32) - 1);
        let b: Number<256> = Number::from((1u64 << 32) - 1);
        let result = a.mul_magnitudes(b);

        assert!(!result.is_overflow());
        assert!(!result.is_underflow());
    }

    #[test]
    fn test_mul_magnitudes_preserves_normalization() {
        let a: Number<128> = Number::from(7u64);
        let b: Number<128> = Number::from(9u64);
        let result = a.mul_magnitudes(b);

        let msb_limb = result.limbs[result.limbs.len() - 1];
        assert_ne!(msb_limb, 0);
        assert!(
            msb_limb & (1u64 << 63) != 0,
            "Result should be normalized with MSB set"
        );
    }

    #[test]
    fn test_mul_magnitudes_sign_handling() {
        let a: Number<128> = Number::from(-5i64);
        let b: Number<128> = Number::from(3i64);
        let result = a.mul_magnitudes(b);

        assert!(result.get_sign());
    }

    #[test]
    fn test_mul_magnitudes_both_negative() {
        let a: Number<128> = Number::from(-4i64);
        let b: Number<128> = Number::from(-7i64);
        let result = a.mul_magnitudes(b);

        assert!(!result.get_sign());
    }

    #[test]
    fn test_mul_magnitudes_commutative() {
        let a: Number<128> = Number::from(13u64);
        let b: Number<128> = Number::from(17u64);

        let result1 = a.clone().mul_magnitudes(b.clone());
        let result2 = b.mul_magnitudes(a);

        assert_eq!(result1, result2);
    }

    #[test]
    fn test_mul_magnitudes_small_by_large() {
        let small: Number<256> = Number::from(2u64);
        let large: Number<256> = Number::from(1u64 << 50);
        let result = small.mul_magnitudes(large);

        let expected: Number<256> = Number::from(1u64 << 51);
        assert_eq!(result, expected);
    }

    #[test]
    fn test_one_divided_by_one() {
        let a: Number<64> =
            Number::from_components(vec![1u64 << 63], ExponentState::Normal(-63), false);
        let b: Number<64> =
            Number::from_components(vec![1u64 << 63], ExponentState::Normal(-63), false);

        let ((q_m, q_e, q_s), (r_m, _, _)) = a.single_limb_div_rem(b);

        let quotient = to_value(&q_m, q_e, q_s);
        assert!((quotient - 1.0).abs() < 1e-15);
        assert_eq!(r_m[0], 0);
    }

    #[test]
    fn test_two_divided_by_one() {
        let a: Number<64> =
            Number::from_components(vec![1u64 << 63], ExponentState::Normal(-62), false);
        let b: Number<64> =
            Number::from_components(vec![1u64 << 63], ExponentState::Normal(-63), false);

        let ((q_m, q_e, q_s), (r_m, _, _)) = a.single_limb_div_rem(b);

        let quotient = to_value(&q_m, q_e, q_s);
        assert!((quotient - 2.0).abs() < 1e-15);
        assert_eq!(r_m[0], 0);
    }

    #[test]
    fn test_one_divided_by_two() {
        let a: Number<64> =
            Number::from_components(vec![1u64 << 63], ExponentState::Normal(-63), false);
        let b: Number<64> =
            Number::from_components(vec![1u64 << 63], ExponentState::Normal(-62), false);

        let ((q_m, q_e, q_s), (r_m, _, _)) = a.single_limb_div_rem(b);

        let quotient = to_value(&q_m, q_e, q_s);
        assert!((quotient - 0.5).abs() < 1e-15);
        assert_eq!(r_m[0], 0);
    }

    #[test]
    fn test_three_divided_by_two() {
        let a: Number<64> = Number::from_components(
            vec![0xC000_0000_0000_0000],
            ExponentState::Normal(-62),
            false,
        );
        let b: Number<64> =
            Number::from_components(vec![1u64 << 63], ExponentState::Normal(-62), false);

        let ((q_m, q_e, q_s), _) = a.single_limb_div_rem(b);

        let quotient = to_value(&q_m, q_e, q_s);
        assert!((quotient - 1.5).abs() < 1e-15);
    }

    #[test]
    fn test_division_identity() {
        let a: Number<64> = Number::from_components(
            vec![0xAAAA_BBBB_CCCC_DDDD],
            ExponentState::Normal(10),
            false,
        );
        let b: Number<64> =
            Number::from_components(vec![0x8888_9999_AAAA_BBBB], ExponentState::Normal(5), false);

        let a_val = to_value(&[0xAAAA_BBBB_CCCC_DDDD], ExponentState::Normal(10), false);
        let b_val = to_value(&[0x8888_9999_AAAA_BBBB], ExponentState::Normal(5), false);

        let ((q_m, q_e, q_s), (r_m, r_e, r_s)) = a.single_limb_div_rem(b);

        let q_val = to_value(&q_m, q_e, q_s);
        let r_val = to_value(&r_m, r_e, r_s);

        let reconstructed = q_val * b_val + r_val;
        assert!((reconstructed - a_val).abs() / a_val < 1e-10);
    }

    #[test]
    fn test_negative_dividend() {
        let a: Number<64> =
            Number::from_components(vec![1u64 << 63], ExponentState::Normal(-61), true);
        let b: Number<64> =
            Number::from_components(vec![1u64 << 63], ExponentState::Normal(-62), false);

        let ((q_m, q_e, q_s), (_, _, r_s)) = a.single_limb_div_rem(b);

        let quotient = to_value(&q_m, q_e, q_s);
        assert!((quotient - (-2.0)).abs() < 1e-15);
        assert!(q_s);
        assert!(r_s);
    }

    #[test]
    fn test_negative_divisor() {
        let a: Number<64> =
            Number::from_components(vec![1u64 << 63], ExponentState::Normal(-61), false);
        let b: Number<64> =
            Number::from_components(vec![1u64 << 63], ExponentState::Normal(-62), true);

        let ((q_m, q_e, q_s), (_, _, r_s)) = a.single_limb_div_rem(b);

        let quotient = to_value(&q_m, q_e, q_s);
        assert!((quotient - (-2.0)).abs() < 1e-15);
        assert!(q_s);
        assert!(!r_s);
    }

    #[test]
    fn test_both_negative() {
        let a: Number<64> =
            Number::from_components(vec![1u64 << 63], ExponentState::Normal(-61), true);
        let b: Number<64> =
            Number::from_components(vec![1u64 << 63], ExponentState::Normal(-62), true);

        let ((q_m, q_e, q_s), _) = a.single_limb_div_rem(b);

        let quotient = to_value(&q_m, q_e, q_s);
        assert!((quotient - 2.0).abs() < 1e-15);
        assert!(!q_s);
    }

    #[test]
    fn test_msb_always_set() {
        let a: Number<64> =
            Number::from_components(vec![0x8000_0000_0000_0001], ExponentState::Normal(0), false);
        let b: Number<64> =
            Number::from_components(vec![0xFFFF_FFFF_FFFF_FFFF], ExponentState::Normal(0), false);

        let ((q_m, _, _), _) = a.single_limb_div_rem(b);

        assert!(q_m[0] & (1u64 << 63) != 0, "MSB should be set");
    }

    #[test]
    fn test_zero_remainder_handled() {
        let a: Number<64> =
            Number::from_components(vec![1u64 << 63], ExponentState::Normal(-61), false);
        let b: Number<64> =
            Number::from_components(vec![1u64 << 63], ExponentState::Normal(-62), false);

        let ((q_m, q_e, q_s), (r_m, _, _)) = a.single_limb_div_rem(b);

        let quotient = to_value(&q_m, q_e, q_s);
        assert!((quotient - 2.0).abs() < 1e-15);
        assert_eq!(r_m[0], 0);
    }

    #[test]
    fn test_handpicked_digits() {
        let a: Number<64> = Number::from(2356);
        let b: Number<64> = Number::from(395);

        let ((q_m, q_e, q_s), (_, _, _)) = a.single_limb_div_rem(b);

        let quotient = to_value(&q_m, q_e, q_s);
        assert!((quotient - (2356.0 / 395.0)).abs() < 1e-15);
    }

    #[test]
    fn test_knuth_one_divided_by_one() {
        let a: Number<128> =
            Number::from_components(vec![0, 1u64 << 63], ExponentState::Normal(-127), false);
        let b: Number<128> =
            Number::from_components(vec![0, 1u64 << 63], ExponentState::Normal(-127), false);

        let (q, _) = a.knuth_div_rem(b);

        let quotient = to_value_tuple(&q);
        assert!(
            (quotient - 1.0).abs() < 1e-10,
            "Expected 1.0, got {}",
            quotient
        );
    }

    #[test]
    fn test_knuth_two_divided_by_one() {
        let a: Number<128> =
            Number::from_components(vec![0, 1u64 << 63], ExponentState::Normal(-126), false);
        let b: Number<128> =
            Number::from_components(vec![0, 1u64 << 63], ExponentState::Normal(-127), false);

        let (q, _) = a.knuth_div_rem(b);

        let quotient = to_value_tuple(&q);
        assert!(
            (quotient - 2.0).abs() < 1e-10,
            "Expected 2.0, got {}",
            quotient
        );
    }

    #[test]
    fn test_knuth_one_divided_by_two() {
        let a: Number<128> =
            Number::from_components(vec![0, 1u64 << 63], ExponentState::Normal(-127), false);
        let b: Number<128> =
            Number::from_components(vec![0, 1u64 << 63], ExponentState::Normal(-126), false);

        let (q, _) = a.knuth_div_rem(b);

        let quotient = to_value_tuple(&q);
        assert!(
            (quotient - 0.5).abs() < 1e-10,
            "Expected 0.5, got {}",
            quotient
        );
    }

    #[test]
    fn test_knuth_three_divided_by_two() {
        let a: Number<128> = Number::from_components(
            vec![0, 0xC000_0000_0000_0000],
            ExponentState::Normal(-126),
            false,
        );
        let b: Number<128> =
            Number::from_components(vec![0, 1u64 << 63], ExponentState::Normal(-126), false);

        let (q, _) = a.knuth_div_rem(b);

        let quotient = to_value_tuple(&q);
        assert!(
            (quotient - 1.5).abs() < 1e-10,
            "Expected 1.5, got {}",
            quotient
        );
    }

    #[test]
    fn test_knuth_division_identity() {
        let a: Number<128> = Number::from_components(
            vec![0xDEAD_BEEF_CAFE_BABE, 0xAAAA_BBBB_CCCC_DDDD],
            ExponentState::Normal(10),
            false,
        );
        let b: Number<128> = Number::from_components(
            vec![0x1234_5678_9ABC_DEF0, 0x8888_9999_AAAA_BBBB],
            ExponentState::Normal(5),
            false,
        );

        let a_val = to_value_tuple(&(a.limbs.to_vec(), a.exponent, a.get_sign()));
        let b_val = to_value_tuple(&(b.limbs.to_vec(), b.exponent, b.get_sign()));

        let (q, r) = a.knuth_div_rem(b);

        let q_val = to_value_tuple(&q);
        let r_val = to_value_tuple(&r);

        let reconstructed = q_val * b_val + r_val;
        let rel_error = (reconstructed - a_val).abs() / a_val;
        assert!(
            rel_error < 1e-10,
            "Identity failed: {} != {}, rel_error = {}",
            reconstructed,
            a_val,
            rel_error
        );
    }

    #[test]
    fn test_knuth_negative_dividend() {
        let a: Number<128> =
            Number::from_components(vec![0, 1u64 << 63], ExponentState::Normal(-125), true);
        let b: Number<128> =
            Number::from_components(vec![0, 1u64 << 63], ExponentState::Normal(-126), false);

        let (q, r) = a.knuth_div_rem(b);

        let quotient = to_value_tuple(&q);
        assert!(
            (quotient - (-2.0)).abs() < 1e-10,
            "Expected -2.0, got {}",
            quotient
        );
        assert!(q.2, "Quotient should be negative");
        assert!(r.2, "Remainder should have sign of dividend (negative)");
    }

    #[test]
    fn test_knuth_negative_divisor() {
        let a: Number<128> =
            Number::from_components(vec![0, 1u64 << 63], ExponentState::Normal(-125), false);
        let b: Number<128> =
            Number::from_components(vec![0, 1u64 << 63], ExponentState::Normal(-126), true);

        let (q, r) = a.knuth_div_rem(b);

        let quotient = to_value_tuple(&q);
        assert!(
            (quotient - (-2.0)).abs() < 1e-10,
            "Expected -2.0, got {}",
            quotient
        );
        assert!(q.2, "Quotient should be negative");
        assert!(!r.2, "Remainder should have sign of dividend (positive)");
    }

    #[test]
    fn test_knuth_both_negative() {
        let a: Number<128> =
            Number::from_components(vec![0, 1u64 << 63], ExponentState::Normal(-125), true);
        let b: Number<128> =
            Number::from_components(vec![0, 1u64 << 63], ExponentState::Normal(-126), true);

        let (q, _) = a.knuth_div_rem(b);

        let quotient = to_value_tuple(&q);
        assert!(
            (quotient - 2.0).abs() < 1e-10,
            "Expected 2.0, got {}",
            quotient
        );
        assert!(!q.2, "Quotient should be positive");
    }

    #[test]
    fn test_knuth_quotient_msb_set() {
        let a: Number<128> = Number::from_components(
            vec![0x0000_0000_0000_0001, 0x8000_0000_0000_0000],
            ExponentState::Normal(0),
            false,
        );
        let b: Number<128> = Number::from_components(
            vec![0xFFFF_FFFF_FFFF_FFFF, 0xFFFF_FFFF_FFFF_FFFF],
            ExponentState::Normal(0),
            false,
        );

        let (q, _) = a.knuth_div_rem(b);

        let top_limb = q.0.last().unwrap();
        assert!(
            top_limb & (1u64 << 63) != 0,
            "MSB should be set, got {:016x}",
            top_limb
        );
    }

    #[test]
    fn test_knuth_large_dividend_small_divisor() {
        let a: Number<128> =
            Number::from_components(vec![0, 1u64 << 63], ExponentState::Normal(100), false);
        let b: Number<128> =
            Number::from_components(vec![0, 1u64 << 63], ExponentState::Normal(-100), false);

        let (q, _) = a.knuth_div_rem(b);

        let quotient = to_value_tuple(&q);
        let expected = 2_f64.powi(200);
        let rel_error = (quotient - expected).abs() / expected;
        assert!(
            rel_error < 1e-10,
            "Expected 2^200, got {}, rel_error = {}",
            quotient,
            rel_error
        );
    }

    #[test]
    fn test_knuth_small_dividend_large_divisor() {
        let a: Number<128> =
            Number::from_components(vec![0, 1u64 << 63], ExponentState::Normal(-100), false);
        let b: Number<128> =
            Number::from_components(vec![0, 1u64 << 63], ExponentState::Normal(100), false);

        let (q, _) = a.knuth_div_rem(b);

        let quotient = to_value_tuple(&q);
        let expected = 2_f64.powi(-200);
        let rel_error = (quotient - expected).abs() / expected;
        assert!(
            rel_error < 1e-10,
            "Expected 2^(-200), got {}, rel_error = {}",
            quotient,
            rel_error
        );
    }

    #[test]
    fn test_knuth_same_numbers() {
        let a: Number<128> = Number::from_components(
            vec![0x1234_5678_ABCD_EF00, 0xFEDC_BA98_7654_3210],
            ExponentState::Normal(42),
            false,
        );
        let b: Number<128> = Number::from_components(
            vec![0x1234_5678_ABCD_EF00, 0xFEDC_BA98_7654_3210],
            ExponentState::Normal(42),
            false,
        );

        let (q, _) = a.knuth_div_rem(b);

        let quotient = to_value_tuple(&q);
        assert!(
            (quotient - 1.0).abs() < 1e-10,
            "Expected 1.0, got {}",
            quotient
        );
    }

    #[test]
    fn test_knuth_pi_approximation() {
        let a: Number<128> = Number::from_components(
            vec![0, 0xB180_0000_0000_0000],
            ExponentState::Normal(-118),
            false,
        );

        let b: Number<128> = Number::from_components(
            vec![0, 0xE200_0000_0000_0000],
            ExponentState::Normal(-120),
            false,
        );

        let (q, _) = a.knuth_div_rem(b);

        let quotient = to_value_tuple(&q);
        let expected = 355.0 / 113.0;
        assert!(
            (quotient - expected).abs() < 1e-10,
            "Expected {}, got {}",
            expected,
            quotient
        );
    }

    #[test]
    fn test_knuth_handpicked_numbers() {
        let a: Number<128> = Number::from(123456789123456789u64);
        let b: Number<128> = Number::from(123456789);

        let (q, _) = a.knuth_div_rem(b);
        let quotient = to_value_tuple(&q);
        let expected = 123456789123456789.0 / 123456789.0;

        assert!((quotient - expected).abs() < 1e-15);
    }
}
