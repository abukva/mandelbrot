mod bitshift;
mod exponent_state;

use bitshift::{BitShift, BitShiftDirection};
use exponent_state::ExponentState;
use std::{cmp::Ordering, ops::Neg};

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

    fn empty(exponent: i64, sign: bool) -> Self {
        Self {
            limbs: vec![0; PRECISION.div_ceil(64)].into_boxed_slice(),
            exponent: ExponentState::Normal(exponent),
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
            self.shift_limbs(limb_shift, &direction);
        }

        if bit_shift > 0 {
            self.shift_bits_internal(bit_shift, &direction);
        }
    }

    fn shift_limbs(&mut self, limb_count: usize, direction: &BitShiftDirection) {
        let len = self.limbs.len();
        let to_rotate = limb_count.min(len);
        match direction {
            BitShiftDirection::Left => {
                self.limbs.rotate_left(to_rotate);
                for i in 0..to_rotate {
                    self.limbs[i] = 0;
                }
            }
            BitShiftDirection::Right => {
                self.limbs.rotate_right(to_rotate);
                for i in (len - to_rotate)..len {
                    self.limbs[i] = 0;
                }
            }
        }
    }

    fn shift_bits_internal(&mut self, amount: u64, direction: &BitShiftDirection) {
        match direction {
            BitShiftDirection::Left => {
                let mut previous_limb = 0;
                for (idx, limb) in self.limbs.iter_mut().enumerate() {
                    if idx == 0 {
                        previous_limb = *limb;
                        *limb <<= amount;
                    } else {
                        let current = *limb;
                        *limb = (*limb << amount) | (previous_limb >> (64 - amount));
                        previous_limb = current;
                    }
                }
            }
            BitShiftDirection::Right => {
                let mut previous_limb = 0;
                for (idx, limb) in self.limbs.iter_mut().rev().enumerate() {
                    if idx == 0 {
                        previous_limb = *limb;
                        *limb >>= amount;
                    } else {
                        let current = *limb;
                        *limb = (*limb >> amount) | (previous_limb << (64 - amount));
                        previous_limb = current;
                    }
                }
            }
        }
    }

    pub(super) fn add_magnitudes(mut self, mut other: Self, result_sign: bool) -> Self {
        let mut carry = false;

        self.normalize(&mut other);

        let result_exponent = self.exponent.get_exponent();
        let mut result = Self::empty(result_exponent, result_sign);

        for i in 0..self.get_num_limbs() {
            let (sum, new_carry) = self.limbs[i].carrying_add(other.limbs[i], carry);
            result.limbs[i] = sum;
            carry = new_carry;
        }

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
        let mut borrow = false;

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

        let result_exponent = larger.exponent.get_exponent();
        let mut result = Self::empty(result_exponent, result_sign);

        for i in 0..larger.limbs.len() {
            let (diff, new_borrow) = larger.limbs[i].borrowing_sub(smaller.limbs[i], borrow);
            result.limbs[i] = diff;
            borrow = new_borrow;
        }

        result.normalize_leading_zeros();
        result
    }

    fn normalize_leading_zeros(&mut self) {
        let first_nonzero_idx = self.limbs.iter().rposition(|&x| x != 0);

        let (limb_shift_amount, first_nonzero_limb) = match first_nonzero_idx {
            Some(idx) => {
                let zero_limbs = self.get_num_limbs() - 1 - idx;
                (zero_limbs * 64, idx)
            }
            None => return,
        };

        let leading_zeros = self.limbs[first_nonzero_limb].leading_zeros() as usize;
        let bit_shift = if leading_zeros > 0 && leading_zeros < 64 {
            leading_zeros
        } else {
            0
        };

        let total_shift = limb_shift_amount + bit_shift;
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
            exponent: ExponentState::Normal(msb_position as i64 + 1),
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
        number.limbs[num_limbs - 1] = 0x8000_0000_0000_0000; // MSB set

        number.normalize_leading_zeros();

        assert_eq!(number.exponent.get_exponent(), 10);
        assert_eq!(number.limbs[num_limbs - 1], 0x8000_0000_0000_0000);
    }

    #[test]
    fn test_normalize_leading_zeros_single_bit_shift() {
        let mut number: Number<128> = Number::empty(10, false);
        let num_limbs = number.limbs.len();
        number.limbs[num_limbs - 1] = 0x4000_0000_0000_0000; // 1 leading zero

        number.normalize_leading_zeros();

        assert_eq!(number.exponent.get_exponent(), 9);
        assert_eq!(number.limbs[num_limbs - 1], 0x8000_0000_0000_0000);
    }

    #[test]
    fn test_normalize_leading_zeros_multiple_bits() {
        let mut number: Number<128> = Number::empty(20, false);
        let num_limbs = number.limbs.len();
        number.limbs[num_limbs - 1] = 0x0010_0000_0000_0000; // 11 leading zeros

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
        number.limbs[num_limbs - 2] = 0x0100_0000_0000_0000; // 7 leading zeros

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
        number.limbs[num_limbs - 1] = 0x0000_0000_0000_0001; // 63 leading zeros
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
        number.limbs[num_limbs - 1] = 0x0000_0000_0000_0001; // 63 leading zeros

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
        number.limbs[0] = 0x0000_0000_0000_0001; // Only LSB of first limb set

        number.normalize_leading_zeros();

        let num_limbs = number.limbs.len();
        let expected_shift = (num_limbs - 1) * 64 + 63;
        assert_eq!(number.exponent.get_exponent(), 5 - expected_shift as i64);
    }
}
