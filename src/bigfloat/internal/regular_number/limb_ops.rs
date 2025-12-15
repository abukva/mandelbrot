use itertools::izip;
use std::cmp::Ordering;

use super::bitshift::BitShiftDirection;

#[inline]
pub(super) fn shift_limbs(limbs: &mut [u64], limb_count: usize, direction: &BitShiftDirection) {
    let len = limbs.len();
    let to_rotate = limb_count.min(len);
    match direction {
        BitShiftDirection::Left => {
            limbs.copy_within(0..(len - to_rotate), to_rotate);
            limbs[..to_rotate].fill(0);
        }
        BitShiftDirection::Right => {
            limbs.copy_within(to_rotate..len, 0);
            limbs[(len - to_rotate)..].fill(0);
        }
    }
}

#[inline]
pub(super) fn shift_bits_internal(limbs: &mut [u64], amount: u64, direction: &BitShiftDirection) {
    match direction {
        BitShiftDirection::Left => {
            let mut previous_limb = 0;
            for (idx, limb) in limbs.iter_mut().enumerate() {
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
            for (idx, limb) in limbs.iter_mut().rev().enumerate() {
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

#[inline]
pub(super) fn normalize_and_shift_limbs(limbs: &mut [u64]) -> usize {
    let shift_amount = get_normalization_leading_zeros_limb(limbs);

    if shift_amount == 0 {
        return 0;
    }

    let limb_shift = shift_amount / 64;
    let bit_shift = shift_amount % 64;

    if limb_shift > 0 {
        shift_limbs(limbs, limb_shift, &BitShiftDirection::Left);
    }

    if bit_shift > 0 {
        shift_bits_internal(limbs, bit_shift as u64, &BitShiftDirection::Left);
    }

    shift_amount
}

/// It's assumed that lhs.len() == rhs.len()
#[inline]
pub(super) fn add_limbs<const N: usize>(
    lhs: &[u64],
    rhs: &[u64],
    mut carry: bool,
) -> ([u64; N], bool) {
    let mut result = [0u64; N];

    for (res, l, r) in izip!(&mut result, lhs, rhs) {
        (*res, carry) = l.carrying_add(*r, carry);
    }

    (result, carry)
}

/// Multiply n limbs by single limb, returns n+1 limbs (no normalization)
#[inline]
pub(super) fn mul_limbs_by_single<const N: usize>(limbs: &[u64], scalar: u64) -> [u64; N + 1]
where
    [(); N + 1]:,
{
    let mut result = [0u64; N + 1];
    let mut carry: u64 = 0;

    for (i, &limb) in limbs.iter().enumerate() {
        (result[i], carry) = scalar.carrying_mul(limb, carry);
    }
    result[N] = carry;
    result
}

/// It's assumed that lhs.len() == rhs.len()
#[inline]
pub(super) fn sub_limbs<const N: usize>(
    lhs: &[u64],
    rhs: &[u64],
    mut borrow: bool,
) -> ([u64; N], bool) {
    let mut result = [0u64; N];

    for (res, l, r) in izip!(&mut result, lhs, rhs) {
        (*res, borrow) = l.borrowing_sub(*r, borrow);
    }

    (result, borrow)
}

/// It's assumed that lhs.len() == rhs.len()
#[inline]
pub(super) fn mul_limbs<const N: usize>(lhs: &[u64; N], rhs: &[u64; N]) -> ([u64; N], i64)
where
    [(); 2 * N]:,
{
    let n = lhs.len();
    let mut temp_res = [0u64; 2 * N];

    for i in 0..n {
        let mut carry: u64 = 0;

        for (j, &rhs_limb) in rhs.iter().enumerate() {
            let k = i + j;
            (temp_res[k], carry) = lhs[i].carrying_mul_add(rhs_limb, carry, temp_res[k]);
        }

        temp_res[i + n] = carry;
    }

    let msb_index = temp_res.iter().rposition(|&x| x != 0).unwrap();

    if msb_index >= n - 1 {
        let start_index = msb_index - (n - 1);
        let shift_amount = (n as i64) - (start_index as i64);

        let mut result: [u64; N] = temp_res[start_index..(start_index + n)].try_into().unwrap();
        let overflow = round_mul_result(&mut result, &temp_res, start_index);

        let exp_adj = -(shift_amount * 64) + if overflow { 1 } else { 0 };
        (result, exp_adj)
    } else {
        let shift_amount = ((n - 1 - msb_index) * 64) as i64;
        let mut result = [0u64; N];
        result[..=msb_index].copy_from_slice(&temp_res[0..=msb_index]);

        (result, -shift_amount)
    }
}

#[inline]
fn round_mul_result(result: &mut [u64], full_product: &[u64], start_index: usize) -> bool {
    if start_index == 0 {
        return false;
    }

    let guard_limb = full_product[start_index - 1];
    let guard_bit = (guard_limb >> 63) & 1;

    let sticky = (guard_limb & 0x7FFFFFFFFFFFFFFF) != 0
        || full_product[..start_index - 1].iter().any(|&x| x != 0);

    let round_up = guard_bit == 1 && (sticky || (result[0] & 1) == 1);

    if round_up {
        let mut carry = true;
        for limb in result.iter_mut() {
            let (res, c) = limb.overflowing_add(if carry { 1 } else { 0 });
            *limb = res;
            carry = c;
            if !carry {
                break;
            }
        }

        if carry {
            result[result.len() - 1] = 1u64 << 63;
            return true;
        }
    }

    false
}

#[inline]
pub(super) fn get_normalization_leading_zeros_limb(limbs: &mut [u64]) -> usize {
    let first_nonzero_idx = limbs.iter().rposition(|&x| x != 0);

    let (limb_shift_amount, first_nonzero_limb) = match first_nonzero_idx {
        Some(idx) => {
            let zero_limbs = limbs.len() - 1 - idx;
            (zero_limbs * 64, idx)
        }
        None => return 0,
    };

    let leading_zeros = limbs[first_nonzero_limb].leading_zeros() as usize;
    let bit_shift = if leading_zeros > 0 && leading_zeros < 64 {
        leading_zeros
    } else {
        0
    };

    limb_shift_amount + bit_shift
}

#[inline]
pub(super) fn round_limbs<const N: usize>(q: &mut [u64], v: &[u64], r: &[u64]) -> bool
where
    [(); N + 1]:,
{
    let double_r = mul_limbs_by_single::<N>(r, 2);

    let cmp = compare_limbs(&double_r, v);

    let round_up = match cmp {
        Ordering::Less => false,
        Ordering::Greater => true,
        Ordering::Equal => (q[1] & 1) == 1,
    };

    if round_up {
        let mut carry = true;
        for q_i in q[1..].iter_mut() {
            let (res, c) = q_i.overflowing_add(if carry { 1 } else { 0 });
            *q_i = res;
            carry = c;
            if !carry {
                break;
            }
        }

        if carry {
            let top_idx = q.len() - 1;
            q[top_idx] = 1u64 << 63;
            return true;
        }
    }

    false
}

#[inline]
fn compare_limbs(a: &[u64], b: &[u64]) -> Ordering {
    let max_len = a.len().max(b.len());

    for i in (0..max_len).rev() {
        let a_limb = a.get(i).copied().unwrap_or(0);
        let b_limb = b.get(i).copied().unwrap_or(0);

        match a_limb.cmp(&b_limb) {
            Ordering::Equal => continue,
            other => return other,
        }
    }

    Ordering::Equal
}
