pub enum BitShiftDirection {
    Left,
    Right,
}

pub struct BitShift {
    pub amount: u64,
    pub direction: BitShiftDirection,
}

// Convention is that positive amount will shift to the right, and negative to the left, like a
// number line
impl BitShift {
    #[inline]
    pub fn new(signed_amount: i64) -> BitShift {
        let direction = match signed_amount.signum() {
            v if v < 0 => BitShiftDirection::Left,
            _ => BitShiftDirection::Right,
        };
        BitShift {
            amount: signed_amount.unsigned_abs(),
            direction,
        }
    }
}
