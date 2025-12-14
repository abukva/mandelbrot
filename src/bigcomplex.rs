use crate::bigfloat::BigFloat;

use std::ops::{Add, Div, Mul, Sub};

#[derive(Debug, Clone)]
pub struct BigComplex<const PRECISION: usize> {
    pub re: BigFloat<PRECISION>,
    pub im: BigFloat<PRECISION>,
}

impl<const PRECISION: usize> BigComplex<PRECISION> {
    pub fn from_bigfloat(re: &BigFloat<PRECISION>, im: &BigFloat<PRECISION>) -> Self {
        Self {
            re: re.clone(),
            im: im.clone(),
        }
    }

    pub fn from_float(re: f64, im: f64) -> Self {
        Self {
            re: BigFloat::<PRECISION>::from(re),
            im: BigFloat::<PRECISION>::from(im),
        }
    }

    pub fn norm_sq(&self) -> BigFloat<PRECISION> {
        &self.im * &self.im + &self.re * &self.re
    }
}

// Operations with standard types

// Add
// F64
impl<const PRECISION: usize> Add<f64> for BigComplex<PRECISION> {
    type Output = Self;

    fn add(self, other: f64) -> Self {
        self + BigComplex::<PRECISION>::from(other)
    }
}

impl<const PRECISION: usize> Add<f64> for &BigComplex<PRECISION> {
    type Output = BigComplex<PRECISION>;

    fn add(self, other: f64) -> Self::Output {
        self.clone() + BigComplex::<PRECISION>::from(other)
    }
}
// U64
impl<const PRECISION: usize> Add<u64> for BigComplex<PRECISION> {
    type Output = Self;

    fn add(self, other: u64) -> Self {
        self + BigComplex::<PRECISION>::from(other)
    }
}

impl<const PRECISION: usize> Add<u64> for &BigComplex<PRECISION> {
    type Output = BigComplex<PRECISION>;

    fn add(self, other: u64) -> Self::Output {
        self.clone() + BigComplex::<PRECISION>::from(other)
    }
}
// Sub
// F64
impl<const PRECISION: usize> Sub<f64> for BigComplex<PRECISION> {
    type Output = Self;

    fn sub(self, other: f64) -> Self {
        self - BigComplex::<PRECISION>::from(other)
    }
}

impl<const PRECISION: usize> Sub<f64> for &BigComplex<PRECISION> {
    type Output = BigComplex<PRECISION>;

    fn sub(self, other: f64) -> Self::Output {
        self.clone() - BigComplex::<PRECISION>::from(other)
    }
}

// U64
impl<const PRECISION: usize> Sub<u64> for BigComplex<PRECISION> {
    type Output = Self;

    fn sub(self, other: u64) -> Self {
        self - BigComplex::<PRECISION>::from(other)
    }
}

impl<const PRECISION: usize> Sub<u64> for &BigComplex<PRECISION> {
    type Output = BigComplex<PRECISION>;

    fn sub(self, other: u64) -> Self::Output {
        self.clone() - BigComplex::<PRECISION>::from(other)
    }
}

// Mul
// F64
impl<const PRECISION: usize> Mul<f64> for BigComplex<PRECISION> {
    type Output = Self;

    fn mul(self, other: f64) -> Self {
        self * BigComplex::<PRECISION>::from(other)
    }
}

impl<const PRECISION: usize> Mul<f64> for &BigComplex<PRECISION> {
    type Output = BigComplex<PRECISION>;

    fn mul(self, other: f64) -> Self::Output {
        self.clone() * BigComplex::<PRECISION>::from(other)
    }
}

// U64
impl<const PRECISION: usize> Mul<u64> for BigComplex<PRECISION> {
    type Output = Self;

    fn mul(self, other: u64) -> Self {
        self * BigComplex::<PRECISION>::from(other)
    }
}

impl<const PRECISION: usize> Mul<u64> for &BigComplex<PRECISION> {
    type Output = BigComplex<PRECISION>;

    fn mul(self, other: u64) -> Self::Output {
        self.clone() * BigComplex::<PRECISION>::from(other)
    }
}

// Div
// F64
impl<const PRECISION: usize> Div<f64> for BigComplex<PRECISION> {
    type Output = Self;

    fn div(self, other: f64) -> Self {
        self / BigComplex::<PRECISION>::from(other)
    }
}

// Addition

impl<const PRECISION: usize> Add<BigComplex<PRECISION>> for BigComplex<PRECISION> {
    type Output = Self;

    fn add(self, other: Self) -> Self {
        Self {
            re: self.re + other.re,
            im: self.im + other.im,
        }
    }
}

impl<const PRECISION: usize> Add<&BigComplex<PRECISION>> for BigComplex<PRECISION> {
    type Output = Self;

    fn add(self, other: &Self) -> Self {
        self + other.clone()
    }
}

impl<const PRECISION: usize> Add<BigComplex<PRECISION>> for &BigComplex<PRECISION> {
    type Output = BigComplex<PRECISION>;

    fn add(self, other: Self::Output) -> Self::Output {
        self.clone() + other
    }
}

impl<const PRECISION: usize> Add<&BigComplex<PRECISION>> for &BigComplex<PRECISION> {
    type Output = BigComplex<PRECISION>;

    fn add(self, other: &BigComplex<PRECISION>) -> BigComplex<PRECISION> {
        self.clone() + other.clone()
    }
}

// Subtraction

impl<const PRECISION: usize> Sub<BigComplex<PRECISION>> for BigComplex<PRECISION> {
    type Output = Self;

    fn sub(self, other: Self) -> Self {
        Self {
            re: self.re - other.re,
            im: self.im - other.im,
        }
    }
}

impl<const PRECISION: usize> Sub<&BigComplex<PRECISION>> for BigComplex<PRECISION> {
    type Output = Self;

    fn sub(self, other: &Self) -> Self {
        self - other.clone()
    }
}

impl<const PRECISION: usize> Sub<BigComplex<PRECISION>> for &BigComplex<PRECISION> {
    type Output = BigComplex<PRECISION>;

    fn sub(self, other: Self::Output) -> Self::Output {
        self.clone() - other
    }
}

impl<const PRECISION: usize> Sub<&BigComplex<PRECISION>> for &BigComplex<PRECISION> {
    type Output = BigComplex<PRECISION>;

    fn sub(self, other: &BigComplex<PRECISION>) -> BigComplex<PRECISION> {
        self.clone() - other.clone()
    }
}

// Multiplication

impl<const PRECISION: usize> Mul<BigComplex<PRECISION>> for BigComplex<PRECISION> {
    type Output = Self;

    fn mul(self, other: Self) -> Self {
        Self {
            re: &self.re * &other.re - &self.im * &other.im,
            im: &self.re * &other.im + &other.re * &self.im,
        }
    }
}

impl<const PRECISION: usize> Mul<&BigComplex<PRECISION>> for BigComplex<PRECISION> {
    type Output = Self;

    fn mul(self, other: &Self) -> Self {
        self * other.clone()
    }
}

impl<const PRECISION: usize> Mul<BigComplex<PRECISION>> for &BigComplex<PRECISION> {
    type Output = BigComplex<PRECISION>;

    fn mul(self, other: Self::Output) -> Self::Output {
        self.clone() * other
    }
}

impl<const PRECISION: usize> Mul<&BigComplex<PRECISION>> for &BigComplex<PRECISION> {
    type Output = BigComplex<PRECISION>;

    fn mul(self, other: &BigComplex<PRECISION>) -> BigComplex<PRECISION> {
        self.clone() * other.clone()
    }
}

// Division

impl<const PRECISION: usize> Div<BigComplex<PRECISION>> for BigComplex<PRECISION> {
    type Output = Self;

    fn div(self, other: Self) -> Self {
        Self {
            re: (&self.re * &other.re + &self.im * &other.im)
                / (other.re.powi(2) + other.im.powi(2)),
            im: (&self.re * &other.re - &self.im * &other.im)
                / (other.re.powi(2) + other.im.powi(2)),
        }
    }
}

impl<const PRECISION: usize> Div<&BigComplex<PRECISION>> for BigComplex<PRECISION> {
    type Output = Self;

    fn div(self, other: &Self) -> Self {
        self / other.clone()
    }
}

impl<const PRECISION: usize> Div<BigComplex<PRECISION>> for &BigComplex<PRECISION> {
    type Output = BigComplex<PRECISION>;

    fn div(self, other: Self::Output) -> Self::Output {
        self.clone() / other
    }
}

impl<const PRECISION: usize> Div<&BigComplex<PRECISION>> for &BigComplex<PRECISION> {
    type Output = BigComplex<PRECISION>;

    fn div(self, other: &BigComplex<PRECISION>) -> BigComplex<PRECISION> {
        self.clone() / other.clone()
    }
}

impl<const PRECISION: usize> From<f64> for BigComplex<PRECISION> {
    fn from(value: f64) -> Self {
        Self {
            re: BigFloat::<PRECISION>::from(value),
            im: BigFloat::<PRECISION>::zero(),
        }
    }
}

impl<const PRECISION: usize> From<u64> for BigComplex<PRECISION> {
    fn from(value: u64) -> Self {
        Self {
            re: BigFloat::<PRECISION>::from(value),
            im: BigFloat::<PRECISION>::zero(),
        }
    }
}
