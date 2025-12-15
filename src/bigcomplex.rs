use crate::bigfloat::BigFloat;

use std::ops::{Add, Div, Mul, Sub};

#[derive(Debug, Clone, Copy)]
pub struct BigComplex<const LIMBS: usize> {
    pub re: BigFloat<LIMBS>,
    pub im: BigFloat<LIMBS>,
}

impl<const LIMBS: usize> BigComplex<LIMBS> {
    pub fn from_bigfloat(re: &BigFloat<LIMBS>, im: &BigFloat<LIMBS>) -> Self {
        Self { re: *re, im: *im }
    }

    pub fn from_float(re: f64, im: f64) -> Self {
        Self {
            re: BigFloat::<LIMBS>::from(re),
            im: BigFloat::<LIMBS>::from(im),
        }
    }

    pub fn norm_sq(&self) -> BigFloat<LIMBS>
    where
        [(); 2 * LIMBS + 1]:,
    {
        self.im * self.im + self.re * self.re
    }
}

// Operations with standard types

// Add
// F64
impl<const LIMBS: usize> Add<f64> for BigComplex<LIMBS> {
    type Output = Self;

    fn add(self, other: f64) -> Self {
        self + BigComplex::<LIMBS>::from(other)
    }
}

// U64
impl<const LIMBS: usize> Add<u64> for BigComplex<LIMBS> {
    type Output = Self;

    fn add(self, other: u64) -> Self {
        self + BigComplex::<LIMBS>::from(other)
    }
}

// Sub
// F64
impl<const LIMBS: usize> Sub<f64> for BigComplex<LIMBS> {
    type Output = Self;

    fn sub(self, other: f64) -> Self {
        self - BigComplex::<LIMBS>::from(other)
    }
}

// U64
impl<const LIMBS: usize> Sub<u64> for BigComplex<LIMBS> {
    type Output = Self;

    fn sub(self, other: u64) -> Self {
        self - BigComplex::<LIMBS>::from(other)
    }
}

// Mul
// F64
impl<const LIMBS: usize> Mul<f64> for BigComplex<LIMBS>
where
    [(); 2 * LIMBS + 1]:,
{
    type Output = Self;

    fn mul(self, other: f64) -> Self {
        self * BigComplex::<LIMBS>::from(other)
    }
}

// U64
impl<const LIMBS: usize> Mul<u64> for BigComplex<LIMBS>
where
    [(); 2 * LIMBS + 1]:,
{
    type Output = Self;

    fn mul(self, other: u64) -> Self {
        self * BigComplex::<LIMBS>::from(other)
    }
}

// Div
// F64
impl<const LIMBS: usize> Div<f64> for BigComplex<LIMBS>
where
    [(); 2 * LIMBS + 1]:,
    [(); LIMBS + 1]:,
{
    type Output = Self;

    fn div(self, other: f64) -> Self {
        self / BigComplex::<LIMBS>::from(other)
    }
}

// Addition

impl<const LIMBS: usize> Add for BigComplex<LIMBS> {
    type Output = Self;

    fn add(self, other: Self) -> Self {
        Self {
            re: self.re + other.re,
            im: self.im + other.im,
        }
    }
}

impl<const LIMBS: usize> Add<BigFloat<LIMBS>> for BigComplex<LIMBS> {
    type Output = Self;

    fn add(self, other: BigFloat<LIMBS>) -> Self {
        Self {
            re: self.re + other,
            im: self.im,
        }
    }
}

// Subtraction

impl<const LIMBS: usize> Sub for BigComplex<LIMBS> {
    type Output = Self;

    fn sub(self, other: Self) -> Self {
        Self {
            re: self.re - other.re,
            im: self.im - other.im,
        }
    }
}

// Multiplication

impl<const LIMBS: usize> Mul for BigComplex<LIMBS>
where
    [(); 2 * LIMBS + 1]:,
{
    type Output = Self;

    fn mul(self, other: Self) -> Self {
        Self {
            re: self.re * other.re - self.im * other.im,
            im: self.re * other.im + other.re * self.im,
        }
    }
}

// Division

impl<const LIMBS: usize> Div for BigComplex<LIMBS>
where
    [(); 2 * LIMBS + 1]:,
    [(); LIMBS + 1]:,
{
    type Output = Self;

    fn div(self, other: Self) -> Self {
        Self {
            re: (self.re * other.re + self.im * other.im) / (other.re.powi(2) + other.im.powi(2)),
            im: (self.re * other.re - self.im * other.im) / (other.re.powi(2) + other.im.powi(2)),
        }
    }
}

impl<const LIMBS: usize> From<f64> for BigComplex<LIMBS> {
    fn from(value: f64) -> Self {
        Self {
            re: BigFloat::<LIMBS>::from(value),
            im: BigFloat::<LIMBS>::zero(),
        }
    }
}

impl<const LIMBS: usize> From<u64> for BigComplex<LIMBS> {
    fn from(value: u64) -> Self {
        Self {
            re: BigFloat::<LIMBS>::from(value),
            im: BigFloat::<LIMBS>::zero(),
        }
    }
}
