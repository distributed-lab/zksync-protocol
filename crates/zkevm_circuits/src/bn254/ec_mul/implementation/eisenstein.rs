//! Off-circuit implementation of Eisenstein integer arithmetics.
//! Based on:
//! https://github.com/Consensys/gnark-crypto/blob/master/field/eisenstein/eisenstein.go

use num_bigint::BigInt;
use num_traits::{Euclid, One, Signed, Zero};
use std::fmt;
use std::ops::{Add, Mul, Neg, Sub};

/// Arbitrary-precision Eisenstein integer: z = a0 + (a1 * ω)
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct ComplexNumber {
    pub(super) a0: BigInt,
    pub(super) a1: BigInt,
}

impl Neg for ComplexNumber {
    type Output = ComplexNumber;

    fn neg(self) -> Self::Output {
        Self {
            a0: -self.a0,
            a1: -self.a1,
        }
    }
}

impl Add for ComplexNumber {
    type Output = ComplexNumber;

    fn add(self, other: Self) -> Self::Output {
        Self {
            a0: self.a0 + other.a0,
            a1: self.a1 + other.a1,
        }
    }
}

impl Sub for ComplexNumber {
    type Output = ComplexNumber;

    fn sub(self, other: Self) -> Self::Output {
        Self {
            a0: self.a0 - other.a0,
            a1: self.a1 - other.a1,
        }
    }
}

impl Mul for ComplexNumber {
    type Output = ComplexNumber;

    /// (x0 + x1 ω)(y0 + y1 ω) = (x0y0 - x1y1) + (x0y1 + x1y0 - x1y1) ω
    fn mul(self, other: Self) -> Self::Output {
        let a0b0 = &self.a0 * &other.a0;
        let a1b1 = &self.a1 * &other.a1;

        let a0b1 = self.a0 * other.a1;
        let a1b0 = self.a1 * other.a0;

        Self {
            a0: a0b0 - &a1b1,
            a1: a0b1 + a1b0 - a1b1,
        }
    }
}

impl fmt::Display for ComplexNumber {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}+({}*ω)", self.a0, self.a1)
    }
}

impl From<(BigInt, BigInt)> for ComplexNumber {
    fn from(value: (BigInt, BigInt)) -> Self {
        Self {
            a0: value.0,
            a1: value.1,
        }
    }
}

impl ComplexNumber {
    /// Creates 0 + 0*ω.
    pub(super) fn new() -> Self {
        Self {
            a0: BigInt::zero(),
            a1: BigInt::zero(),
        }
    }

    pub(super) fn set_zero(&mut self) {
        self.a0 = BigInt::zero();
        self.a1 = BigInt::zero();
    }

    pub(super) fn set_one(&mut self) {
        self.a0 = BigInt::one();
        self.a1 = BigInt::zero();
    }

    /// **Conjugate**:  
    /// - Computes **(a0 + a1 ω)̄ = (a0 - a1) + (-a1) ω**  
    /// - Returns **a new** `ComplexNumber`.
    pub(super) fn conjugate(&self) -> ComplexNumber {
        ComplexNumber {
            a0: &self.a0 - &self.a1, // a0 - a1
            a1: -&self.a1,           // -a1
        }
    }

    /// Norm: N(a0 + a1 ω) = a0² + a1² - a0·a1
    pub(super) fn norm(&self) -> BigInt {
        let a0_sq = &self.a0 * &self.a0;
        let a1_sq = &self.a1 * &self.a1;
        a0_sq + a1_sq - (&self.a0 * &self.a1)
    }

    /// Compute quotient and remainder: `(q, r) = (x ÷ y, remainder)`
    /// Using Eisenstein integer division.
    pub(super) fn quo_rem(x: &ComplexNumber, y: &ComplexNumber) -> (ComplexNumber, ComplexNumber) {
        let norm_y = y.norm();
        if norm_y.is_zero() {
            panic!("Division by zero in Eisenstein integers!");
        }

        // Compute q = round((x * conj(y)) / norm(y))
        let conj_y = y.conjugate();
        let numerator = x.clone() * conj_y;
        let quotient = ComplexNumber {
            a0: numerator.a0.div_euclid(&norm_y),
            a1: numerator.a1.div_euclid(&norm_y),
        };

        // Compute remainder: r = x - y * q
        let remainder = x.clone() - (y.clone() * quotient.clone());

        (quotient, remainder)
    }

    /// Compute `half_gcd(a, b)`, which returns `[g, v, u]` such that:
    /// - `g = a * u + b * v`
    /// - `|b| < sqrt(a's norm)`
    pub(super) fn half_gcd(a: &ComplexNumber, b: &ComplexNumber) -> [ComplexNumber; 3] {
        let mut a_run = a.clone();
        let mut b_run = b.clone();

        let mut u = ComplexNumber::new();
        u.set_one();
        let mut v = ComplexNumber::new();
        v.set_zero();

        let mut u_ = ComplexNumber::new();
        u_.set_zero();
        let mut v_ = ComplexNumber::new();
        v_.set_one();

        let sqrt_n = a.norm().abs().sqrt();

        while b_run.norm() >= sqrt_n {
            let (q, r) = ComplexNumber::quo_rem(&a_run, &b_run);

            let new_u = u.clone() - (q.clone() * u_.clone());
            let new_v = v.clone() - (q * v_.clone());

            // Update values for next iteration
            a_run = b_run;
            b_run = r;
            u = u_;
            v = v_;
            u_ = new_u;
            v_ = new_v;
        }

        [b_run, v_, u_]
    }
}
