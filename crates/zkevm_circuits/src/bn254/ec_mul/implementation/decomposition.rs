use crate::bn254::{BN256Fr, BN256ScalarNNField};

use super::eisenstein::ComplexNumber;
use super::utils::{
    allocate_scalar_from_bigint, allocate_scalar_from_bn254_fr, bigint_to_bn254_fr,
    bn254_fr_to_bigint,
};
use super::NUM_MULTIPLICATION_STEPS_FOR_WIDTH_4;

use boojum::cs::traits::cs::ConstraintSystem;
use boojum::field::SmallField;
use boojum::gadgets::boolean::Boolean;
use boojum::gadgets::num::Num;
use boojum::gadgets::tables::ByteSplitTable;
use boojum::gadgets::traits::allocatable::CSAllocatable;
use boojum::gadgets::traits::witnessable::CSWitnessable;
use boojum::gadgets::u16::UInt16;
use boojum::pairing::ff::{Field, PrimeField};

use crate::main_vm::decoded_opcode::reg_idx_into_bitspread;
use boojum::field::traits::field_like::PrimeFieldLike;
use lazy_static::lazy_static;
use num_bigint::BigInt;
use num_traits::Signed;
use std::str::FromStr;

lazy_static! {
    /// Lambda parameter
    static ref LAMBDA: BN256Fr = BN256Fr::from_str("4407920970296243842393367215006156084916469457145843978461").unwrap();

    /// `-b1` component of a short vector `v1=(a1, b1)`.
    static ref B1: BN256Fr = {
        let mut b1 = BN256Fr::from_str("147946756881789319000765030803803410728").unwrap();
        b1.negate();
        b1
    };
    /// `-b2` component of a short vector `v2=(a2, b2)`.
    static ref B2: BN256Fr = {
        let mut b2 = BN256Fr::from_str("9931322734385697763").unwrap();
        b2.negate();
        b2
    };

    /// Precomputed value of `-b1/n << 256`.
    static ref G1: BigInt = BigInt::from_str("782660544089080853078787955015628534157").unwrap();
    /// Precomputed value of `b2/n << 256`.
    static ref G2: BigInt = BigInt::from_str("52538187511802934231").unwrap();

    /// Decomposed `BN254` scalar modulus.
    static ref R: ComplexNumber = ComplexNumber {
        a0: BigInt::from_str("9931322734385697763").unwrap(),
        a1: -BigInt::from_str("147946756881789319000765030803803410728").unwrap(),
    };
}

#[derive(Debug, Clone)]
pub(super) struct ScalarDecomposition<F: SmallField> {
    pub u0: (BN256ScalarNNField<F>, Boolean<F>),
    pub u1: (BN256ScalarNNField<F>, Boolean<F>),
    pub v0: (BN256ScalarNNField<F>, Boolean<F>),
    pub v1: (BN256ScalarNNField<F>, Boolean<F>),
}

impl<F> ScalarDecomposition<F>
where
    F: SmallField,
{
    /// Perform decomposition of the scalar `s` with corresponding witness `k`
    /// into 4 "short" (< r/4) vectors.
    pub(super) fn from<CS>(cs: &mut CS, s: &mut BN256ScalarNNField<F>, k: &BN256Fr) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        let (k1, k2) = Self::decompose_glv(k);
        let decomposition = unsafe { Self::half_gcd(cs, k1, k2) };

        // After off-circuit computation, constraint:
        // s*v0 + s*λ*v1 + u0 + λ*u1 = 0

        let mut lambda = allocate_scalar_from_bn254_fr(cs, *LAMBDA);

        let s_v0 = s.mul(cs, &mut decomposition.v0.0.clone());
        let mut lambda_v1 = lambda.mul(cs, &mut decomposition.v1.0.clone());
        let s_lambda_v1 = s.mul(cs, &mut lambda_v1);
        let lambda_u1 = lambda.mul(cs, &mut decomposition.u1.0.clone());

        let mut lhs1 = s_v0.mask_negated(cs, decomposition.v0.1);
        let mut lhs2 = s_lambda_v1.mask_negated(cs, decomposition.v1.1);
        let mut lhs3 = decomposition.u0.0.mask_negated(cs, decomposition.u0.1);
        let mut lhs4 = lambda_u1.mask_negated(cs, decomposition.u1.1);

        let lhs = lhs1
            .add(cs, &mut lhs2)
            .add(cs, &mut lhs3)
            .add(cs, &mut lhs4);

        let mut rhs1 = s_v0.mask(cs, decomposition.v0.1);
        let mut rhs2 = s_lambda_v1.mask(cs, decomposition.v1.1);
        let mut rhs3 = decomposition.u0.0.mask(cs, decomposition.u0.1);
        let mut rhs4 = lambda_u1.mask(cs, decomposition.u1.1);

        let rhs = rhs1
            .add(cs, &mut rhs2)
            .add(cs, &mut rhs3)
            .add(cs, &mut rhs4);

        BN256ScalarNNField::enforce_equal(cs, &lhs, &rhs);

        decomposition
    }

    /// Half GCD Eisenstein decomposition in the number field
    /// `K=Q[w]/f(w)`. This corresponds to K being the Eisenstein ring of
    /// integers i.e. w is a primitive cube root of unity, f(w)=w^2+w+1=0.
    /// Marked `unsafe` as it requires constraining result from the caller.
    unsafe fn half_gcd<CS>(cs: &mut CS, k1: BN256Fr, k2: BN256Fr) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        let k = ComplexNumber::from((k1, k2));
        let [u, v, _] = ComplexNumber::half_gcd(&k, &R);

        let u0_is_neg = Boolean::allocate(cs, u.a0.is_negative());
        let u1_is_neg = Boolean::allocate(cs, u.a1.is_negative());
        let v0_is_neg = Boolean::allocate(cs, v.a0.is_negative());
        let v1_is_neg = Boolean::allocate(cs, v.a1.is_negative());

        let u0 = allocate_scalar_from_bigint(cs, u.a0);
        let u1 = allocate_scalar_from_bigint(cs, u.a1);
        let v0 = allocate_scalar_from_bigint(cs, v.a0);
        let v1 = allocate_scalar_from_bigint(cs, v.a1);

        Self {
            u0: (u0, u0_is_neg),
            u1: (u1, u1_is_neg),
            v0: (v0, v0_is_neg),
            v1: (v1, v1_is_neg),
        }
    }

    /// Off-circuit classical scalar decomposition using efficient GLV endomorphism.
    fn decompose_glv(k: &BN256Fr) -> (BN256Fr, BN256Fr) {
        let k_int = &bn254_fr_to_bigint(k);

        let c1: BigInt = (k_int * &*G2) >> 256;
        let c2: BigInt = (k_int * &*G1) >> 256;

        // q1 = c1 * b1
        let mut q1 = unsafe { bigint_to_bn254_fr(&c1) };
        q1.mul_assign(&B1);

        // q2 = -c2 * b2
        let mut q2 = unsafe { bigint_to_bn254_fr(&c2) };
        q2.mul_assign(&B2);

        // k2 = q2 - q1
        let mut k2 = q2.clone();
        k2.sub_assign(&q1);

        // k1 = k - k2 * λ
        let mut k2_lambda = k2.clone();
        k2_lambda.mul_assign(&LAMBDA);
        let mut k1 = k.clone();
        k1.sub_assign(&k2_lambda);

        (k1, k2)
    }
}

#[derive(Debug, Clone)]
pub(super) struct BitScalarDecomposition<F: SmallField> {
    pub u0_bits: Vec<Num<F>>,
    pub u1_bits: Vec<Num<F>>,
    pub v0_bits: Vec<Num<F>>,
    pub v1_bits: Vec<Num<F>>,
}

impl<F: SmallField> BitScalarDecomposition<F> {
    pub(super) fn from<CS>(cs: &mut CS, decomposition: ScalarDecomposition<F>) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        let u0_bits = Self::scalar_to_bits(cs, decomposition.u0.0);
        let u1_bits = Self::scalar_to_bits(cs, decomposition.u1.0);
        let v0_bits = Self::scalar_to_bits(cs, decomposition.v0.0);
        let v1_bits = Self::scalar_to_bits(cs, decomposition.v1.0);

        Self {
            u0_bits,
            u1_bits,
            v0_bits,
            v1_bits,
        }
    }

    fn scalar_to_bits<CS>(cs: &mut CS, scalar: BN256ScalarNNField<F>) -> Vec<Num<F>>
    where
        CS: ConstraintSystem<F>,
    {
        todo!()
    }

    /// Compose 3-bit index from scalar bit decomposition at `i`.
    /// If selectorY < 8: selectorX = selectorY
    /// If selectorY >= 8: selectorX = 15 - selectorY
    pub(super) fn selector_x<CS>(&self, cs: &mut CS, i: usize, selector_y: &Num<F>) -> Num<F>
    where
        CS: ConstraintSystem<F>,
    {
        let one = Num::allocated_constant(cs, F::one(&mut ()));
        let two = Num::allocated_constant(cs, F::from_raw_u64_unchecked(2));
        let fifteen = Num::allocated_constant(cs, F::from_raw_u64_unchecked(15));

        let p1 = self.v1_bits[i].mul(cs, &two);
        let p2 = self.v1_bits[i].mul(cs, &fifteen);

        // 1 - v1[i] * 2
        let p3 = one.sub(cs, &p1);

        // selector_y * (1 - v1[i] * 2)
        let p4 = selector_y.mul(cs, &p3);

        // selector_y * (1 - v1[i] * 2) - v1[i] * 15
        p4.add(cs, &p2)
    }

    /// Compose 4-bit index from scalar bit decomposition at `i`.
    pub(super) fn selector_y<CS>(&self, cs: &mut CS, i: usize) -> Num<F>
    where
        CS: ConstraintSystem<F>,
    {
        let parts: [Num<F>; 4] = [
            self.u0_bits[i],
            self.u1_bits[i],
            self.v0_bits[i],
            self.v1_bits[i],
        ];
        let parts = parts.as_variables_set();

        let input = [
            (parts[0], F::from_raw_u64_unchecked(1)),
            (parts[1], F::from_raw_u64_unchecked(2)),
            (parts[2], F::from_raw_u64_unchecked(4)),
            (parts[3], F::from_raw_u64_unchecked(8)),
        ];

        Num::linear_combination(cs, &input)
    }
}
