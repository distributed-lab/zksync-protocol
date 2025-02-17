use super::utils::allocate_base_from_bn254_fq;

use crate::bn254::{bn254_base_field_params, BN256Affine, BN256BaseNNField, BN256Fq, BN256Fr};

use boojum::config::{CSConfig, CSWitnessEvaluationConfig};
use boojum::cs::traits::cs::ConstraintSystem;
use boojum::field::SmallField;
use boojum::gadgets::boolean::Boolean;
use boojum::gadgets::non_native_field::traits::NonNativeField;
use boojum::gadgets::traits::witnessable::WitnessHookable;
use boojum::pairing::ff::{Field, PrimeField};
use boojum::pairing::{CurveAffine, CurveProjective};

use lazy_static::lazy_static;
use std::sync::Arc;

lazy_static! {
    /// [2^SUBSCALAR_BITLENGTH] * G
    static ref GM: (BN256Fq, BN256Fq) = (
        BN256Fq::from_str(
            "20947751279411573967585707957796076884838306892329084570991215098141587145326"
        )
        .unwrap(),
        BN256Fq::from_str(
            "10881143085651043635655119061072151249898091434241810000875579880240699672420"
        )
        .unwrap(),
    );
}

pub(super) type Affine<F> = (BN256BaseNNField<F>, BN256BaseNNField<F>);

/// Computes `a + b`.
/// Based on https://arxiv.org/pdf/math/0208038 (Section 3.1).
/// Marked `unsafe` as requires `a` and `b` have distinct `x` coordinates.
pub(super) unsafe fn add<F, CS>(cs: &mut CS, a: &Affine<F>, b: &Affine<F>) -> Affine<F>
where
    F: SmallField,
    CS: ConstraintSystem<F>,
{
    let (mut x1, mut y1) = a.clone();
    let (mut x2, mut y2) = b.clone();

    let mut dx = x1.sub(cs, &mut x2);
    let mut dy = y1.sub(cs, &mut y2);

    let mut lambda = dy.div_unchecked(cs, &mut dx);

    let mut x3 = lambda.clone().square(cs);
    x3 = x3.sub(cs, &mut x1);
    x3 = x3.sub(cs, &mut x2);

    let mut y3 = x1.sub(cs, &mut x3);
    y3 = lambda.mul(cs, &mut y3);
    y3 = y3.sub(cs, &mut y1);

    (x3, y3)
}

#[inline(always)]
pub(super) fn negate<F, CS>(cs: &mut CS, &(ref x, ref y): &Affine<F>) -> Affine<F>
where
    F: SmallField,
    CS: ConstraintSystem<F>,
{
    (x.clone(), y.clone().negated(cs))
}

#[inline(always)]
pub(super) fn conditioned_negate<F, CS>(
    cs: &mut CS,
    flag: Boolean<F>,
    &(ref x, ref y): &Affine<F>,
) -> Affine<F>
where
    F: SmallField,
    CS: ConstraintSystem<F>,
{
    let neg_y = y.clone().negated(cs);
    let y = BN256BaseNNField::conditionally_select(cs, flag, &neg_y, &y);
    (x.clone(), y)
}

/// Perform scalar multiplication off-circuit.
/// Marked `unsafe` as it requires constraining result from the caller.
pub(super) unsafe fn witness_mul<F, CS>(
    cs: &mut CS,
    point: &Affine<F>,
    scalar: BN256Fr, // scalar is off-circuit here as we hook it to use elsewhere
) -> Affine<F>
where
    F: SmallField,
    CS: ConstraintSystem<F>,
{
    let x = point.0.witness_hook(cs)()
        .map(|v| v.get())
        .unwrap_or_else(|| {
            assert!(!<CS::Config as CSConfig>::WitnessConfig::EVALUATE_WITNESS);
            BN256Fq::zero()
        });
    let y = point.1.witness_hook(cs)()
        .map(|v| v.get())
        .unwrap_or_else(|| {
            assert!(!<CS::Config as CSConfig>::WitnessConfig::EVALUATE_WITNESS);
            BN256Fq::zero()
        });
    let point = BN256Affine::from_xy_unchecked(x, y);

    let result = point.mul(scalar).into_affine();
    let (x, y) = result.as_xy();

    let x = allocate_base_from_bn254_fq(cs, *x);
    let y = allocate_base_from_bn254_fq(cs, *y);

    (x, y)
}

#[inline(always)]
pub(super) fn phi<F, CS>(
    cs: &mut CS,
    (ref mut x, _): &mut Affine<F>,
    beta: &mut BN256BaseNNField<F>, // passing beta here to avoid multiple allocations
) where
    F: SmallField,
    CS: ConstraintSystem<F>,
{
    *x = x.mul(cs, beta);
}

/// Returns `BN254` generator point.
pub(super) fn g<F, CS>(cs: &mut CS) -> Affine<F>
where
    F: SmallField,
    CS: ConstraintSystem<F>,
{
    let one = BN256Affine::one();
    let (x, y) = one.into_xy_unchecked();
    let params = Arc::new(bn254_base_field_params());
    let x = BN256BaseNNField::allocated_constant(cs, x, &params);
    let y = BN256BaseNNField::allocated_constant(cs, y, &params);

    (x, y)
}

/// Returns `BN254` [2^72] * G.
pub(super) fn g_multiples<F, CS>(cs: &mut CS) -> Affine<F>
where
    F: SmallField,
    CS: ConstraintSystem<F>,
{
    let (x, y) = *GM;

    let params = Arc::new(bn254_base_field_params());
    let x = BN256BaseNNField::allocated_constant(cs, x, &params);
    let y = BN256BaseNNField::allocated_constant(cs, y, &params);

    (x, y)
}

/// Computes `2a + b`.
/// Based on https://arxiv.org/pdf/math/0208038 (Section 3.1).
/// Marked `unsafe` as requires `a` and `b` have distinct `x` coordinates .
pub(super) unsafe fn double_and_add<F, CS>(cs: &mut CS, a: &Affine<F>, b: &Affine<F>) -> Affine<F>
where
    F: SmallField,
    CS: ConstraintSystem<F>,
{
    let (mut x1, mut y1) = a.clone();
    let (mut x2, mut y2) = b.clone();

    let mut dx = x1.sub(cs, &mut x2);
    let mut dy = y1.sub(cs, &mut y2);
    let mut lambda1 = dy.div_unchecked(cs, &mut dx);

    let mut x3 = lambda1.clone().square(cs);
    x3 = x3.sub(cs, &mut x1);
    x3 = x3.sub(cs, &mut x2);

    let mut dx = x1.sub(cs, &mut x3);
    let mut dy = y1.double(cs);
    let mut lambda2 = dy.div_unchecked(cs, &mut dx);
    lambda2 = lambda1.sub(cs, &mut lambda2);
    lambda2 = lambda2.negated(cs);

    let mut x4 = lambda2.clone().square(cs);
    x4 = x4.sub(cs, &mut x1);
    x4 = x4.sub(cs, &mut x3);

    let mut y4 = x1.sub(cs, &mut x4);
    y4 = y4.mul(cs, &mut lambda2);
    y4 = y4.sub(cs, &mut y1);

    (x4, y4)
}

pub(super) fn conditionally_select<F, CS>(
    cs: &mut CS,
    flag: Boolean<F>,
    a: &Affine<F>,
    b: &Affine<F>,
) -> Affine<F>
where
    F: SmallField,
    CS: ConstraintSystem<F>,
{
    let x = BN256BaseNNField::conditionally_select(cs, flag, &a.0, &b.0);
    let y = BN256BaseNNField::conditionally_select(cs, flag, &a.1, &b.1);

    (x, y)
}

pub(super) fn enforce_equal<F, CS>(cs: &mut CS, a: &Affine<F>, b: &Affine<F>)
where
    F: SmallField,
    CS: ConstraintSystem<F>,
{
    BN256BaseNNField::enforce_equal(cs, &a.0, &b.0);
    BN256BaseNNField::enforce_equal(cs, &a.1, &b.1);
}
