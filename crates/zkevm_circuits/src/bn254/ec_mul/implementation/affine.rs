use super::utils::allocate_base_from_bn254_fq;

use crate::bn254::{bn254_base_field_params, BN256Affine, BN256BaseNNField, BN256Fq, BN256Fr};

use boojum::config::{CSConfig, CSWitnessEvaluationConfig};
use boojum::cs::traits::cs::ConstraintSystem;
use boojum::field::SmallField;
use boojum::gadgets::boolean::Boolean;
use boojum::gadgets::non_native_field::traits::NonNativeField;
use boojum::gadgets::traits::witnessable::WitnessHookable;
use boojum::pairing::ff::Field;
use boojum::pairing::{CurveAffine, CurveProjective};

use boojum::gadgets::num::Num;
use std::sync::Arc;

pub(super) unsafe fn add<F, CS>(
    cs: &mut CS,
    a: &(BN256BaseNNField<F>, BN256BaseNNField<F>),
    b: &(BN256BaseNNField<F>, BN256BaseNNField<F>),
) -> (BN256BaseNNField<F>, BN256BaseNNField<F>)
where
    F: SmallField,
    CS: ConstraintSystem<F>,
{
    let mut a = a.clone();
    let mut b = b.clone();

    let mut dx = a.0.sub(cs, &mut b.0);
    let mut dy = a.1.sub(cs, &mut b.1);

    let mut slope = dy.div_unchecked(cs, &mut dx);

    let mut x = slope.clone().square(cs);
    x = x.sub(cs, &mut a.0);
    x = x.sub(cs, &mut b.0);

    let mut y = a.0.sub(cs, &mut x);
    y = slope.mul(cs, &mut y);
    y = y.sub(cs, &mut a.1);

    (x, y)
}

#[inline(always)]
pub(super) fn negate<F, CS>(
    cs: &mut CS,
    &(ref x, ref y): &(BN256BaseNNField<F>, BN256BaseNNField<F>),
) -> (BN256BaseNNField<F>, BN256BaseNNField<F>)
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
    &(ref x, ref y): &(BN256BaseNNField<F>, BN256BaseNNField<F>),
) -> (BN256BaseNNField<F>, BN256BaseNNField<F>)
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
    point: (&BN256BaseNNField<F>, &BN256BaseNNField<F>),
    scalar: BN256Fr,
) -> (BN256BaseNNField<F>, BN256BaseNNField<F>)
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
    (ref mut x, _): &mut (BN256BaseNNField<F>, BN256BaseNNField<F>),
    beta: &mut BN256BaseNNField<F>, // passing beta here to avoid multiple allocations
) where
    F: SmallField,
    CS: ConstraintSystem<F>,
{
    *x = x.mul(cs, beta);
}

pub(super) fn g<F, CS>(cs: &mut CS) -> (BN256BaseNNField<F>, BN256BaseNNField<F>)
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

pub(super) fn g_multiples<F, CS>(cs: &mut CS) -> (BN256BaseNNField<F>, BN256BaseNNField<F>)
where
    F: SmallField,
    CS: ConstraintSystem<F>,
{
    g(cs) // todo!
}

/// 2a + b
pub(super) unsafe fn double_and_add<F, CS>(
    cs: &mut CS,
    a: &(BN256BaseNNField<F>, BN256BaseNNField<F>),
    b: &(BN256BaseNNField<F>, BN256BaseNNField<F>),
) -> (BN256BaseNNField<F>, BN256BaseNNField<F>)
where
    F: SmallField,
    CS: ConstraintSystem<F>,
{
    todo!()
}

pub(super) fn conditionally_select<F, CS>(
    cs: &mut CS,
    flag: &Num<F>,
    a: &(BN256BaseNNField<F>, BN256BaseNNField<F>),
    b: &(BN256BaseNNField<F>, BN256BaseNNField<F>),
) -> (BN256BaseNNField<F>, BN256BaseNNField<F>)
where
    F: SmallField,
    CS: ConstraintSystem<F>,
{
    let x = BN256BaseNNField::conditionally_select(cs, flag, &a.0, &b.0);
    let y = BN256BaseNNField::conditionally_select(cs, flag, &a.1, &b.1);

    (x, y)
}

pub(super) fn enforce_equal<F, CS>(
    cs: &mut CS,
    a: &(BN256BaseNNField<F>, BN256BaseNNField<F>),
    b: &(BN256BaseNNField<F>, BN256BaseNNField<F>),
) where
    F: SmallField,
    CS: ConstraintSystem<F>,
{
    BN256BaseNNField::enforce_equal(cs, &a.0, &b.0);
    BN256BaseNNField::enforce_equal(cs, &a.1, &b.1);
}
