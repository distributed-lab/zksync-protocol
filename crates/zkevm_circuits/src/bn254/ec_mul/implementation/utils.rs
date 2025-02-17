use crate::bn254::{
    BN256BaseNNField, BN256BaseWitness, BN256Fq, BN256Fr, BN256ScalarNNField, BN256ScalarWitness,
};

use boojum::cs::traits::cs::ConstraintSystem;
use boojum::field::SmallField;
use boojum::gadgets::boolean::Boolean;
use boojum::gadgets::non_native_field::traits::NonNativeField;
use boojum::gadgets::num::Num;
use boojum::gadgets::traits::allocatable::CSAllocatable;
use boojum::pairing::ff::PrimeField;

use num_bigint::BigInt;

/// Allocate BN254 scalar field element from `v` BigInt.
pub(super) unsafe fn allocate_scalar_from_bigint<F, CS>(
    cs: &mut CS,
    v: BigInt,
) -> BN256ScalarNNField<F>
where
    F: SmallField,
    CS: ConstraintSystem<F>,
{
    let v = bigint_to_bn254_fr(&v);
    allocate_scalar_from_bn254_fr(cs, v)
}

/// Allocate BN254 scalar field element from off-circuit `v` scalar.
pub(super) fn allocate_scalar_from_bn254_fr<F, CS>(cs: &mut CS, v: BN256Fr) -> BN256ScalarNNField<F>
where
    F: SmallField,
    CS: ConstraintSystem<F>,
{
    let v = BN256ScalarWitness::set(v);

    BN256ScalarNNField::allocate(cs, v)
}

/// Allocate BN254 base field element from off-circuit `v` base.
pub(super) fn allocate_base_from_bn254_fq<F, CS>(cs: &mut CS, v: BN256Fq) -> BN256BaseNNField<F>
where
    F: SmallField,
    CS: ConstraintSystem<F>,
{
    let v = BN256BaseWitness::set(v);

    BN256BaseNNField::allocate(cs, v)
}

/// Convert BN254 off-circuit scalar into BigInt.
pub(super) fn bn254_fr_to_bigint(v: &BN256Fr) -> BigInt {
    use num_traits::Num;
    use zkevm_opcode_defs::bn254::to_hex;
    BigInt::from_str_radix(&to_hex(v), 16).unwrap()
}

/// Convert BigInt into BN254 off-circuit scalar.
pub(super) unsafe fn bigint_to_bn254_fr(v: &BigInt) -> BN256Fr {
    BN256Fr::from_str(&v.to_str_radix(10)).unwrap()
}

pub(super) fn mux_16<F, CS>(
    cs: &mut CS,
    index: &Num<F>,
    candidates: [&BN256BaseNNField<F>; 16],
) -> BN256BaseNNField<F>
where
    F: SmallField,
    CS: ConstraintSystem<F>,
{
    // Since bits are LSB decomposed, need to reverse candidates.
    let mut candidates = candidates.clone();
    candidates.reverse();

    let bits: [Boolean<F>; 4] = index.spread_into_bits(cs);

    let p0 = mux2(cs, bits[0], candidates[0], candidates[1]);
    let p1 = mux2(cs, bits[0], candidates[2], candidates[3]);
    let p2 = mux2(cs, bits[0], candidates[4], candidates[5]);
    let p3 = mux2(cs, bits[0], candidates[6], candidates[7]);
    let p4 = mux2(cs, bits[0], candidates[8], candidates[9]);
    let p5 = mux2(cs, bits[0], candidates[10], candidates[11]);
    let p6 = mux2(cs, bits[0], candidates[12], candidates[13]);
    let p7 = mux2(cs, bits[0], candidates[14], candidates[15]);

    let p01 = mux2(cs, bits[1], &p0, &p1);
    let p23 = mux2(cs, bits[1], &p2, &p3);
    let p45 = mux2(cs, bits[1], &p4, &p5);
    let p67 = mux2(cs, bits[1], &p6, &p7);

    let p0123 = mux2(cs, bits[2], &p01, &p23);
    let p4567 = mux2(cs, bits[2], &p45, &p67);

    mux2(cs, bits[3], &p0123, &p4567)
}

pub(super) fn mux_8<F, CS>(
    cs: &mut CS,
    index: &Num<F>,
    candidates: [&BN256BaseNNField<F>; 8],
) -> BN256BaseNNField<F>
where
    F: SmallField,
    CS: ConstraintSystem<F>,
{
    // Since bits are LSB decomposed, need to reverse candidates.
    let mut candidates = candidates.clone();
    candidates.reverse();

    let bits: [Boolean<F>; 3] = index.spread_into_bits(cs);

    let p0 = mux2(cs, bits[0], candidates[0], candidates[1]);
    let p1 = mux2(cs, bits[0], candidates[2], candidates[3]);
    let p2 = mux2(cs, bits[0], candidates[4], candidates[5]);
    let p3 = mux2(cs, bits[0], candidates[6], candidates[7]);

    let p01 = mux2(cs, bits[1], &p0, &p1);
    let p23 = mux2(cs, bits[1], &p2, &p3);

    mux2(cs, bits[2], &p01, &p23)
}

#[inline(always)]
fn mux2<F, CS>(
    cs: &mut CS,
    flag: Boolean<F>,
    left: &BN256BaseNNField<F>,
    right: &BN256BaseNNField<F>,
) -> BN256BaseNNField<F>
where
    F: SmallField,
    CS: ConstraintSystem<F>,
{
    BN256BaseNNField::conditionally_select(cs, flag, left, right)
}
