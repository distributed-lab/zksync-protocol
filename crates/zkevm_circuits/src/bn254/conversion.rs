use boojum::{
    crypto_bigint::U1024,
    gadgets::{
        non_native_field::{
            implementations::{OverflowTracker, RepresentationForm},
            // traits::NonNativeField,
        },
        u16::UInt16,
    },
    pairing::ff::PrimeField,
};

use std::sync::Arc;

// use boojum::algebraic_props::round_function::AlgebraicRoundFunction;
use boojum::crypto_bigint::Zero;
use boojum::cs::traits::cs::ConstraintSystem;
use boojum::field::SmallField;
use boojum::gadgets::non_native_field::implementations::*;
use boojum::gadgets::num::Num;
use boojum::gadgets::u256::UInt256;
use boojum::gadgets::u32::UInt32;
// use boojum::pairing::CurveAffine;

// use super::*;

/// Converts the `UInt256<F>` element to a non-native field element over `u16`.
pub fn convert_uint256_to_field_element<F, CS, P, const N: usize>(
    cs: &mut CS,
    value: &UInt256<F>,
    params: &Arc<NonNativeFieldOverU16Params<P, N>>,
) -> NonNativeFieldOverU16<F, P, N>
where
    F: SmallField,
    CS: ConstraintSystem<F>,
    P: PrimeField,
{
    // We still have to decompose it into u16 words
    let zero_var = Num::allocated_constant(cs, F::ZERO).get_variable();
    let mut limbs = [zero_var; N];
    assert!(N >= 16);

    for (dst, src) in limbs.array_chunks_mut::<2>().zip(value.inner.iter()) {
        let [b0, b1, b2, b3] = src.to_le_bytes(cs);
        let low = UInt16::from_le_bytes(cs, [b0, b1]);
        let high = UInt16::from_le_bytes(cs, [b2, b3]);

        *dst = [low.get_variable(), high.get_variable()];
    }

    let mut max_value = U1024::from_word(1u64);
    max_value = max_value.shl_vartime(256);
    max_value = max_value.saturating_sub(&U1024::from_word(1u64));

    let (overflows, rem) = max_value.div_rem(&params.modulus_u1024);
    let mut max_moduluses = overflows.as_words()[0] as u32;
    if rem.is_zero().unwrap_u8() != 1 {
        max_moduluses += 1;
    }

    let element = NonNativeFieldOverU16 {
        limbs,
        non_zero_limbs: 16,
        tracker: OverflowTracker { max_moduluses },
        form: RepresentationForm::Normalized,
        params: params.clone(),
        _marker: std::marker::PhantomData,
    };

    element
}

/// Converts the non-native field eelement over `u16` to a `UInt256`.
/// Note that caller must ensure that the field element is normalized,
/// otherwise this will fail.
pub fn convert_field_element_to_uint256<F, CS, P, const N: usize>(
    cs: &mut CS,
    mut value: NonNativeFieldOverU16<F, P, N>,
) -> UInt256<F>
where
    F: SmallField,
    CS: ConstraintSystem<F>,
    P: PrimeField,
{
    assert_eq!(value.form, RepresentationForm::Normalized);
    assert_eq!(value.tracker.max_moduluses, 1);

    let mut limbs = [UInt32::<F>::zero(cs); 8];
    let two_pow_16 = Num::allocated_constant(cs, F::from_u64_unchecked(2u32.pow(16) as u64));
    for (dst, src) in limbs.iter_mut().zip(value.limbs.array_chunks_mut::<2>()) {
        let low = Num::from_variable(src[0]);
        let high = Num::from_variable(src[1]);
        *dst = unsafe {
            UInt32::from_variable_unchecked(
                Num::fma(cs, &high, &two_pow_16, &F::ONE, &low, &F::ONE).get_variable(),
            )
        };
    }

    UInt256 { inner: limbs }
}
