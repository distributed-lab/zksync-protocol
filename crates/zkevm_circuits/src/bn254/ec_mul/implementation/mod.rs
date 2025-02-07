use super::*;

use self::affine::{
    add, conditionally_select, double_and_add, enforce_equal, g, g_multiples, witness_mul,
};
use self::decomposition::{BitScalarDecomposition, ScalarDecomposition};
use self::tables::Precomputations;

use boojum::config::{CSConfig, CSWitnessEvaluationConfig};
use boojum::pairing::ff::Field;

mod affine;
mod decomposition;
mod eisenstein;
mod tables;
mod utils;

const BN254_SCALAR_PRIME_BIT_LENGTH: usize = 256;
const NUM_MULTIPLICATION_STEPS_FOR_WIDTH_4: usize = BN254_SCALAR_PRIME_BIT_LENGTH >> 2 + 9;

/// Scalar multiplication over BN254.
pub fn mul<F, CS>(
    cs: &mut CS,
    mut point: BN256SWProjectivePoint<F>,
    mut scalar: BN256ScalarNNField<F>,
) -> (BN256BaseNNField<F>, BN256BaseNNField<F>)
where
    F: SmallField,
    CS: ConstraintSystem<F>,
{
    let p = unsafe { point.convert_to_affine(cs) };

    let k = scalar.witness_hook(cs)()
        .map(|v| v.get())
        .unwrap_or_else(|| {
            assert!(!<CS::Config as CSConfig>::WitnessConfig::EVALUATE_WITNESS);
            BN256Fr::zero()
        });

    let decomposition = ScalarDecomposition::from(cs, &mut scalar, &k);
    let q = unsafe { witness_mul(cs, (&p.0, &p.1), k) };

    let tables = Precomputations::compute(cs, &p, &q, &decomposition);

    // We suppose that the first bit of the sub-scalars is 1 and set:
    // acc = P + Q + φ(P) + φ(Q)
    let acc = tables.combinations[0].clone();

    // Then we add generator point to acc to avoid incomplete additions in
    // the loop, because when doing double-and-add (acc, bi) as (acc+bi)+acc it
    // might happen that acc==bi or acc==-bi. But now we force acc to be
    // different than the stored bi. However, at the end, acc will not be the
    // point at infinity but [2^NUM_MULTIPLICATION_STEPS_FOR_WIDTH_4]G.
    //
    // N.B.: Acc cannot be equal to G, otherwise this means G = -φ²([s+1]P)
    let g = g(cs);
    let mut acc = unsafe { add(cs, &acc, &g) };

    let decomposition_bits = BitScalarDecomposition::from(cs, decomposition);

    for i in (1..NUM_MULTIPLICATION_STEPS_FOR_WIDTH_4).rev() {
        let y_selector = decomposition_bits.selector_y(cs, i);
        let x_selector = decomposition_bits.selector_x(cs, i, &y_selector);

        let x = tables.select_x_from_combinations(cs, &x_selector);
        let y = tables.select_y_from_combinations(cs, &y_selector);

        acc = unsafe { double_and_add(cs, &acc, &(x, y)) };
    }

    // i = 0
    // subtract the P, Q, φ(P), φ(Q) if the first bits are 0
    let acc_sub_p = unsafe { add(cs, &acc, &tables.table_p[0]) };
    let acc = conditionally_select(cs, &decomposition_bits.u0_bits[0], &acc, &acc_sub_p);

    let acc_sub_q = unsafe { add(cs, &acc, &tables.table_q[0]) };
    let acc = conditionally_select(cs, &decomposition_bits.u1_bits[0], &acc, &acc_sub_q);

    let acc_sub_phi_p = unsafe { add(cs, &acc, &tables.table_phi_p[0]) };
    let acc = conditionally_select(cs, &decomposition_bits.v0_bits[0], &acc, &acc_sub_phi_p);

    let acc_sub_phi_q = unsafe { add(cs, &acc, &tables.table_phi_q[0]) };
    let acc = conditionally_select(cs, &decomposition_bits.v1_bits[0], &acc, &acc_sub_phi_q);

    // Acc should be now equal to [2^NUM_MULTIPLICATION_STEPS_FOR_WIDTH_4]G
    let gm = g_multiples(cs);

    enforce_equal(cs, &acc, &gm);

    q
}
