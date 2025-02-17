use super::affine::{add, conditioned_negate, negate, phi, Affine};
use super::decomposition::ScalarDecomposition;
use super::utils::{allocate_base_from_bn254_fq, mux_16, mux_8};

use crate::bn254::{BN256BaseNNField, BN256Fq};

use boojum::cs::traits::cs::ConstraintSystem;
use boojum::field::SmallField;
use boojum::gadgets::num::Num;
use boojum::pairing::ff::PrimeField;

use lazy_static::lazy_static;

lazy_static! {
    /// BETA parameter such that phi(x, y) = (beta*x, y)
    /// is a valid endomorphism for the curve. Note
    /// that it is possible to use one since 3 divides prime order - 1.
    /// Detailed explanation can be found in file `endomorphism.sage` in `sage` folder.
    static ref BETA: BN256Fq = BN256Fq::from_str("2203960485148121921418603742825762020974279258880205651966").unwrap();
}

pub(super) struct Precomputations<F: SmallField> {
    /// -P, P
    pub(super) table_p: [Affine<F>; 2],
    /// -Q, Q
    pub(super) table_q: [Affine<F>; 2],
    /// -φ(P), φ(P)
    pub(super) table_phi_p: [Affine<F>; 2],
    /// -φ(Q), φ(Q)
    pub(super) table_phi_q: [Affine<F>; 2],

    /// -P-Q, P+Q, P-Q, -P+Q
    table_s: [Affine<F>; 4],
    /// -φ(P)-φ(Q), φ(P)+φ(Q), φ(P)-φ(Q), -φ(P)+φ(Q)
    table_phi_s: [Affine<F>; 4],

    /// ±P ± Q ± φ(P) ± φ(Q)
    pub(super) combinations: [Affine<F>; 16],
}

impl<F: SmallField> Precomputations<F> {
    pub(super) fn compute<CS>(
        cs: &mut CS,
        p: &Affine<F>,
        q: &Affine<F>,
        decomposition: &ScalarDecomposition<F>,
    ) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        let (table_p, table_q) = Self::compute_tables_p_q(cs, p, q, decomposition);
        let (table_phi_p, table_phi_q) = Self::compute_tables_phi_p_phi_q(cs, p, q, decomposition);

        let table_s = Self::compute_table_s(cs, &table_p, &table_q);
        let table_phi_s = Self::compute_table_phi_s(cs, &table_phi_p, &table_phi_q);

        let combinations = Self::compute_combinations(cs, &table_s, &table_phi_s);

        Self {
            table_p,
            table_q,
            table_phi_p,
            table_phi_q,
            table_s,
            table_phi_s,
            combinations,
        }
    }

    fn compute_tables_p_q<CS>(
        cs: &mut CS,
        p: &Affine<F>,
        q: &Affine<F>,
        decomposition: &ScalarDecomposition<F>,
    ) -> ([Affine<F>; 2], [Affine<F>; 2])
    where
        CS: ConstraintSystem<F>,
    {
        let p = conditioned_negate(cs, decomposition.u0.1, &p);
        let q = conditioned_negate(cs, decomposition.v0.1, &q);
        let neg_p = negate(cs, &p);
        let neg_q = negate(cs, &q);

        ([neg_p, p], [neg_q, q])
    }

    fn compute_tables_phi_p_phi_q<CS>(
        cs: &mut CS,
        p: &Affine<F>,
        q: &Affine<F>,
        decomposition: &ScalarDecomposition<F>,
    ) -> ([Affine<F>; 2], [Affine<F>; 2])
    where
        CS: ConstraintSystem<F>,
    {
        let mut beta = allocate_base_from_bn254_fq(cs, *BETA);

        let mut phi_p = conditioned_negate(cs, decomposition.u1.1, &p);
        let mut phi_q = conditioned_negate(cs, decomposition.v1.1, &q);
        phi(cs, &mut phi_p, &mut beta);
        phi(cs, &mut phi_q, &mut beta);

        let neg_phi_p = negate(cs, &phi_p);
        let neg_phi_q = negate(cs, &phi_q);

        ([neg_phi_p, phi_p], [neg_phi_q, phi_q])
    }

    fn compute_table_s<CS>(
        cs: &mut CS,
        table_p: &[Affine<F>; 2],
        table_q: &[Affine<F>; 2],
    ) -> [Affine<F>; 4]
    where
        CS: ConstraintSystem<F>,
    {
        // -P-Q, P+Q, P-Q, -P+Q
        let s0 = unsafe { add(cs, &table_p[0], &table_q[0]) };
        let s1 = negate(cs, &s0);
        let s2 = unsafe { add(cs, &table_p[1], &table_q[0]) };
        let s3 = negate(cs, &s2);

        [s0, s1, s2, s3]
    }

    fn compute_table_phi_s<CS>(
        cs: &mut CS,
        table_phi_p: &[Affine<F>; 2],
        table_phi_q: &[Affine<F>; 2],
    ) -> [Affine<F>; 4]
    where
        CS: ConstraintSystem<F>,
    {
        // -φ(P)-φ(Q), φ(P)+φ(Q), φ(P)-φ(Q), -φ(P)+φ(Q)
        let phi_s0 = unsafe { add(cs, &table_phi_p[0], &table_phi_q[0]) };
        let phi_s1 = negate(cs, &phi_s0);
        let phi_s2 = unsafe { add(cs, &table_phi_p[1], &table_phi_q[0]) };
        let phi_s3 = negate(cs, &phi_s2);

        [phi_s0, phi_s1, phi_s2, phi_s3]
    }

    fn compute_combinations<CS>(
        cs: &mut CS,
        table_s: &[Affine<F>; 4],
        table_phi_s: &[Affine<F>; 4],
    ) -> [Affine<F>; 16]
    where
        CS: ConstraintSystem<F>,
    {
        let c0 = unsafe { add(cs, &table_s[1], &table_phi_s[1]) }; // +P + Q + φ(P) + φ(Q)
        let c1 = unsafe { add(cs, &table_s[1], &table_phi_s[2]) }; // +P + Q + φ(P) - φ(Q)
        let c2 = unsafe { add(cs, &table_s[1], &table_phi_s[3]) }; // +P + Q - φ(P) + φ(Q)
        let c3 = unsafe { add(cs, &table_s[1], &table_phi_s[0]) }; // +P + Q - φ(P) - φ(Q)
        let c4 = unsafe { add(cs, &table_s[2], &table_phi_s[1]) }; // +P - Q + φ(P) + φ(Q)
        let c5 = unsafe { add(cs, &table_s[2], &table_phi_s[2]) }; // +P - Q + φ(P) - φ(Q)
        let c6 = unsafe { add(cs, &table_s[2], &table_phi_s[3]) }; // +P - Q - φ(P) + φ(Q)
        let c7 = unsafe { add(cs, &table_s[2], &table_phi_s[0]) }; // +P - Q - φ(P) - φ(Q)
        let c8 = negate(cs, &c7); //  -P + Q + φ(P) + φ(Q)
        let c9 = negate(cs, &c6); //  -P + Q + φ(P) - φ(Q)
        let c10 = negate(cs, &c5); // -P + Q - φ(P) + φ(Q)
        let c11 = negate(cs, &c4); // -P + Q - φ(P) - φ(Q)
        let c12 = negate(cs, &c3); // -P - Q + φ(P) + φ(Q)
        let c13 = negate(cs, &c2); // -P - Q + φ(P) - φ(Q)
        let c14 = negate(cs, &c1); // -P - Q - φ(P) + φ(Q)
        let c15 = negate(cs, &c0); // -P - Q - φ(P) - φ(Q)

        [
            c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15,
        ]
    }

    /// Returns `x` coordinate of the `combinations[x_selector]` point.
    /// Since first half of 16 `combinations` has same `x` coordinate as second,
    /// `x_selector` may take values in range [0; 7].
    pub(super) fn select_x_from_combinations<CS>(
        &self,
        cs: &mut CS,
        x_selector: &Num<F>,
    ) -> BN256BaseNNField<F>
    where
        CS: ConstraintSystem<F>,
    {
        // Order is based on ±P, ±φ(P), ±Q, ±φ(Q)
        let combinations_x = [
            &self.combinations[15].0,
            &self.combinations[7].0,
            &self.combinations[13].0,
            &self.combinations[5].0,
            &self.combinations[11].0,
            &self.combinations[3].0,
            &self.combinations[9].0,
            &self.combinations[1].0,
        ];

        mux_8(cs, &x_selector, combinations_x)
    }

    /// Returns `y` coordinate of the `combinations[y_selector]` point.
    /// `y_selector` may take values in range [0; 15].
    pub(super) fn select_y_from_combinations<CS>(
        &self,
        cs: &mut CS,
        y_selector: &Num<F>,
    ) -> BN256BaseNNField<F>
    where
        CS: ConstraintSystem<F>,
    {
        // Order is based on ±P, ±φ(P), ±Q, ±φ(Q)
        let combinations_y = [
            &self.combinations[15].1,
            &self.combinations[7].1,
            &self.combinations[13].1,
            &self.combinations[5].1,
            &self.combinations[11].1,
            &self.combinations[3].1,
            &self.combinations[9].1,
            &self.combinations[1].1,
            &self.combinations[14].1,
            &self.combinations[6].1,
            &self.combinations[12].1,
            &self.combinations[4].1,
            &self.combinations[10].1,
            &self.combinations[2].1,
            &self.combinations[8].1,
            &self.combinations[0].1,
        ];

        mux_16(cs, &y_selector, combinations_y)
    }
}
