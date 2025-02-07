use super::affine::{add, conditioned_negate, negate, phi};
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

type Affine<F> = (BN256BaseNNField<F>, BN256BaseNNField<F>);

pub(super) struct Precomputations<F: SmallField> {
    /// -P, P
    pub(super) table_p: Vec<Affine<F>>,
    /// -Q, Q
    pub(super) table_q: Vec<Affine<F>>,
    /// -φ(P), φ(P)
    pub(super) table_phi_p: Vec<Affine<F>>,
    /// -φ(Q), φ(Q)
    pub(super) table_phi_q: Vec<Affine<F>>,

    /// -P-Q, P+Q, P-Q, -P+Q
    table_s: Vec<Affine<F>>,
    /// -φ(P)-φ(Q), φ(P)+φ(Q), φ(P)-φ(Q), -φ(P)+φ(Q)
    table_phi_s: Vec<Affine<F>>,

    /// ±P ± Q ± φ(P) ± φ(Q)
    pub(super) combinations: Vec<Affine<F>>,
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
    ) -> (Vec<Affine<F>>, Vec<Affine<F>>)
    where
        CS: ConstraintSystem<F>,
    {
        let p = conditioned_negate(cs, decomposition.u0.1, &p);
        let q = conditioned_negate(cs, decomposition.v1.1, &q);
        let neg_p = negate(cs, &p);
        let neg_q = negate(cs, &q);

        (vec![neg_p, p], vec![neg_q, q])
    }

    fn compute_tables_phi_p_phi_q<CS>(
        cs: &mut CS,
        p: &Affine<F>,
        q: &Affine<F>,
        decomposition: &ScalarDecomposition<F>,
    ) -> (Vec<Affine<F>>, Vec<Affine<F>>)
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

        (vec![neg_phi_p, phi_p], vec![neg_phi_q, phi_q])
    }

    fn compute_table_s<CS>(
        cs: &mut CS,
        table_p: &Vec<Affine<F>>,
        table_q: &Vec<Affine<F>>,
    ) -> Vec<Affine<F>>
    where
        CS: ConstraintSystem<F>,
    {
        let mut table_s = vec![];

        // -P-Q, P+Q, P-Q, -P+Q
        table_s.push(unsafe { add(cs, &table_p[0], &table_q[0]) });
        table_s.push(negate(cs, &table_s[0]));
        table_s.push(unsafe { add(cs, &table_p[0], &table_q[1]) });
        table_s.push(negate(cs, &table_s[2]));

        table_s
    }

    fn compute_table_phi_s<CS>(
        cs: &mut CS,
        table_phi_p: &Vec<Affine<F>>,
        table_phi_q: &Vec<Affine<F>>,
    ) -> Vec<Affine<F>>
    where
        CS: ConstraintSystem<F>,
    {
        // -φ(P)-φ(Q), φ(P)+φ(Q), φ(P)-φ(Q), -φ(P)+φ(Q)
        let mut table_phi_s = vec![];

        table_phi_s.push(unsafe { add(cs, &table_phi_p[0], &table_phi_q[0]) });
        table_phi_s.push(negate(cs, &table_phi_s[0]));
        table_phi_s.push(unsafe { add(cs, &table_phi_p[0], &table_phi_q[1]) });
        table_phi_s.push(negate(cs, &table_phi_s[2]));

        table_phi_s
    }

    fn compute_combinations<CS>(
        cs: &mut CS,
        table_s: &Vec<Affine<F>>,
        table_phi_s: &Vec<Affine<F>>,
    ) -> Vec<Affine<F>>
    where
        CS: ConstraintSystem<F>,
    {
        let b1 = unsafe { add(cs, &table_s[1], &table_phi_s[1]) }; // +P + Q + φ(P) + φ(Q)
        let b2 = unsafe { add(cs, &table_s[1], &table_phi_s[2]) }; // +P + Q + φ(P) - φ(Q)
        let b3 = unsafe { add(cs, &table_s[1], &table_phi_s[3]) }; // +P + Q - φ(P) + φ(Q)
        let b4 = unsafe { add(cs, &table_s[1], &table_phi_s[0]) }; // +P + Q - φ(P) - φ(Q)
        let b5 = unsafe { add(cs, &table_s[2], &table_phi_s[1]) }; // +P - Q + φ(P) + φ(Q)
        let b6 = unsafe { add(cs, &table_s[2], &table_phi_s[2]) }; // +P - Q + φ(P) - φ(Q)
        let b7 = unsafe { add(cs, &table_s[2], &table_phi_s[3]) }; // +P - Q - φ(P) + φ(Q)
        let b8 = unsafe { add(cs, &table_s[2], &table_phi_s[0]) }; // +P - Q - φ(P) - φ(Q)
        let b9 = negate(cs, &b8); //  -P + Q + φ(P) + φ(Q)
        let b10 = negate(cs, &b7); // -P + Q + φ(P) - φ(Q)
        let b11 = negate(cs, &b6); // -P + Q - φ(P) + φ(Q)
        let b12 = negate(cs, &b5); // -P + Q - φ(P) - φ(Q)
        let b13 = negate(cs, &b4); // -P - Q + φ(P) + φ(Q)
        let b14 = negate(cs, &b3); // -P - Q + φ(P) - φ(Q)
        let b15 = negate(cs, &b2); // -P - Q - φ(P) + φ(Q)
        let b16 = negate(cs, &b1); // -P - Q - φ(P) - φ(Q)

        vec![
            b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16,
        ]
    }

    /// Returns `x` coordinate of the `combinations[x_selector]` point.
    /// `x_selector` may take values in range [0; 7].
    /// First half of 16 `combinations` has same `x` coordinate as second.
    pub(super) fn select_x_from_combinations<CS>(
        &self,
        cs: &mut CS,
        x_selector: &Num<F>,
    ) -> BN256BaseNNField<F>
    where
        CS: ConstraintSystem<F>,
    {
        let combinations_x: Vec<&BN256BaseNNField<F>> =
            self.combinations.iter().take(8).map(|(x, _)| x).collect();

        mux_8(cs, &x_selector, &combinations_x)
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
        let combinations_y: Vec<&BN256BaseNNField<F>> =
            self.combinations.iter().map(|(_, y)| y).collect();

        mux_16(cs, &y_selector, &combinations_y)
    }
}
