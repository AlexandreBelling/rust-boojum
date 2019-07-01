use bellman_ce::pairing::{ Engine };
use crate::{
    fields::bellman_ce::pairing::ff::Field
};

pub trait Fp2Parameters<E: Engine>: 'static + Send + Sync {

    const NONRESIDUE: E::Fr;

    const QUADRATIC_NONRESIDUE: (E::Fr, E::Fr);

    /// Coefficients for the Frobenius automorphism.
    const FROBENIUS_COEFF_E: [E::Fr; 2];

    #[inline(always)]
    fn mul_fp_by_nonresidue(fe: &E::Fr) -> E::Fr {
        let mut output: E::Fr = fe.clone();
        output.mul_assign(&Self::NONRESIDUE);
        output
    }
}