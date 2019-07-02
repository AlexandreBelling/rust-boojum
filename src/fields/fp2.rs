use bellman_ce::pairing::{ Engine };
use crate::{
    fields::bellman_ce::pairing::ff::{ 
        Field, 
        //SqrtField
    }
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

pub struct Fp2<E: Engine> {
    pub c0: E::Fr,
    pub c1: E::Fr
}

impl<E: Engine> Fp2<E> {

    pub fn new(c0: E::Fr, c1: E::Fr) -> Self {
        Fp2{
            c0: c0,
            c1: c1,
        }
    }

    pub fn is_zero(&self) -> bool {
        self.c0.is_zero() && self.c1.is_zero()
    }

    pub fn inverse<P>(&self) -> Option<Self> 
        where P: Fp2Parameters<E>
    {
        if self.is_zero() {
            None
        } else {
            let mut v0 = self.c0;
            v0.square();
            let mut v1 = self.c1;
            v1.square();
            let mut beta_v1 = v1;
            beta_v1.mul_assign(&P::NONRESIDUE);
            v0.sub_assign(&beta_v1);
            v0 = v0.inverse().expect("v0 cannot be zero because self is not zero");

            let mut tmp = Self {
                c0: self.c0,
                c1: self.c1,
            };

            tmp.c0.mul_assign(&v0);
            tmp.c1.mul_assign(&v0);
            tmp.c1.negate();

            Some(tmp)
        }
    }

}