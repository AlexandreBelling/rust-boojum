use crate::{
    fields::bellman_ce::pairing::ff::{ 
        Field, 
    }
};

pub trait Fp2Parameters: 'static + Send + Sync {

    type Fp: Field;

    const NONRESIDUE: Self::Fp;
    const QUADRATIC_NONRESIDUE: (Self::Fp, Self::Fp);

    /// Coefficients for the Frobenius automorphism.
    const FROBENIUS_COEFF_E: [Self::Fp; 2];
}

pub struct Fp2<P: Fp2Parameters> {
    pub c0: P::Fp,
    pub c1: P::Fp
}

impl<P: Fp2Parameters> Fp2<P> {

    pub fn new(c0: P::Fp, c1: P::Fp) -> Self {
        Fp2{
            c0: c0,
            c1: c1,
        }
    }

    pub fn is_zero(&self) -> bool {
        self.c0.is_zero() && self.c1.is_zero()
    }

    pub fn inverse(&self) -> Option<Self> 
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