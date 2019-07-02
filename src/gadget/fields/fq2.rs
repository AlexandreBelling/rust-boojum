use bellman_ce::pairing::{
    Engine
};

use bellman_ce::{
    // SynthesisError, 
    // Variable
    ConstraintSystem, 
    //LinearCombination, 
};

use bellman_ce::pairing::ff::{
    Field,
};

use super::fq::{
    Fq
};

use crate::fields::{ Fp2Parameters, Fp2 };

//use bellman_ce::pairing::ff::{ Field };

pub struct Fq2<E: Engine> {
    pub c0: Fq<E>,
    pub c1: Fq<E>
}

impl<E: Engine> Fq2<E> {

    #[allow(dead_code)]
    pub fn new(
        c0: Fq<E>,
        c1: Fq<E>,
    ) -> Self {

        Self{
            c0: c0,
            c1: c1,
        }
    }

    #[allow(dead_code)]
    pub fn from_fp2_alloc<CS>(
        cs: &mut CS,
        value: &Fp2<E>,
    ) -> Self 
        where CS: ConstraintSystem<E>
    {
        Self{
            c0: Fq::<E>::alloc(cs, value.c0),
            c1: Fq::<E>::alloc(cs, value.c1),
        }
    }

    #[allow(dead_code)]
    pub fn value(&self) -> Fp2<E> 
    {
        Fp2::<E>::new(self.c0.value, self.c1.value)
    }

    #[allow(dead_code)]
    fn one<CS>() -> Self
        where CS: ConstraintSystem<E>
    {
        Self {
            c0: Fq::<E>::one::<CS>(),
            c1: Fq::<E>::zero::<CS>(),
        }
    }

    #[allow(dead_code)]
    pub fn negate(&self) -> Self {
        Self{
            c0: self.c0.negate(),
            c1: self.c1.negate()
        }
    }

     #[allow(dead_code)]
    pub fn mul_by_constant(&self, coeff: E::Fr) -> Self {
        Self{
            c0: self.c0.mul_by_constant(coeff),
            c1: self.c1.mul_by_constant(coeff),
        }
    }

    #[allow(dead_code)]
    pub fn add(
        &self,
        other: &Self,
    ) -> Self {

        Self{
            c0: self.c0.add(&other.c0),
            c1: self.c1.add(&other.c1)
        }
    }

    #[allow(dead_code)]
    pub fn sub(
        &self,
        other: &Self,
    ) -> Self {

        Self{
            c0: self.c0.sub(&other.c0),
            c1: self.c1.sub(&other.c1)
        }
    }

    #[allow(dead_code)]
    pub fn mul<CS, P>(
        &self,
        cs: &mut CS,
        other: &Self,
    ) -> Self 
        where CS: ConstraintSystem<E>, P: Fp2Parameters<E>
    {
        let mut mul_cs = cs.namespace(|| "Fp2 multiplication");

        // Karatsuba multiplication for Fp2:
        //     v0 = A.c0 * B.c0
        //     v1 = A.c1 * B.c1
        //     result.c0 = v0 + non_residue * v1
        //     result.c1 = (A.c0 + A.c1) * (B.c0 + B.c1) - v0 - v1
        // Enforced with 3 constraints:
        //     A.c1 * B.c1 = v1
        //     A.c0 * B.c0 = result.c0 - non_residue * v1
        //     (A.c0+A.c1)*(B.c0+B.c1) = result.c1 + result.c0 + (1 - non_residue) * v1
        // Reference:
        // "Multiplication and Squaring on Pairing-Friendly Fields"
        // Devegili, OhEigeartaigh, Scott, Dahab

        let v0 = self.c0.mul(&mut mul_cs.namespace(|| "B.c0 = v0"), &other.c0);
        let v1 = self.c1.mul(&mut mul_cs.namespace(|| "B.c1 = v1"), &other.c1);

        let c0 = {
            let non_residue_times_v1 = v1.mul_by_constant(P::NONRESIDUE);
            v0.add(
                &non_residue_times_v1
            )
        };

        let c1 = {
            let a0_plus_a1 = self.c0.add(&self.c1);
            let b0_plus_b1 = other.c0.add(&other.c1);
            let a0_plus_a1_times_b0_plus_b1 = a0_plus_a1.mul(
                &mut mul_cs.namespace(|| "(A.c0+A.c1)*(B.c0+B.c1)"), 
                &b0_plus_b1
            );

            a0_plus_a1_times_b0_plus_b1
                .sub(&v0)
                .sub(&v1)
        };

        Self{
            c0: c0,
            c1: c1
        }
    }

    #[allow(dead_code)]
    pub fn square<CS, P>(
        &self,
        cs: &mut CS,
    ) -> Self 
        where CS: ConstraintSystem<E>, P: Fp2Parameters<E>
    {
        let mut sqr_cs = cs.namespace(|| "Fp2 squaring");

        // From Libsnark/fp2_gadget.tcc
        // Complex multiplication for Fp2:
        //     v0 = A.c0 * A.c1
        //     result.c0 = (A.c0 + A.c1) * (A.c0 + non_residue * A.c1) - (1 +
        // non_residue) * v0     
        // result.c1 = 2 * v0
        // Enforced with 2 constraints:
        //     (2*A.c0) * A.c1 = result.c1
        //     (A.c0 + A.c1) * (A.c0 + non_residue * A.c1) = result.c0 + result.c1 * (1
        // + non_residue)/2 Reference:
        //     "Multiplication and Squaring on Pairing-Friendly Fields"
        //     Devegili, OhEigeartaigh, Scott, Dahab
        
        let v0 = self.c0.mul(&mut sqr_cs.namespace(|| "v0 = A.c0 * A.c1"), &self.c1);
        
        let c0 = {
            // (A.c0 + A.c1)
            let a0_plus_a1 = self.c0.add(&self.c1);
            // (A.c0 + non_residue * A.c1)
            let a0_plus_non_residue_c1 = self.c1.mul_by_constant(P::NONRESIDUE).add(&self.c0);
            // (1 + non_residue) * v0
            let one_plus_nonresidue = {
                let mut res = E::Fr::one();
                res.add_assign(&P::NONRESIDUE);
                res
            };
            let one_plus_non_residue_v0 = v0.mul_by_constant(one_plus_nonresidue);
            // A.c0 + A.c1) * (A.c0 + non_residue * A.c1) - (1 + non_residue) * v0
            a0_plus_a1.mul(&mut sqr_cs.namespace(|| "(A.c0 + A.c1) * (A.c0 + non_residue * A.c1)"),
                    &a0_plus_non_residue_c1,
                )
                .add(&one_plus_non_residue_v0)
        };

        let c1 = self.c1.double();

        Self{
            c0: c0,
            c1: c1
        }
    }

    #[allow(dead_code)]
    pub fn inverse<CS, P>(
        &self,
        cs: &mut CS,
    ) -> Option<Self> 
        where CS: ConstraintSystem<E>, P: Fp2Parameters<E>
    {
        let mut inv_cs = cs.namespace(|| "Fp2 inversion");
        // Karatsuba multiplication for Fp2 with the inverse:
        //     v0 = A.c0 * B.c0
        //     v1 = A.c1 * B.c1
        //
        //      1 = v0 + non_residue * v1
        //  => v0 = 1 - non_residue * v1
        //
        //      0 = result.c1 = (A.c0 + A.c1) * (B.c0 + B.c1) - v0 - v1
        //  => v0 + v1 = (A.c0 + A.c1) * (B.c0 + B.c1)
        //  => 1 + (1 - non_residue) * v1 = (A.c0 + A.c1) * (B.c0 + B.c1)
        // Enforced with 2 constraints:
        //     A.c1 * B.c1 = v1
        //  => 1 + (1 - non_residue) * v1 = (A.c0 + A.c1) * (B.c0 + B.c1)
        // Reference:
        // "Multiplication and Squaring on Pairing-Friendly Fields"
        // Devegili, OhEigeartaigh, Scott, Dahab

        let output_fp2 = self.value().inverse::<P>();
        if output_fp2.is_none(){
            return None;
        }

        let output_value = Self::from_fp2_alloc(&mut inv_cs, 
            &output_fp2.expect("We just check that output fp2 is not None")
        );

        let v1 = self.c1.mul(
            &mut inv_cs.namespace(|| "A.c1 * B.c1 = v1"),
            &output_value.c1
        );

        let a0_plus_a1 = self.c0.add(&self.c1);
        let b0_plus_b1 = output_value.c0.add(&output_value.c1);

        let one = Fq::<E>::one::<CS>();
        let mut one_minus_residu = E::Fr::one();
        one_minus_residu.sub_assign(&P::NONRESIDUE);

        let rhs = v1
            .mul_by_constant(one_minus_residu)
            .add(&one);

        a0_plus_a1.enforce_mul(
            &mut inv_cs.namespace(|| "1 + (1 - non_residue) * v1 = (A.c0 + A.c1) * (B.c0 + B.c1)"),
            &b0_plus_b1, &rhs
        );

        Some(output_value)
    }

    #[allow(dead_code)]
    pub fn enforce_mul<CS, P>(
        &self,
        cs: &mut CS,
        other: &Self,
        result: &Self
    )
        where CS: ConstraintSystem<E>, P: Fp2Parameters<E>
    {
        // Karatsuba multiplication for Fp2:
        //     v0 = A.c0 * B.c0
        //     v1 = A.c1 * B.c1
        //     result.c0 = v0 + non_residue * v1
        //     result.c1 = (A.c0 + A.c1) * (B.c0 + B.c1) - v0 - v1
        // Enforced with 3 constraints:
        //     A.c1 * B.c1 = v1
        //     A.c0 * B.c0 = result.c0 - non_residue * v1
        //     (A.c0+A.c1)*(B.c0+B.c1) = result.c1 + result.c0 + (1 - non_residue) * v1
        // Reference:
        // "Multiplication and Squaring on Pairing-Friendly Fields"
        // Devegili, OhEigeartaigh, Scott, Dahab
        let mul_cs = &mut cs.namespace(|| "mul");

        // Compute v1
        let v1 = self.c1.mul(&mut mul_cs.namespace(|| "v1"), &other.c1);

        // Perform second check
        let non_residue_times_v1 = v1.mul_by_constant(P::NONRESIDUE);
        let rhs = result.c0.sub(&non_residue_times_v1);
        self.c0.enforce_mul(&mut mul_cs.namespace(|| "second check"), &other.c0, &rhs);

        // Last check
        let a0_plus_a1 = self.c0.add(&self.c1);
        let b0_plus_b1 = other.c0.add(&other.c1);
        let one_minus_non_residue_v1 = v1.sub(&non_residue_times_v1);

        let result_c1_plus_result_c0_plus_one_minus_non_residue_v1 = result
            .c1
            .add(&result.c0)
            .add(&one_minus_non_residue_v1);

        a0_plus_a1.enforce_mul(
            &mut mul_cs.namespace(|| "third check"),
            &b0_plus_b1,
            &result_c1_plus_result_c0_plus_one_minus_non_residue_v1,
        );
    }

    #[allow(dead_code)]
    pub fn frobenius_map_in_place<P>(&self, power: usize) -> Self
        where P: Fp2Parameters<E>
    {
        let mut result = Self::new(
            Fq::<E>::new(self.c0.value, &self.c0.lc), 
            Fq::<E>::new(self.c1.value, &self.c1.lc), 
        );
        result.c1 = result.c1.mul_by_constant(P::FROBENIUS_COEFF_E[power % 2]);
        result
    }

}