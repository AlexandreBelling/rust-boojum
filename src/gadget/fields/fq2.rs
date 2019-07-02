use bellman_ce::pairing::{
    Engine
};

use bellman_ce::{ConstraintSystem};
use bellman_ce::pairing::ff::{Field};
use super::fq::{Fq};
use crate::fields::{ Fp2Parameters, Fp2 };
use std::marker::PhantomData;

pub struct Fq2<E: Engine, P: Fp2Parameters<E>> {
    pub c0:         Fq<E>,
    pub c1:         Fq<E>,
    _phantom:       PhantomData<P>
}

// trait Fp2Field<E: Engine, P: Fp2Parameters<E>> : Sized {

//     type P: Fp2Parameters<E>;

//     fn mul<CS>(
//         &self,
//         cs: &mut CS,
//         other: &Self,
//     ) -> Self 
//         where CS: ConstraintSystem<E>;

//     fn square<CS>(
//         &self,
//         cs: &mut CS,
//     ) -> Self 
//         where CS: ConstraintSystem<E>;

//     fn inverse<CS>(
//         &self,
//         cs: &mut CS,
//     ) -> Option<Self> 
//         where CS: ConstraintSystem<E>;

//     fn enforce_mul<CS>(
//         &self,
//         cs: &mut CS,
//         other: &Self,
//         result: &Self
//     )
//         where CS: ConstraintSystem<E>;

//     fn frobenius_map(&self, power: usize) -> Self;

// }

impl<E: Engine, P: Fp2Parameters<E>> Fq2<E, P> {

    #[allow(dead_code)]
    pub fn new(
        c0: Fq<E>,
        c1: Fq<E>,
    ) -> Self {

        Self {
            c0:         c0,
            c1:         c1,
            _phantom:   PhantomData,
        }
    }

    #[allow(dead_code)]
    pub fn from_fp2_alloc<CS>(
        cs: &mut CS,
        value: &Fp2<E>,
    ) -> Self 
        where CS: ConstraintSystem<E>
    {
        Self {
            c0: Fq::<E>::alloc(cs, value.c0),
            c1: Fq::<E>::alloc(cs, value.c1),
            _phantom:   PhantomData,
        }
    }

    #[allow(dead_code)]
    pub fn from_fp2_alloc_input<CS>(
        cs: &mut CS,
        value: &Fp2<E>,
    ) -> Self 
        where CS: ConstraintSystem<E>
    {
        Self {
            c0: Fq::<E>::alloc_input(cs, value.c0),
            c1: Fq::<E>::alloc_input(cs, value.c1),
            _phantom:   PhantomData,
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
            _phantom:   PhantomData,
        }
    }

    #[allow(dead_code)]
    pub fn negate(&self) -> Self {
        Self{
            c0: self.c0.negate(),
            c1: self.c1.negate(),
            _phantom:   PhantomData,
        }
    }

     #[allow(dead_code)]
    pub fn mul_by_constant(&self, coeff: E::Fr) -> Self {
        Self{
            c0: self.c0.mul_by_constant(coeff),
            c1: self.c1.mul_by_constant(coeff),
            _phantom:   PhantomData,
        }
    }

    #[allow(dead_code)]
    pub fn add(
        &self,
        other: &Self,
    ) -> Self {

        Self{
            c0: self.c0.add(&other.c0),
            c1: self.c1.add(&other.c1),
            _phantom:   PhantomData,
        }
    }

    #[allow(dead_code)]
    pub fn sub(
        &self,
        other: &Self,
    ) -> Self {

        Self{
            c0: self.c0.sub(&other.c0),
            c1: self.c1.sub(&other.c1),
            _phantom:   PhantomData,
        }
    }

// }

// impl<E: Engine, P: Fp2Parameters<E>> Fp2Field<E, P> for Fq2<E>{

//     type P = P;

    #[allow(dead_code)]
    fn mul<CS>(
        &self,
        cs: &mut CS,
        other: &Self,
    ) -> Self 
        where CS: ConstraintSystem<E>
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
            c1: c1,
            _phantom:   PhantomData,
        }
    }

    #[allow(dead_code)]
    fn square<CS>(
        &self,
        cs: &mut CS,
    ) -> Self 
        where CS: ConstraintSystem<E>
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
            c1: c1,
            _phantom:   PhantomData,
        }
    }

    #[allow(dead_code)]
    fn inverse<CS>(
        &self,
        cs: &mut CS,
    ) -> Option<Self> 
        where CS: ConstraintSystem<E>
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
    fn enforce_mul<CS>(
        &self,
        cs: &mut CS,
        other: &Self,
        result: &Self
    )
        where CS: ConstraintSystem<E>
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
    fn frobenius_map(&self, power: usize) -> Self {

        let mut result = Self::new(
            Fq::<E>::new(self.c0.value, &self.c0.lc), 
            Fq::<E>::new(self.c1.value, &self.c1.lc), 
        );
        result.c1 = result.c1.mul_by_constant(P::FROBENIUS_COEFF_E[power % 2]);
        result
    }

}


#[cfg(test)]
mod tests {

    extern crate rand;
    extern crate bellman_ce;
 
    use std::marker::PhantomData;
    use rand::{Rand, thread_rng};
    use super::{Fq2};
    use crate::fields::{Fp2, Fp2Parameters};

    use bellman_ce::pairing::{Engine};
    use bellman_ce::pairing::ff::{Field};
    use bellman_ce::pairing::bls12_381::{Bls12, Fr};

    use bellman_ce::{
        ConstraintSystem,
        Circuit,
        SynthesisError
    };

    // We're going to use the Groth16 proving system.
    use bellman_ce::groth16::{ 
        // generate_random_parameters, 
        // prepare_verifying_key, 
        // create_random_proof, 
        // verify_proof
    };

    // This is a trivial circuit that verifies that a² * b / b == a²
    pub struct TestCircuit<E: Engine, P: Fp2Parameters<E>> {
        a_value: Fp2<E>,
        b_value: Fp2<E>,
        _phantom: PhantomData<P>,
    }

    impl<E: Engine, P: Fp2Parameters<E>> Circuit<E> for TestCircuit<E, P> {
        
        fn synthesize<CS: ConstraintSystem<E>>(
            self,
            cs: &mut CS
        ) -> Result<(), SynthesisError>
        {
            // Creates the gadgets and allocate the inputs
            let a = Fq2::<E, P>::from_fp2_alloc_input(&mut cs.namespace(|| "A"), &self.a_value);
            let b = Fq2::<E, P>::from_fp2_alloc_input(&mut cs.namespace(|| "B"), &self.b_value);

            // Allocate the constraints
            let a2          = a.square(&mut cs.namespace(|| "A²"));
            let a2_b        = a2.mul(&mut cs.namespace(|| "A² * B"), &b);
            let b_inv       = b.inverse(&mut cs.namespace(|| "1/B"));

            // Catch division error
            if b_inv.is_none() {
                return Err(SynthesisError::DivisionByZero);
            }
            let b_inv       = b_inv.expect("We already handled errors");
            let lhs         = b_inv.mul(&mut cs.namespace(|| "A² * B / B"), &a2_b);

            // Doubly enforce the egality in order to increase coverage
            a.enforce_mul(&mut cs.namespace(|| "lhs = a²"), &a, &lhs);

            Ok(())
        }
    }

    #[test]
    fn test() {
        // let rng = &mut thread_rng();

        // let params = {
        //     let c = TestCircuit::<Bls12> {
        //         a_value: Fp2::<Bls12>::one(),
        //         b_value: Fp2::<Bls12>::one(), // b cannot be zero
        //     };

        //     generate_random_parameters(c, rng).unwrap()
        // };

        // // Prepare the verification key (for proof verification)
        // let pvk = prepare_verifying_key(&params.vk);

        // let a = Fr::rand(rng);
        // let b = Fr::rand(rng);

        // let circuit = TestCircuit::<Bls12> {
        //     a_value: a,
        //     b_value: b,
        // };

        // let proof = create_random_proof(circuit, &params, rng).expect("Expect the prover to work");
        // assert!(verify_proof(&pvk, &proof, &[a, b]).expect("Expect well formed verification key"));
    }
}
