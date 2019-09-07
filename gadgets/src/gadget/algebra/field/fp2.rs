use bellman_ce::{
    pairing::{
        Engine,
        ff::{
            ScalarEngine,
            Field as AlgebraField,
        },
    },
    ConstraintSystem, 
    LinearCombination, 
};

use super::{
    field::{
        Field,
        FieldExtension,
    },
    fp::Fp,
    super::super::{
        Gadget,
    },
};

pub struct Fp2<E: Engine> {
    pub c0: Fp<E>,
    pub c1: Fp<E>
}

impl<E: Engine> Fp2<E> {

    fn new(c0: Fp<E>, c1: Fp<E>) -> Self {

        Self { 
            c0: c0,
            c1: c1
        }
    }
}

impl <E: Engine> Gadget<E,  AlgebraicFp2<E>> for Fp2<E> {

    fn value(&self) -> AlgebraicFp2<E> {
        AlgebraicFp2 { c0: self.c0.value(), c1: self.c1.value() }
    }

    fn alloc<CS>(
        cs:     &mut CS,
        value:  AlgebraicFp2<E>,
    ) -> Self 
        where CS: ConstraintSystem<E>
    {
        let inner_cs = &mut cs.namespace(|| "Fp2 allocation");

        Self {
            c0: Fp::alloc(inner_cs, value.c0),
            c1: Fp::alloc(inner_cs, value.c1),
        }
    }

    fn alloc_input<CS>(
        cs:     &mut CS,
        value:  AlgebraicFp2<E>,
    ) -> Self
        where CS: ConstraintSystem<E>
    {
        let inner_cs = &mut cs.namespace(|| "Fp2 allocation as input");

        Self {
            c0: Fp::alloc_input(inner_cs, value.c0),
            c1: Fp::alloc_input(inner_cs, value.c1),
        }
    }
}

impl<E: Engine> Field<E, AlgebraicFp2<E>> for Fp2<E> {

    fn zero<CS>(_: &mut CS) -> Self
        where CS: ConstraintSystem<E>
    {
        Self {
           c0: Fp::<E>::zero(),
           c1: Fp::<E>::zero(),
        }
    }

    fn one<CS>(cs: &mut CS) -> Self
        where CS: ConstraintSystem<E>
    {
        Self {
           c0: Fp::<E>::one(cs),
           c1: Fp::<E>::zero(cs),
        }
    }

    fn add(&self, other:  &Self) -> Self
    {

        Self {
            c0: self.c0.add(&other.c0),
            c1: self.c1.add(&other.c1),
        }
    }

    fn sub(&self, other: &Self) -> Self 
    {

        Self {
            c0: self.c0.sub(&other.c0),
            c1: self.c1.sub(&other.c1),
        }
    }

    fn negate(&self) -> Self 
    {
        Self {
            c0: self.negate(),
            c1: self.negate(),
        }
    }

    fn mul_by_constant(&self, other: &AlgebraicFp2<E>) -> Self
    {   
        let ac = self.c0.mul_by_constant(&other.c0);
        let ad = self.c0.mul_by_constant(&other.c1);
        let bc = self.c1.mul_by_constant(&other.c0);
        let nr_bd = self.c1.mul_by_constant(&other.c1).mul_non_residue();

        Self {
            c0: self.c0.mul_by_constant()
        }
    }

//     fn mul<CS>(
//         &self,
//         other: &Self, 
//         cs:    &mut CS,
//     ) -> Self 
//         where CS: ConstraintSystem<E>
//     {
//         let mut mul_cs = cs.namespace(|| "Field multiplication");

//         let output_value = {
//             let mut e = self.value;
//             e.mul_assign(&other.value);
//             e
//         };

//         let output_var = mul_cs.alloc(
//             || "Result",
//             || Ok(output_value),
//         ).expect("Could not allocate variable");

//         let output_lc = LinearCombination::<E>::zero() + output_var;

//         let output = Self{
//             value: output_value,
//             lc: output_lc
//         };

//         mul_cs.enforce(
//             || "a * b == c",
//             |lc| lc + &self.lc, 
//             |lc| lc + &other.lc, 
//             |lc| lc + &output.lc,
//         );

//         output
//     }

    
//     fn inverse<CS>(
//         &self,
//         cs:    &mut CS
//     ) -> Option<Self> 
//         where CS: ConstraintSystem<E>
//     {
//         let mut inv_cs = cs.namespace(|| "Field inversion");

//         let inv_opt = self.value.inverse();
//         if inv_opt.is_none() {
//             return None;
//         }
//         let inv_value = inv_opt.expect("We just checked that it would not fail");

//         let inverse_var = inv_cs.alloc(
//             || "Result",
//             || Ok(inv_value),
//         ).expect("Could not allocate variable");

//         let inverse_lc = LinearCombination::<E>::zero() + inverse_var;
        
//         let inverse = Self {
//             value:     inv_value,
//             lc:  inverse_lc,
//         };

//         inv_cs.enforce(
//             || "A * 1/A == 1",
//             |lc| lc + &self.lc,
//             |lc| lc + &inverse.lc,
//             |lc| lc + CS::one()
//         );

//         Some(inverse)
//     }

    
//     fn square<CS>(
//         &self,
//         cs:    &mut CS,
//     ) -> Self 
//         where CS: ConstraintSystem<E>
//     { 
//         let mut sqr_cs = cs.namespace(|| "Field squaring");
//         let mut sqr_value = self.value;
//         sqr_value.square();

//         let sqr_var = sqr_cs.alloc(
//             || "Result",
//             || Ok(sqr_value),
//         ).expect("Could not allocate variable");

//         let sqr_lc = LinearCombination::<E>::zero() + sqr_var;
        
//         let square = Self {
//             value:     sqr_value,
//             lc:  sqr_lc,
//         };

//         sqr_cs.enforce(
//             || "A * 1/A == 1",
//             |lc| lc + &self.lc,
//             |lc| lc + &self.lc,
//             |lc| lc + &square.lc,
//         );

//         square
//     }

    
//     fn enforce_mul<CS>(
//         &self,
//         other:  &Self, 
//         result: &Self,
//         cs:     &mut CS,
//     ) -> Option<()>
//         where CS: ConstraintSystem<E>
//     {
//         // TODO: explicitly check the constraints at building time
//         cs.enforce(|| "Multiplication constraint", 
//             |lc| lc + &self.lc, 
//             |lc| lc + &other.lc, 
//             |lc| lc + &result.lc
//         );

//         Some(())
//     }

    
//     fn enforce_square<CS>(
//         &self,
//         result: &Self,
//         cs:     &mut CS,
//     ) -> Option<()>
//         where CS: ConstraintSystem<E>
//     {
//         // TODO: explicitly check the constraints at building time
//         cs.enforce(|| "Squaring constraint", 
//             |lc| lc + &self.lc, 
//             |lc| lc + &self.lc, 
//             |lc| lc + &result.lc
//         );

//         Some(())
//     }
}

// #[cfg(test)]
// mod tests {

//     extern crate rand;
//     extern crate bellman_ce;

//     use rand::{Rand, thread_rng};
//     use super::Fq;

//     use bellman_ce::pairing::{ Engine };
//     use bellman_ce::pairing::ff::{ Field };

//     use bellman_ce::{
//         ConstraintSystem,
//         Circuit,
//         SynthesisError
//     };

//     // We're going to use the Groth16 proving system.
//     #[cfg(test)]
//     use bellman_ce::groth16::{ 
//         generate_random_parameters, 
//         prepare_verifying_key, 
//         create_random_proof,
//         verify_proof
//     };

//     // This is a trivial circuit that verifies that a² * b / b == a²
//     pub struct TestCircuit<E: Engine> {
//         a_value: E::Fr,
//         b_value: E::Fr,
//     }

//     impl<E: Engine> Circuit<E> for TestCircuit<E> {
        
//         fn synthesize<CS: ConstraintSystem<E>>(
//             self,
//             cs: &mut CS
//         ) -> Result<(), SynthesisError>
//         {
//             // Creates the gadgets and allocate the inputs
//             let a = Fq::<E>::alloc_input(&mut cs.namespace(|| "A"), self.a_value);
//             let b = Fq::<E>::alloc_input(&mut cs.namespace(|| "B"), self.b_value);

//             // Allocate the constraints
//             let a2          = a.square(&mut cs.namespace(|| "A²"));
//             let a2_b        = a2.mul(&mut cs.namespace(|| "A² * B"), &b);
//             let b_inv       = b.inverse(&mut cs.namespace(|| "1/B"));

//             // Catch division error
//             if b_inv.is_none() {
//                 return Err(SynthesisError::DivisionByZero);
//             }
//             let b_inv       = b_inv.expect("We already handled errors");
//             let lhs         = b_inv.mul(&mut cs.namespace(|| "A² * B / B"), &a2_b);

//             // Doubly enforce the egality in order to increase coverage
//             a.enforce_sqr(&mut cs.namespace(|| "lhs = a²"), &lhs);
//             a.enforce_mul(&mut cs.namespace(|| "lhs = a²"), &a, &lhs);

//             Ok(())
//         }
//     }

//     #[test]
//     fn test_mnt4() {
//         use bellman_ce::pairing::mnt4_753::{ Fr };
//         use bellman_ce::pairing::mnt4_753::Mnt4 as engine;
//         // use bellman_ce::pairing::bls12_381::{ Fr };
//         // use bellman_ce::pairing::bls12_381::Bls12 as engine;

//         let rng = &mut thread_rng();

//         println!("Generating parameters");

//         let params = {
//             let c = TestCircuit::<engine> {
//                 a_value: Fr::one(),
//                 b_value: Fr::one(), // b cannot be zero
//             };

//             generate_random_parameters(c, rng).unwrap()
//         };

//         println!("Generated parameters");

//         // Prepare the verification key (for proof verification)
//         let pvk = prepare_verifying_key(&params.vk);

//         println!("Prepared the vk");

//         let a = Fr::rand(rng);
//         let b = Fr::rand(rng);

//         let circuit = TestCircuit::<engine> {
//             a_value: a,
//             b_value: b,
//         };

//         println!("Creating the proof");

//         let proof = create_random_proof(circuit, &params, rng).expect("Expect the prover to work");
//         assert!(verify_proof(&pvk, &proof, &[a, b]).expect("Expect well formed verification key"));
//     }

//     #[test]
//     fn test_mnt6() {
//         use bellman_ce::pairing::mnt6_753::{ Mnt6, Fr };
//         let rng = &mut thread_rng();

//         let params = {
//             let c = TestCircuit::<Mnt6> {
//                 a_value: Fr::one(),
//                 b_value: Fr::one(), // b cannot be zero
//             };

//             generate_random_parameters(c, rng).unwrap()
//         };

//         // Prepare the verification key (for proof verification)
//         let pvk = prepare_verifying_key(&params.vk);

//         let a = Fr::rand(rng);
//         let b = Fr::rand(rng);

//         let circuit = TestCircuit::<Mnt6> {
//             a_value: a,
//             b_value: b,
//         };

//         let proof = create_random_proof(circuit, &params, rng).expect("Expect the prover to work");
//         assert!(verify_proof(&pvk, &proof, &[a, b]).expect("Expect well formed verification key"));
//     }

// }
