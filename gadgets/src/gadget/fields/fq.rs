use bellman_ce::pairing::{
    Engine
};

use bellman_ce::{
    // SynthesisError, 
    // Variable
    ConstraintSystem, 
    LinearCombination, 
};

use bellman_ce::pairing::ff::{
    Field
};

pub struct Fq<E: Engine> {
    pub value:     E::Fr,
    pub lc:  LinearCombination<E>
}

impl<E: Engine> Fq<E> {

    pub fn new(
        value:     E::Fr,
        lc:  &LinearCombination<E>,
    ) -> Self {

        Self{
            value: value,
            lc: LinearCombination::<E>::zero() + lc,
        }
    }

    pub fn alloc<CS>(
        cs:     &mut CS,
        value:     E::Fr,
    ) -> Self 
        where CS: ConstraintSystem<E>
    {

        let var = cs.alloc(
            || "Fields allocation", 
            || Ok(value)
        ).expect("Could not allocate variable");

        Self{
            value: value,
            lc: LinearCombination::<E>::zero() + var,
        }
    }

    pub fn zero<CS>() -> Self
        where CS: ConstraintSystem<E>
    {
        Self {
            value: E::Fr::zero(),
            lc: LinearCombination::<E>::zero()
        }
    }

    pub fn one<CS>() -> Self
        where CS: ConstraintSystem<E>
    {
        Self {
            value: E::Fr::zero(),
            lc: LinearCombination::<E>::zero() + CS::one()
        }
    }

    #[allow(dead_code)]
    pub fn alloc_input<CS>(
        cs:     &mut CS,
        value:     E::Fr,
    ) -> Self
        where CS: ConstraintSystem<E>
    {
        let var = cs.alloc_input(
            || "Fields allocatio as primary input",
            || Ok(value),
        ).expect("Could not allocate variable");

        Self{
            value: value,
            lc: LinearCombination::<E>::zero() + var,
        }
    }

    pub fn add(
        &self,
        other:  &Self,
    ) -> Self {

        Self{
            value: {
                let mut e = self.value;
                e.add_assign(&other.value);
                e
            },
            lc: LinearCombination::<E>::zero() + &self.lc + &self.lc
        }
    }

    pub fn sub(
        &self,
        other: &Self,
    ) -> Self {

        Self{
            value: {
                let mut e = self.value;
                e.sub_assign(&other.value);
                e
            },
            lc: LinearCombination::<E>::zero() + &self.lc - &self.lc
        }
    }

    pub fn negate(
       &self, 
    ) -> Self {

        Self{
            value: {
                let mut e = E::Fr::zero();
                e.sub_assign(&self.value);
                e
            },
            lc: LinearCombination::<E>::zero() - &self.lc
        }
    }

    pub fn mul_by_constant(
        &self,
        coeff:  E::Fr,
    ) -> Self {
        
        Fq{
            value: {
                let mut output = self.value;
                output.mul_assign(&coeff);
                output
            },
            lc: LinearCombination::<E>::zero() + (coeff, &self.lc)
        }
    }

    pub fn double(
        &self,
    ) -> Self {
        let mut two = E::Fr::one();
        two.double();
        self.mul_by_constant(two)
    }

    pub fn mul<CS>(
        &self,
        cs:    &mut CS,
        other: &Self, 
    ) -> Self 
        where CS: ConstraintSystem<E>
    {
        let mut mul_cs = cs.namespace(|| "Field multiplication");

        let output_value = {
            let mut e = self.value;
            e.mul_assign(&other.value);
            e
        };

        let output_var = mul_cs.alloc(
            || "Result",
            || Ok(output_value),
        ).expect("Could not allocate variable");

        let output_lc = LinearCombination::<E>::zero() + output_var;

        let output = Self{
            value: output_value,
            lc: output_lc
        };

        mul_cs.enforce(
            || "a * b == c",
            |lc| lc + &self.lc, 
            |lc| lc + &other.lc, 
            |lc| lc + &output.lc,
        );

        output
    }

    #[allow(dead_code)]
    pub fn inverse<CS>(
        &self,
        cs:    &mut CS
    ) -> Option<Self> 
        where CS: ConstraintSystem<E>
    {
        let mut inv_cs = cs.namespace(|| "Field inversion");

        let inv_opt = self.value.inverse();
        if inv_opt.is_none() {
            return None;
        }
        let inv_value = inv_opt.expect("We just checked that it would not fail");

        let inverse_var = inv_cs.alloc(
            || "Result",
            || Ok(inv_value),
        ).expect("Could not allocate variable");

        let inverse_lc = LinearCombination::<E>::zero() + inverse_var;
        
        let inverse = Fq{
            value:     inv_value,
            lc:  inverse_lc,
        };

        inv_cs.enforce(
            || "A * 1/A == 1",
            |lc| lc + &self.lc,
            |lc| lc + &inverse.lc,
            |lc| lc + CS::one()
        );

        Some(inverse)
    }

    #[allow(dead_code)]
    pub fn square<CS>(
        &self,
        cs:    &mut CS,
    ) -> Self 
        where CS: ConstraintSystem<E>
    { 
        let mut sqr_cs = cs.namespace(|| "Field squaring");
        let mut sqr_value = self.value;
        sqr_value.square();

        let sqr_var = sqr_cs.alloc(
            || "Result",
            || Ok(sqr_value),
        ).expect("Could not allocate variable");

        let sqr_lc = LinearCombination::<E>::zero() + sqr_var;
        
        let square = Fq{
            value:     sqr_value,
            lc:  sqr_lc,
        };

        sqr_cs.enforce(
            || "A * 1/A == 1",
            |lc| lc + &self.lc,
            |lc| lc + &self.lc,
            |lc| lc + &square.lc,
        );

        square
    }

    #[allow(dead_code)]
    pub fn enforce_mul<CS>(
        &self,
        cs:     &mut CS,
        other:  &Self, 
        result: &Self,
    )
        where CS: ConstraintSystem<E>
    {
        cs.enforce(|| "Multiplication constraint", 
            |lc| lc + &self.lc, 
            |lc| lc + &other.lc, 
            |lc| lc + &result.lc
        );
    }

    #[allow(dead_code)]
    pub fn enforce_sqr<CS>(
        &self,
        cs:     &mut CS,
        result: &Self,
    )
        where CS: ConstraintSystem<E>
    {
        cs.enforce(|| "Multiplication constraint", 
            |lc| lc + &self.lc, 
            |lc| lc + &self.lc, 
            |lc| lc + &result.lc
        );
    }
}

#[cfg(test)]
mod tests {

    extern crate rand;
    extern crate bellman_ce;

    use rand::{Rand, thread_rng};
    use super::Fq;

    use bellman_ce::pairing::{ Engine };
    use bellman_ce::pairing::ff::{ Field };
    use bellman_ce::pairing::bls12_381::{ Bls12, Fr };

    use bellman_ce::{
        ConstraintSystem,
        Circuit,
        SynthesisError
    };

    // We're going to use the Groth16 proving system.
    use bellman_ce::groth16::{ 
        generate_random_parameters, 
        prepare_verifying_key, 
        create_random_proof, 
        verify_proof
    };

    // This is a trivial circuit that verifies that a² * b / b == a²
    pub struct TestCircuit<E: Engine> {
        a_value: E::Fr,
        b_value: E::Fr,
    }

    impl<E: Engine> Circuit<E> for TestCircuit<E> {
        
        fn synthesize<CS: ConstraintSystem<E>>(
            self,
            cs: &mut CS
        ) -> Result<(), SynthesisError>
        {
            // Creates the gadgets and allocate the inputs
            let a = Fq::<E>::alloc_input(&mut cs.namespace(|| "A"), self.a_value);
            let b = Fq::<E>::alloc_input(&mut cs.namespace(|| "B"), self.b_value);

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
            a.enforce_sqr(&mut cs.namespace(|| "lhs = a²"), &lhs);
            a.enforce_mul(&mut cs.namespace(|| "lhs = a²"), &a, &lhs);

            Ok(())
        }
    }

    #[test]
    fn test() {
        let rng = &mut thread_rng();

        let params = {
            let c = TestCircuit::<Bls12> {
                a_value: Fr::one(),
                b_value: Fr::one(), // b cannot be zero
            };

            generate_random_parameters(c, rng).unwrap()
        };

        // Prepare the verification key (for proof verification)
        let pvk = prepare_verifying_key(&params.vk);

        let a = Fr::rand(rng);
        let b = Fr::rand(rng);

        let circuit = TestCircuit::<Bls12> {
            a_value: a,
            b_value: b,
        };

        let proof = create_random_proof(circuit, &params, rng).expect("Expect the prover to work");
        assert!(verify_proof(&pvk, &proof, &[a, b]).expect("Expect well formed verification key"));
    }

}
