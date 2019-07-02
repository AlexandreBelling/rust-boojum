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

#[allow(dead_code)]
pub struct Fq<E: Engine> {
    pub c0:     E::Fr,
    pub c0_lc:  LinearCombination<E>
}

impl<E: Engine> Fq<E> {

    #[allow(dead_code)]
    pub fn new(
        c0:     E::Fr,
        c0_lc:  &LinearCombination<E>,
    ) -> Self {

        Self{
            c0: c0,
            c0_lc: LinearCombination::<E>::zero() + c0_lc,
        }
    }

    #[allow(dead_code)]
    pub fn alloc<CS>(
        cs:     &mut CS,
        c0:     E::Fr,
    ) -> Self 
        where CS: ConstraintSystem<E>
    {

        let var = cs.alloc(
            || "Fields allocation", 
            || Ok(c0)
        ).expect("Could not allocate variable");

        Self{
            c0: c0,
            c0_lc: LinearCombination::<E>::zero() + var,
        }
    }

    #[allow(dead_code)]
    pub fn zero<CS>() -> Self
        where CS: ConstraintSystem<E>
    {
        Self {
            c0: E::Fr::zero(),
            c0_lc: LinearCombination::<E>::zero()
        }
    }

    #[allow(dead_code)]
    pub fn one<CS>() -> Self
        where CS: ConstraintSystem<E>
    {
        Self {
            c0: E::Fr::zero(),
            c0_lc: LinearCombination::<E>::zero() + CS::one()
        }
    }

    #[allow(dead_code)]
    pub fn alloc_input<CS>(
        cs:     &mut CS,
        c0:     E::Fr,
    ) -> Self
        where CS: ConstraintSystem<E>
    {
        let var = cs.alloc_input(
            || "Fields allocation",
            || Ok(c0),
        ).expect("Could not allocate variable");

        Self{
            c0: c0,
            c0_lc: LinearCombination::<E>::zero() + var,
        }
    }

    #[allow(dead_code)]
    pub fn add(
        &self,
        other:  &Self,
    ) -> Self {

        Self{
            c0: {
                let mut e = self.c0;
                e.add_assign(&other.c0);
                e
            },
            c0_lc: LinearCombination::<E>::zero() + &self.c0_lc + &self.c0_lc
        }
    }

    #[allow(dead_code)]
    pub fn sub(
        &self,
        other: &Self,
    ) -> Self {

        Self{
            c0: {
                let mut e = self.c0;
                e.sub_assign(&other.c0);
                e
            },
            c0_lc: LinearCombination::<E>::zero() + &self.c0_lc - &self.c0_lc
        }
    }

    #[allow(dead_code)]
    pub fn negate(
       &self, 
    ) -> Self {

        Self{
            c0: {
                let mut e = E::Fr::zero();
                e.sub_assign(&self.c0);
                e
            },
            c0_lc: LinearCombination::<E>::zero() - &self.c0_lc
        }
    }

    #[allow(dead_code)]
    pub fn mul_by_constant(
        &self,
        coeff:  E::Fr,
    ) -> Self {
        
        Fq{
            c0: {
                let mut output = self.c0;
                output.mul_assign(&coeff);
                output
            },
            c0_lc: LinearCombination::<E>::zero() + (coeff, &self.c0_lc)
        }
    }

    #[allow(dead_code)]
    pub fn double(
        &self,
    ) -> Self {
        let mut two = E::Fr::one();
        two.double();
        self.mul_by_constant(two)
    }

    #[allow(dead_code)]
    pub fn mul<CS>(
        &self,
        cs:    &mut CS,
        other: &Self, 
    ) -> Self 
        where CS: ConstraintSystem<E>
    {
        let mut mul_cs = cs.namespace(|| "Field multiplication");

        let output_value = {
            let mut e = self.c0;
            e.mul_assign(&other.c0);
            e
        };

        let output_var = mul_cs.alloc_input(
            || "Result",
            || Ok(output_value),
        ).expect("Could not allocate variable");

        let output_lc = LinearCombination::<E>::zero() + output_var;

        let output = Self{
            c0: output_value,
            c0_lc: output_lc
        };

        mul_cs.enforce(
            || "a * b == c",
            |lc| lc + &self.c0_lc, 
            |lc| lc + &other.c0_lc, 
            |lc| lc + &output.c0_lc,
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

        let inv_opt = self.c0.inverse();
        if inv_opt.is_none() {
            return None;
        }
        let inv_value = inv_opt.expect("We just checked that it would not fail");

        let inverse_var = inv_cs.alloc_input(
            || "Result",
            || Ok(inv_value),
        ).expect("Could not allocate variable");

        let inverse_lc = LinearCombination::<E>::zero() + inverse_var;
        
        let inverse = Fq{
            c0:     inv_value,
            c0_lc:  inverse_lc,
        };

        inv_cs.enforce(
            || "A * 1/A == 1",
            |lc| lc + &self.c0_lc,
            |lc| lc + &inverse.c0_lc,
            |lc| lc + CS::one()
        );

        Some(inverse)
    }

    #[allow(dead_code)]
    pub fn sqr<CS>(
        &self,
        cs:    &mut CS,
    ) -> Self 
        where CS: ConstraintSystem<E>
    { 
        let mut sqr_cs = cs.namespace(|| "Field squaring");
        let mut sqr_value = self.c0;
        sqr_value.square();

        let sqr_var = sqr_cs.alloc_input(
            || "Result",
            || Ok(sqr_value),
        ).expect("Could not allocate variable");

        let sqr_lc = LinearCombination::<E>::zero() + sqr_var;
        
        let square = Fq{
            c0:     sqr_value,
            c0_lc:  sqr_lc,
        };

        sqr_cs.enforce(
            || "A * 1/A == 1",
            |lc| lc + &self.c0_lc,
            |lc| lc + &self.c0_lc,
            |lc| lc + &square.c0_lc,
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
            |lc| lc + &self.c0_lc, 
            |lc| lc + &other.c0_lc, 
            |lc| lc + &result.c0_lc
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
            |lc| lc + &self.c0_lc, 
            |lc| lc + &self.c0_lc, 
            |lc| lc + &result.c0_lc
        );
    }

}
