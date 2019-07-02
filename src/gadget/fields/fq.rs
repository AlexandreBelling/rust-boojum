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
    pub value:     E::Fr,
    pub lc:  LinearCombination<E>
}

impl<E: Engine> Fq<E> {

    #[allow(dead_code)]
    pub fn new(
        value:     E::Fr,
        lc:  &LinearCombination<E>,
    ) -> Self {

        Self{
            value: value,
            lc: LinearCombination::<E>::zero() + lc,
        }
    }

    #[allow(dead_code)]
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

    #[allow(dead_code)]
    pub fn zero<CS>() -> Self
        where CS: ConstraintSystem<E>
    {
        Self {
            value: E::Fr::zero(),
            lc: LinearCombination::<E>::zero()
        }
    }

    #[allow(dead_code)]
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
            || "Fields allocation",
            || Ok(value),
        ).expect("Could not allocate variable");

        Self{
            value: value,
            lc: LinearCombination::<E>::zero() + var,
        }
    }

    #[allow(dead_code)]
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

    #[allow(dead_code)]
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

    #[allow(dead_code)]
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

    #[allow(dead_code)]
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
            let mut e = self.value;
            e.mul_assign(&other.value);
            e
        };

        let output_var = mul_cs.alloc_input(
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

        let inverse_var = inv_cs.alloc_input(
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
    pub fn sqr<CS>(
        &self,
        cs:    &mut CS,
    ) -> Self 
        where CS: ConstraintSystem<E>
    { 
        let mut sqr_cs = cs.namespace(|| "Field squaring");
        let mut sqr_value = self.value;
        sqr_value.square();

        let sqr_var = sqr_cs.alloc_input(
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
