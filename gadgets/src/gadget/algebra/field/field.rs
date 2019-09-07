use bellman_ce::{
    pairing::{
        Engine, 
        ff::{
            ScalarEngine,
            Field as AlgebraField,
        },
    },
    ConstraintSystem,
};

use super::super::super::{ Gadget };

pub trait Field<E: Engine, F: AlgebraField = <E as ScalarEngine>::Fr >: Sized + Gadget<E, F> {

    // Ideally, this should be a singleton per circuit
    fn zero<CS>(cs: &mut CS) -> Self where CS: ConstraintSystem<E>;
    fn one<CS>(cs: &mut CS) -> Self where CS: ConstraintSystem<E>;

    fn negate(&self) -> Self;
    fn add(&self, other: &Self) -> Self;
    fn mul_by_constant(&self, c: &F) -> Self;
    
    fn mul<CS>(&self, other: &Self, cs: &mut CS) -> Self
        where CS: ConstraintSystem<E>;
    fn inverse<CS>(&self, cs: &mut CS) -> Option<Self>
        where CS: ConstraintSystem<E>;
    fn enforce_mul<CS>(&self, other: &Self, result: &Self, cs: &mut CS) -> Option<()>
        where CS: ConstraintSystem<E>;

    fn double(&self) -> Self {
        self.add(self)
    }

    fn sub(&self, other: &Self) -> Self {
        self.add(&other.negate())
    }

    fn square<CS>(&self, cs: &mut CS) -> Self
        where CS: ConstraintSystem<E>
    {
        self.mul(&self, cs)
    }

    fn enforce_square<CS>(&self, result: &Self, cs: &mut CS) -> Option<()>
        where CS: ConstraintSystem<E>
    {
        self.enforce_mul(self, result, cs)
    }
}

pub trait FieldExtension<E: Engine, F: AlgebraField>: Field<E, F> {

    const FROBENIUS_COEFFS: [E::Fr];
    const NON_RESIDUE: E::Fr;

    fn frobenius_map(&self, power: usize) -> Self;
    
    fn mul_by_non_residue(&self) -> Self;

    fn mul_by_fp<CS>(&self, fp: &E::Fr, cs: &mut CS) -> Self
        where CS: ConstraintSystem<E>;

}