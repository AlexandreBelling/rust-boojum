mod algebra;

use bellman_ce::{
    pairing::{ Engine },
    ConstraintSystem,
};

pub trait Gadget<E: Engine, T>: Sized {

    fn value(&self) -> T;

    fn alloc<CS>(cs: &mut CS, value: T) -> Self
        where CS: ConstraintSystem<E>;
        
    fn alloc_input<CS>(cs: &mut CS, value: T) -> Self
        where CS: ConstraintSystem<E>;
}
