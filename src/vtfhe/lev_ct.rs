use std::array::from_fn;

use plonky2::{
    field::extension::Extendable,
    hash::hash_types::RichField,
    iop::{
        target::Target,
        witness::{PartialWitness, WitnessWrite},
    },
    plonk::circuit_builder::CircuitBuilder,
    util::ceil_div_usize,
};

use crate::vec_arithmetic::{scalar_mul, vec_add_many};

use super::glwe_poly::decompose;

#[derive(Debug)]
pub struct LevCt<const n: usize, const ELL: usize> {
    pub lwe_cts: [[Target; n]; ELL],
}

impl<const n: usize, const ELL: usize> LevCt<n, ELL> {
    pub fn new_from_builder<F: RichField + Extendable<D>, const D: usize>(
        cb: &mut CircuitBuilder<F, D>,
    ) -> Self {
        LevCt {
            lwe_cts: from_fn(|_| from_fn(|_| cb.add_virtual_target())),
        }
    }

    pub fn flatten(&self) -> Vec<Target> {
        self.lwe_cts
            .iter()
            .flat_map(|&lwe_ct| lwe_ct.into_iter())
            .collect()
    }

    pub fn register<F: RichField + Extendable<D>, const D: usize>(
        &self,
        cb: &mut CircuitBuilder<F, D>,
    ) {
        for lwe_ct in &self.lwe_cts {
            cb.register_public_inputs(lwe_ct)
        }
    }

    pub fn set_to_random<F: RichField + Extendable<D>, const D: usize>(
        &self,
        pw: &mut PartialWitness<F>,
    ) {
        for lwe in &self.lwe_cts {
            for &element in lwe {
                pw.set_target(element, F::rand());
            }
        }
    }

    pub fn num_targets() -> usize {
        n * ELL
    }

    pub fn mul<F: RichField + Extendable<D>, const D: usize, const LOGB: usize>(
        &self,
        cb: &mut CircuitBuilder<F, D>,
        mask: Target,
    ) -> Vec<Target> {
        let num_limbs = ceil_div_usize(F::BITS, LOGB);
        let limbs = decompose::<F, D, LOGB>(cb, mask, num_limbs);
        let summands = limbs
            .into_iter()
            .zip(self.lwe_cts.iter())
            .map(|(limb, lwe)| scalar_mul(cb, limb, lwe))
            .collect();
        vec_add_many(cb, &summands)
    }
}
