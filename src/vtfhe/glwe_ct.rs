use std::array::from_fn;

use plonky2::{
    field::extension::Extendable,
    hash::hash_types::RichField,
    iop::{target::Target, witness::PartialWitness},
    plonk::circuit_builder::CircuitBuilder,
};

use super::{glwe_poly::GlwePoly, crypto::glwe::Glwe};

#[derive(Debug)]
pub struct GlweCt<const N: usize, const K: usize> {
    pub polys: [GlwePoly<N>; K],
}

impl<const N: usize, const K: usize> GlweCt<N, K> {
    pub fn new_from_builder<F: RichField + Extendable<D>, const D: usize>(
        cb: &mut CircuitBuilder<F, D>,
    ) -> Self {
        let range: [usize; K] = core::array::from_fn(|i| i);
        GlweCt {
            polys: range.map(|_| GlwePoly::new_from_builder(cb)),
        }
    }

    pub fn flatten(&self) -> Vec<Target> {
        self.polys.iter().flat_map(|poly| poly.flatten()).collect()
    }

    pub fn new_from_targets(targets: &[Target]) -> Self {
        let poly_targets = GlwePoly::<N>::num_targets();
        assert_eq!(
            targets.len(),
            K * poly_targets,
            "Incorrect number of targets to construct GlweCt."
        );
        GlweCt {
            polys: targets
                .chunks(poly_targets)
                .map(|t| GlwePoly::<N>::new_from_targets(t))
                .collect::<Vec<_>>()
                .try_into()
                .unwrap(),
        }
    }

    pub fn register<F: RichField + Extendable<D>, const D: usize>(
        &self,
        cb: &mut CircuitBuilder<F, D>,
    ) {
        for poly in &self.polys {
            poly.register(cb);
        }
    }

    pub fn set_to_random<F: RichField + Extendable<D>, const D: usize>(
        &self,
        pw: &mut PartialWitness<F>,
    ) {
        for poly in &self.polys {
            poly.set_to_random(pw);
        }
    }

    pub fn assign<F: RichField + Extendable<D>, const D: usize>(
        &self,
        pw: &mut PartialWitness<F>,
        ct: &Glwe<F, D, N, K>,
    ) {
        for (x, y) in self.polys.iter().zip(ct.polys.iter()) {
            x.assign(pw, y);
        }
    }

    pub fn add<F: RichField + Extendable<D>, const D: usize>(
        &self,
        cb: &mut CircuitBuilder<F, D>,
        other: &GlweCt<N, K>,
    ) -> GlweCt<N, K> {
        let range: [usize; K] = from_fn(|i| i);
        GlweCt {
            polys: range.map(|i| self.polys[i].add(cb, &other.polys[i])),
        }
    }

    pub fn sub<F: RichField + Extendable<D>, const D: usize>(
        &self,
        cb: &mut CircuitBuilder<F, D>,
        other: &GlweCt<N, K>,
    ) -> GlweCt<N, K> {
        let range: [usize; K] = from_fn(|i| i);
        GlweCt {
            polys: range.map(|i| self.polys[i].sub(cb, &other.polys[i])),
        }
    }

    pub fn ntt_backward<F: RichField + Extendable<D>, const D: usize>(
        &self,
        cb: &mut CircuitBuilder<F, D>,
    ) -> GlweCt<N, K> {
        GlweCt {
            polys: self
                .polys
                .iter()
                .map(|poly| poly.ntt_backward(cb))
                .collect::<Vec<_>>()
                .try_into()
                .unwrap(),
        }
    }

    pub fn num_targets() -> usize {
        K * N
    }
}
