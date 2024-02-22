use plonky2::{
    field::extension::Extendable,
    hash::hash_types::RichField,
    iop::{target::Target, witness::PartialWitness},
    plonk::circuit_builder::CircuitBuilder,
    util::ceil_div_usize,
};

use crate::{ntt::ntt_forward, vec_arithmetic::vec_inner};

use super::{crypto::glev::Glev, glwe_ct::GlweCt, glwe_poly::GlwePoly};

#[derive(Debug)]
pub struct GlevCt<const N: usize, const K: usize, const ELL: usize> {
    pub glwe_cts: [GlweCt<N, K>; ELL],
}

impl<const N: usize, const K: usize, const ELL: usize> GlevCt<N, K, ELL> {
    pub fn new_from_builder<F: RichField + Extendable<D>, const D: usize>(
        cb: &mut CircuitBuilder<F, D>,
    ) -> Self {
        let range: [usize; ELL] = core::array::from_fn(|i| i);
        GlevCt {
            glwe_cts: range.map(|_| GlweCt::new_from_builder(cb)),
        }
    }

    pub fn new_from_targets(targets: &[Target]) -> Self {
        let glwe_targets = GlweCt::<N, K>::num_targets();
        assert_eq!(
            targets.len(),
            ELL * glwe_targets,
            "Incorrect number of targets to construct GlevCt."
        );
        GlevCt {
            glwe_cts: targets
                .chunks(glwe_targets)
                .map(|t| GlweCt::<N, K>::new_from_targets(t))
                .collect::<Vec<_>>()
                .try_into()
                .unwrap(),
        }
    }

    pub fn flatten(&self) -> Vec<Target> {
        self.glwe_cts
            .iter()
            .flat_map(|glwe| glwe.flatten())
            .collect()
    }

    pub fn register<F: RichField + Extendable<D>, const D: usize>(
        &self,
        cb: &mut CircuitBuilder<F, D>,
    ) {
        for glwe_ct in &self.glwe_cts {
            glwe_ct.register(cb);
        }
    }

    pub fn set_to_random<F: RichField + Extendable<D>, const D: usize>(
        &self,
        pw: &mut PartialWitness<F>,
    ) {
        for glwe_ct in &self.glwe_cts {
            glwe_ct.set_to_random(pw);
        }
    }

    pub fn assign<F: RichField + Extendable<D>, const D: usize>(
        &self,
        pw: &mut PartialWitness<F>,
        ct: &Glev<F, D, N, K, ELL>,
    ) {
        for (x, y) in self.glwe_cts.iter().zip(ct.glwes.iter()) {
            x.assign(pw, y);
        }
    }

    pub fn get_row(&self, index: usize) -> Vec<Vec<Target>> {
        self.glwe_cts
            .iter()
            .map(|ct| ct.polys[index].coeffs.to_vec())
            .into_iter()
            .collect()
    }

    pub fn num_targets() -> usize {
        K * N * ELL
    }

    pub fn mul<F: RichField + Extendable<D>, const D: usize, const LOGB: usize>(
        &self,
        cb: &mut CircuitBuilder<F, D>,
        glwe_poly: &GlwePoly<N>,
    ) -> GlweCt<N, K> {
        // let num_limbs = ceil_div_usize(log2_ceil(F::ORDER as usize), LOGB);
        let num_limbs = ceil_div_usize(F::BITS, LOGB);
        // let limbs = vec_decompose::<F, D, LOGB>(cb, &glwe_poly.coeffs, num_limbs);
        let limbs = glwe_poly.decompose::<F, D, LOGB>(cb, num_limbs);
        let limbs_hat = &limbs[num_limbs - ELL..]
            .iter()
            .map(|limb| ntt_forward(cb, &limb))
            .collect();
        let range: [usize; K] = core::array::from_fn(|i| i);
        let polys = range.map(|index| GlwePoly {
            coeffs: vec_inner(cb, limbs_hat, &self.get_row(index))
                .try_into()
                .unwrap(),
        });
        GlweCt { polys: polys }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ntt::params::N;
    use crate::vtfhe::crypto::glwe::Glwe;
    use crate::vtfhe::crypto::lwe::decrypt;
    use crate::vtfhe::crypto::poly::Poly;

    use plonky2::field::types::{Field, PrimeField64, Sample};
    use plonky2::iop::witness::PartialWitness;
    use plonky2::plonk::circuit_data::CircuitConfig;
    use plonky2::plonk::config::{GenericConfig, PoseidonGoldilocksConfig};
    // use crate::vec_arithmetic::build_decomposition_lut;

    #[test]
    fn test_glev_mul() {
        const LOGB: usize = 8;
        const ELL: usize = 8;
        const K: usize = 2;
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;

        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        // build_decomposition_lut::<F, D, LOGB>(&mut builder);
        let mut pw = PartialWitness::new();

        let glwe_poly: GlwePoly<N> = GlwePoly::new_from_builder::<F, D>(&mut builder);
        let glev_ct: GlevCt<N, K, ELL> = GlevCt::new_from_builder::<F, D>(&mut builder);

        glwe_poly.register(&mut builder);
        glev_ct.register(&mut builder);

        // glwe_poly.set_to_random::<F, D>(&mut pw);
        // glev_ct.set_to_random::<F, D>(&mut pw);
        let s = Glwe::<F, D, N, K>::key_gen();
        let m = F::rand();
        let a = Poly::<F, D, N>::rand();

        let ct = Glev::<F, D, N, K, ELL>::encrypt::<LOGB>(&s, &Poly::constant(&m), 0f64);
        glev_ct.assign(&mut pw, &ct.ntt_forward());
        glwe_poly.assign(&mut pw, &a);

        let z = glev_ct.mul::<F, D, LOGB>(&mut builder, &glwe_poly);
        z.register(&mut builder);

        let data = builder.build::<C>();
        let proof = data.prove(pw).unwrap();

        let _ = data.verify(proof.clone()).unwrap();

        let start = GlwePoly::<N>::num_targets() + GlevCt::<N, K, ELL>::num_targets();
        let out_glwe_flat = &proof.public_inputs[start..start + GlweCt::<N, K>::num_targets()];
        let out_glwe = Glwe::<F, D, N, K>::from_slice(out_glwe_flat);
        let out_ct = out_glwe.ntt_backward().sample_extract();
        let m0 = decrypt::<F, D, {N*K}>(&Glwe::<F, D, N, K>::flatten_key(&s), &out_ct);
        assert_eq!(m * a.coeffs[0], m0);
    }
}
