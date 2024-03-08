use std::array::from_fn;

use plonky2::{
    field::extension::Extendable,
    hash::hash_types::RichField,
    iop::{target::Target, witness::PartialWitness},
    plonk::circuit_builder::CircuitBuilder,
};

use super::{crypto::ggsw::Ggsw, glev_ct::GlevCt, glwe_ct::GlweCt, glwe_poly::GlwePoly};

pub fn glwe_add_many<
    F: RichField + Extendable<D>,
    const D: usize,
    const N: usize,
    const K: usize,
>(
    cb: &mut CircuitBuilder<F, D>,
    glwes: &[GlweCt<N, K>],
) -> GlweCt<N, K> {
    let range: [usize; K] = from_fn(|i| i);
    let init = GlweCt {
        polys: range.map(|_| GlwePoly {
            coeffs: [cb.zero(); N],
        }),
    };

    glwes.into_iter().fold(init, |acc, t| acc.add(cb, &t))
}

#[derive(Debug)]
pub struct GgswCt<const N: usize, const K: usize, const ELL: usize> {
    pub glev_cts: [GlevCt<N, K, ELL>; K],
}

impl<const N: usize, const K: usize, const ELL: usize> GgswCt<N, K, ELL> {
    pub fn new_from_builder<F: RichField + Extendable<D>, const D: usize>(
        cb: &mut CircuitBuilder<F, D>,
    ) -> Self {
        let range: [usize; K] = core::array::from_fn(|i| i);
        GgswCt {
            glev_cts: range.map(|_| GlevCt::new_from_builder(cb)),
        }
    }

    pub fn new_from_targets(targets: &[Target]) -> Self {
        let glev_targets = GlevCt::<N, K, ELL>::num_targets();
        assert_eq!(
            targets.len(),
            K * glev_targets,
            "Incorrect number of targets to construct GgswCt."
        );
        GgswCt {
            glev_cts: targets
                .chunks(glev_targets)
                .map(|t| GlevCt::<N, K, ELL>::new_from_targets(t))
                .collect::<Vec<_>>()
                .try_into()
                .unwrap(),
        }
    }

    pub fn flatten(&self) -> Vec<Target> {
        self.glev_cts
            .iter()
            .flat_map(|glev| glev.flatten())
            .collect()
    }

    pub fn register<F: RichField + Extendable<D>, const D: usize>(
        &self,
        cb: &mut CircuitBuilder<F, D>,
    ) {
        for glev_ct in &self.glev_cts {
            glev_ct.register(cb);
        }
    }

    pub fn set_to_random<F: RichField + Extendable<D>, const D: usize>(
        &self,
        pw: &mut PartialWitness<F>,
    ) {
        for glev_ct in &self.glev_cts {
            glev_ct.set_to_random(pw);
        }
    }

    pub fn assign<F: RichField + Extendable<D>, const D: usize>(
        &self,
        pw: &mut PartialWitness<F>,
        ct: &Ggsw<F, D, N, K, ELL>,
    ) {
        for (x, y) in self.glev_cts.iter().zip(ct.glevs.iter()) {
            x.assign(pw, y);
        }
    }

    pub fn external_product<F: RichField + Extendable<D>, const D: usize, const LOGB: usize>(
        &self,
        cb: &mut CircuitBuilder<F, D>,
        glwe: &GlweCt<N, K>,
    ) -> GlweCt<N, K> {
        let glev_muls: Vec<GlweCt<N, K>> = glwe
            .polys
            .iter()
            .zip(self.glev_cts.iter())
            .map(|(glwe_poly, glev)| glev.mul::<F, D, LOGB>(cb, &glwe_poly))
            .collect();
        let sum_polys = glwe_add_many(cb, &glev_muls[..K - 1]);
        // sum_polys.sub(cb, &glev_muls[K - 1]).ntt_backward(cb)
        glev_muls[K - 1].sub(cb, &sum_polys).ntt_backward(cb)
    }

    pub fn num_targets() -> usize {
        K * K * N * ELL
    }
}

#[cfg(test)]
mod tests {
    use plonky2::field::types::Field;
    use plonky2::plonk::{
        circuit_data::CircuitConfig,
        config::{GenericConfig, PoseidonGoldilocksConfig},
    };

    use crate::ntt::params::N;
    use crate::vtfhe::{
        crypto::{glwe::Glwe, poly::Poly},
        glwe_ct::GlweCt,
    };

    use super::*;
    #[test]
    fn test_external_product() {
        const LOGB: usize = 8;
        const ELL: usize = 8;
        const K: usize = 3;
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;

        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        let mut pw = PartialWitness::new();

        let glwe = GlweCt::<N, K>::new_from_builder(&mut builder);
        let ggsw = GgswCt::<N, K, ELL>::new_from_builder(&mut builder);

        glwe.register(&mut builder);
        ggsw.register(&mut builder);

        let s = Glwe::<F, D, N, K>::key_gen();
        let m_glwe = Poly::<F, D, N> {
            coeffs: from_fn(|i| F::from_canonical_usize(i)),
        };
        let bit = F::from_canonical_u64(rand::random::<u64>() % 2);
        let m_ggsw = Poly::<F, D, N>::constant(&bit);

        let ct_glwe = Glwe::<F, D, N, K>::encrypt(&s, &m_glwe, 0f64);
        let ct_ggsw = Ggsw::<F, D, N, K, ELL>::encrypt::<LOGB>(&s, &m_ggsw, 0f64).ntt_forward();

        glwe.assign(&mut pw, &ct_glwe);
        ggsw.assign(&mut pw, &ct_ggsw);

        let z = ggsw.external_product::<F, D, LOGB>(&mut builder, &glwe);
        z.register(&mut builder);

        let data = builder.build::<C>();
        let proof = data.prove(pw).unwrap();

        let _ = data.verify(proof.clone()).unwrap();
        let start = GlweCt::<N, K>::num_targets() + GgswCt::<N, K, ELL>::num_targets();
        let out_glwe_slice = &proof.public_inputs[start..start+GlweCt::<N, K>::num_targets()];
        let out_glwe = Glwe::<F, D, N, K>::from_slice(&out_glwe_slice);
        let m_out = out_glwe.decrypt(&s);
        assert_eq!(m_glwe.scalar_mul(&bit), m_out);
    }

    #[test]
    fn test_key_switch() {
        const LOGB: usize = 8;
        const ELL: usize = 8;
        const K: usize = 3;
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;

        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        let mut pw = PartialWitness::new();

        let glwe = GlweCt::<N, K>::new_from_builder(&mut builder);
        let ggsw = GgswCt::<N, K, ELL>::new_from_builder(&mut builder);

        glwe.register(&mut builder);
        ggsw.register(&mut builder);

        let s_to = Glwe::<F, D, N, K>::key_gen();
        let s_from = Glwe::<F, D, N, K>::key_gen();
        let ksk = Ggsw::<F, D, N, K, ELL>::compute_ksk::<LOGB>(&s_to, &s_from, 0f64);

        let m_glwe = Poly::<F, D, N>::rand();
        let ct_glwe = Glwe::<F, D, N, K>::encrypt(&s_from, &m_glwe, 0f64);

        glwe.assign(&mut pw, &ct_glwe);
        ggsw.assign(&mut pw, &ksk);

        let z = ggsw.external_product::<F, D, LOGB>(&mut builder, &glwe);
        z.register(&mut builder);

        let data = builder.build::<C>();
        let proof = data.prove(pw).unwrap();

        let _ = data.verify(proof.clone()).unwrap();
        let start = GlweCt::<N, K>::num_targets() + GgswCt::<N, K, ELL>::num_targets();
        let out_glwe_slice = &proof.public_inputs[start..start+GlweCt::<N, K>::num_targets()];
        let out_glwe = Glwe::<F, D, N, K>::from_slice(&out_glwe_slice);
        let m_out = out_glwe.decrypt(&s_to);
        assert_eq!(m_glwe, m_out);
    }
}
