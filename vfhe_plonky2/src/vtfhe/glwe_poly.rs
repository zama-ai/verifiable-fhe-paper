use std::array::from_fn;

use plonky2::{
    field::extension::Extendable,
    hash::hash_types::RichField,
    iop::{
        target::{BoolTarget, Target},
        witness::{PartialWitness, WitnessWrite},
    },
    plonk::circuit_builder::CircuitBuilder,
};

use crate::ntt::ntt_backward;

use super::crypto::poly::Poly;

pub fn plus_or_minus<F: RichField + Extendable<D>, const D: usize>(
    cb: &mut CircuitBuilder<F, D>,
    b: BoolTarget,
    x: Target,
) -> Target {
    let x_neg = cb.neg(x);
    cb.select(b, x_neg, x)
}

/// Split the given element into a list of targets, where each one represents a
/// base-B limb of the element (centered), with little-endian ordering.
/// TODO: parameterize with ELL and only recompose the ELL ms limbs?
pub fn decompose<F: RichField + Extendable<D>, const D: usize, const LOGB: usize>(
    cb: &mut CircuitBuilder<F, D>,
    x: Target,
    num_limbs: usize,
) -> Vec<Target> {
    let bits = cb.split_le(x, num_limbs * LOGB);
    // (0..num_limbs).map(|i| {cb.le_sum(bits[i * LOGB..(i + 1) * LOGB].into_iter())}).collect()
    let sgn = bits.last().unwrap();
    let x_centered_lift = plus_or_minus(cb, *sgn, x);
    let bits_centered = cb.split_le(x_centered_lift, num_limbs * LOGB);
    let zero: Target = cb.zero();
    let base = cb.constant(F::from_canonical_u64(1u64 << LOGB));
    bits_centered
        .chunks(LOGB)
        .scan(zero, |carry, limb| {
            let k = cb.le_sum(limb.iter());
            let k_w_carry = cb.add(k, *carry);
            *carry = limb.last().unwrap().target;
            let balancer = cb.mul(*carry, base);
            let balanced_k = cb.sub(k_w_carry, balancer);
            Some(plus_or_minus(cb, *sgn, balanced_k))
        })
        .collect()
}

#[derive(Debug)]
pub struct GlwePoly<const N: usize> {
    pub coeffs: [Target; N],
}

impl<const N: usize> GlwePoly<N> {
    pub fn new_from_builder<F: RichField + Extendable<D>, const D: usize>(
        cb: &mut CircuitBuilder<F, D>,
    ) -> Self {
        GlwePoly {
            coeffs: cb.add_virtual_targets(N).try_into().unwrap(),
        }
    }

    pub fn flatten(&self) -> Vec<Target> {
        self.coeffs.to_vec()
    }

    pub fn register<F: RichField + Extendable<D>, const D: usize>(
        &self,
        cb: &mut CircuitBuilder<F, D>,
    ) {
        cb.register_public_inputs(&self.coeffs);
    }

    pub fn set_to_random<F: RichField + Extendable<D>, const D: usize>(
        &self,
        pw: &mut PartialWitness<F>,
    ) {
        for x in self.coeffs.iter() {
            pw.set_target(*x, F::rand());
        }
    }

    pub fn assign<F: RichField + Extendable<D>, const D: usize>(
        &self,
        pw: &mut PartialWitness<F>,
        poly: &Poly<F, D, N>,
    ) {
        for (x, y) in self.coeffs.iter().zip(poly.coeffs.iter()) {
            pw.set_target(*x, *y);
        }
    }

    pub fn add<F: RichField + Extendable<D>, const D: usize>(
        &self,
        cb: &mut CircuitBuilder<F, D>,
        other: &GlwePoly<N>,
    ) -> GlwePoly<N> {
        let range: [usize; N] = from_fn(|i| i);
        GlwePoly {
            coeffs: range.map(|i| cb.add(self.coeffs[i], other.coeffs[i])),
        }
    }

    pub fn sub<F: RichField + Extendable<D>, const D: usize>(
        &self,
        cb: &mut CircuitBuilder<F, D>,
        other: &GlwePoly<N>,
    ) -> GlwePoly<N> {
        let range: [usize; N] = from_fn(|i| i);
        GlwePoly {
            coeffs: range.map(|i| cb.sub(self.coeffs[i], other.coeffs[i])),
        }
    }

    pub fn ntt_backward<F: RichField + Extendable<D>, const D: usize>(
        &self,
        cb: &mut CircuitBuilder<F, D>,
    ) -> GlwePoly<N> {
        GlwePoly {
            coeffs: ntt_backward(cb, &self.coeffs.to_vec()).try_into().unwrap(),
        }
    }

    pub fn rotate<F: RichField + Extendable<D>, const D: usize>(
        &self,
        cb: &mut CircuitBuilder<F, D>,
        shift: usize,
    ) -> GlwePoly<N> {
        let range: [usize; N] = from_fn(|i| i);
        GlwePoly {
            coeffs: range.map(|i| {
                if i < shift {
                    cb.neg(self.coeffs[N - shift + i])
                } else {
                    self.coeffs[i - shift]
                }
            }),
        }
    }

    pub fn decompose<F: RichField + Extendable<D>, const D: usize, const LOGB: usize>(
        &self,
        cb: &mut CircuitBuilder<F, D>,
        num_limbs: usize,
    ) -> Vec<Vec<Target>> {
        let decomps = self
            .coeffs
            .iter()
            .map(|xi| decompose::<F, D, LOGB>(cb, *xi, num_limbs));
        let mut acc = vec![Vec::new(); num_limbs];
        for t in decomps {
            for i in 0..num_limbs {
                acc[i].push(t[i])
            }
        }
        acc
    }

    // pub fn vec_decompose<F: RichField + Extendable<D>, const D: usize, const LOGB: usize>(cb: &mut  CircuitBuilder<F, D>, x: &[Target], num_limbs: usize) -> Vec<Vec<Target>> {
    //     let decomps = x.iter().map(|xi| {decompose::<F, D, LOGB>(cb, *xi, num_limbs)});
    //     let mut acc = vec![Vec::new(); num_limbs];
    //     for t in decomps {
    //         for i in 0..num_limbs {
    //             acc[i].push(t[i])
    //         }
    //     }
    //     acc
    // }

    pub fn num_targets() -> usize {
        N
    }

    pub fn new_from_targets(targets: &[Target]) -> Self {
        assert_eq!(
            targets.len(),
            N,
            "Incorrect number of targets to construct GlwePoly."
        );
        GlwePoly {
            coeffs: targets.to_vec().try_into().unwrap(),
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::vtfhe::glwe_poly::GlwePoly;
    use crate::{ntt::params::N, vtfhe::glwe_poly::decompose};
    use plonky2::field::types::Field;
    use plonky2::{
        field::goldilocks_field::GoldilocksField,
        iop::witness::{PartialWitness, WitnessWrite},
        plonk::{
            circuit_builder::CircuitBuilder,
            circuit_data::CircuitConfig,
            config::{GenericConfig, PoseidonGoldilocksConfig},
        },
    };

    #[test]
    fn test_poly_const_rotate() {
        const K: usize = 2;
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;

        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        let mut pw = PartialWitness::new();

        let poly: GlwePoly<N> = GlwePoly::new_from_builder::<F, D>(&mut builder);

        poly.register(&mut builder);

        poly.set_to_random::<F, D>(&mut pw);
        let shift = 8;
        // let shift = 2usize.pow(rand::random::<u32>() % ( (log2_ceil(N) + 1) as u32));
        let z = poly.rotate(&mut builder, shift);
        z.register(&mut builder);

        let data = builder.build::<C>();
        let proof = data.prove(pw).unwrap();

        let in_poly = &proof.public_inputs[..N];
        let out_poly = &proof.public_inputs[N..2 * N];

        for i in 0..N - shift {
            assert_eq!(
                in_poly[i],
                out_poly[i + shift],
                "poly not rotated correctly."
            )
        }
        for i in 0..shift {
            assert_eq!(
                in_poly[N - shift + i],
                -out_poly[i],
                "poly not rotated correctly."
            )
        }

        let _ = data.verify(proof).unwrap();
    }

    #[test]
    fn test_decompose() {
        const LOGB: usize = 8;
        const D: usize = 2;
        let num_limbs: usize = 8;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;

        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);

        // build_decomposition_lut::<F, D, LOGB>(&mut builder);
        let x = builder.add_virtual_target();

        let z = decompose::<F, D, LOGB>(&mut builder, x, num_limbs);
        // Public inputs are the initial value (provided below) and the result (which is generated).
        builder.register_public_input(x);

        builder.register_public_inputs(&z);

        let mut pw = PartialWitness::new();
        pw.set_target(
            x,
            F::from_noncanonical_u64((1u64 << 63) + (rand::random::<u32>() as u64)),
        );
        // pw.set_target(x, F::rand());

        let data = builder.build::<C>();
        let proof = data.prove(pw).unwrap();

        let input = proof.public_inputs[0];
        let out = &proof.public_inputs[1..num_limbs + 1];
        let base = F::TWO.exp_u64(LOGB as u64);
        let mut sum = F::ZERO;
        for i in 0..num_limbs {
            sum += out[i] * base.exp_u64(i as u64);
        }
        assert_eq!(
            input, sum,
            "Recombined value does not match: {:?} with base {} is not {}",
            out, base, input
        );
        println!("{input} decomposed is {:?}", out);

        let _ = data.verify(proof).unwrap();
    }

    #[test]
    fn test_vec_decompose() {
        const N: usize = 4;
        const LOGB: usize = 8;
        const D: usize = 2;
        let num_limbs: usize = 8;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;

        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        let x = GlwePoly::<N>::new_from_builder(&mut builder);
        // let x = builder.add_virtual_targets(N);

        // let z = vec_decompose::<F, D, LOGB>(&mut builder, &x, num_limbs);
        let z = x.decompose::<F, D, LOGB>(&mut builder, num_limbs);
        // Public inputs are the initial value (provided below) and the result (which is generated).
        // builder.register_public_inputs(&x);
        x.register(&mut builder);

        for zi in z {
            builder.register_public_inputs(&zi);
        }

        let mut pw = PartialWitness::new();
        // for xi in x.into_iter() {
        //     pw.set_target(xi, F::from_canonical_u32(rand::random()));
        // }
        x.set_to_random::<F, D>(&mut pw);

        let data = builder.build::<C>();
        let proof = data.prove(pw).unwrap();

        let base = F::TWO.exp_u64(LOGB as u64);
        for j in 0..N {
            let input = proof.public_inputs[j];
            let out: Vec<&GoldilocksField> =
                proof.public_inputs.iter().skip(N + j).step_by(N).collect();
            let mut sum = F::ZERO;
            for i in 0..num_limbs {
                sum += *out[i] * base.exp_u64(i as u64);
            }
            assert_eq!(
                input, sum,
                "Recombined value does not match: {:?} with base {} is not {}",
                out, base, input
            );
        }

        let _ = data.verify(proof).unwrap();
    }
}
