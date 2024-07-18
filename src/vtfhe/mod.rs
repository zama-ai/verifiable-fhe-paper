/*
   This module contains ciphertext structures wrapping plonky2 targets 
   so that they can be used to construct provable circuits on them. 
   These are used to implement verifiable circuits for operations on these
   ciphertexts.
*/

use self::ggsw_ct::GgswCt;
use self::glwe_ct::GlweCt;
use self::glwe_poly::GlwePoly;
use self::lev_ct::LevCt;
use crate::vec_arithmetic::{vec_add, vec_add_many};
use plonky2::field::extension::Extendable;
use plonky2::hash::hash_types::RichField;
use plonky2::iop::target::{BoolTarget, Target};
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2::util::log2_ceil;
use std::array::from_fn;

pub mod crypto;
pub mod ggsw_ct;
pub mod glev_ct;
pub mod glwe_ct;
pub mod glwe_poly;
pub mod ivc_based_vpbs;
pub mod lev_ct;

// the key switch incorporates the sample extraction, hence glwe -> lwe
// we also assume the ksk is set up nicely so that sample extraction is
// literally reading off the coefficients (no rearranging/negating)
pub fn key_switch<
    F: RichField + Extendable<D>,
    const D: usize,
    const LOGB: usize,
    const n: usize,
    const ELL: usize,
    const N: usize,
    const K: usize,
>(
    cb: &mut CircuitBuilder<F, D>,
    glwe_ct: &GlweCt<N, K>,
    ksk: &[LevCt<n, ELL>; N],
) -> Vec<Target> {
    let summands = glwe_ct.flatten()[GlweCt::<N, K>::num_targets() - N..]
        .iter()
        .zip(ksk.iter())
        .map(|(&mask, lev_ct)| lev_ct.mul::<F, D, LOGB>(cb, mask))
        .collect();
    let sum = vec_add_many(cb, &summands);
    let mut init = vec![cb.zero(); n - 1];
    init.push(*glwe_ct.polys.last().unwrap().coeffs.first().unwrap());
    // we assume the KSK encrypts -s_i instead of s_i so we can simply add here
    vec_add(cb, &init, &sum)
}

pub fn poly_select<F: RichField + Extendable<D>, const D: usize, const N: usize>(
    cb: &mut CircuitBuilder<F, D>,
    control: BoolTarget,
    left: &GlwePoly<N>,
    right: &GlwePoly<N>,
) -> GlwePoly<N> {
    let range: [usize; N] = from_fn(|i| i);
    GlwePoly {
        coeffs: range.map(|i| cb.select(control, left.coeffs[i], right.coeffs[i])),
    }
}

pub fn glwe_select<F: RichField + Extendable<D>, const D: usize, const N: usize, const K: usize>(
    cb: &mut CircuitBuilder<F, D>,
    control: BoolTarget,
    left: &GlweCt<N, K>,
    right: &GlweCt<N, K>,
) -> GlweCt<N, K> {
    let range: [usize; K] = from_fn(|i| i);
    GlweCt {
        polys: range.map(|i| poly_select(cb, control, &left.polys[i], &right.polys[i])),
    }
}

pub fn rotate_poly<F: RichField + Extendable<D>, const D: usize, const N: usize>(
    cb: &mut CircuitBuilder<F, D>,
    poly: &GlwePoly<N>,
    shift: Target,
) -> GlwePoly<N> {
    let log2N = log2_ceil(N) + 1;
    let bits = cb.split_le(shift, F::BITS);
    let mut polys = Vec::new();
    // mod switch target to 2N
    let it = bits[F::BITS - log2N..].iter();
    // we round the target by performing a shift by 1 depending on the next bit
    let carry_shift = poly.rotate(cb, 1);
    polys.push(poly_select(
        cb,
        bits[F::BITS - log2N - 1],
        &carry_shift,
        poly,
    ));

    for (log_shift, bit) in it.enumerate() {
        let current = polys.last().unwrap();
        // let current_shift = 2usize.pow((log_shift + 1) as u32);
        let current_shift = 2usize.pow((log_shift) as u32);
        let shifted_poly = current.rotate(cb, current_shift);
        polys.push(poly_select(cb, *bit, &shifted_poly, current));
    }
    polys.remove(polys.len() - 1)
}

pub fn rotate_glwe<F: RichField + Extendable<D>, const D: usize, const N: usize, const K: usize>(
    cb: &mut CircuitBuilder<F, D>,
    glwe: &GlweCt<N, K>,
    shift: Target,
) -> GlweCt<N, K> {
    GlweCt {
        polys: from_fn(|i| rotate_poly(cb, &glwe.polys[i], shift)),
    }
}

pub fn blind_rotation_step<
    F: RichField + Extendable<D>,
    const D: usize,
    const LOGB: usize,
    const N: usize,
    const K: usize,
    const ELL: usize,
>(
    cb: &mut CircuitBuilder<F, D>,
    glwe: &GlweCt<N, K>,
    ggsw: &GgswCt<N, K, ELL>,
    mask_element: Target,
) -> GlweCt<N, K> {
    let shifted_glwe = rotate_glwe::<F, D, N, K>(cb, glwe, mask_element);
    let diff_glwe = shifted_glwe.sub(cb, glwe);
    ggsw.external_product::<F, D, LOGB>(cb, &diff_glwe)
        .add(cb, glwe)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ntt::params::N;
    use crate::vtfhe::crypto::ggsw::Ggsw;
    use crate::vtfhe::crypto::glwe::Glwe;
    use crate::vtfhe::crypto::poly::Poly;

    use plonky2::field::types::{Field, Sample};
    use plonky2::iop::witness::{PartialWitness, WitnessWrite};
    use plonky2::plonk::circuit_data::CircuitConfig;
    use plonky2::plonk::config::{GenericConfig, PoseidonGoldilocksConfig};
    use rand::random;
    use tests::crypto::compute_bsk;
    use tests::crypto::lwe::{encrypt, key_gen};

    fn check_rotation<F: RichField + Extendable<D>, const D: usize, const N: usize>(
        in_poly: &Poly<F, D, N>,
        out_poly: &Poly<F, D, N>,
        mask_element: &F,
    ) {
        let mut shift = mask_element.to_canonical_u64() as usize;
        shift >>= F::BITS - log2_ceil(N) - 2;
        let carry = shift % 2;
        shift >>= 1;
        shift += carry;

        let mut poly = in_poly;
        let neg_poly = &in_poly.scalar_mul(&(-F::ONE));
        if shift > N {
            shift = shift % N;
            poly = neg_poly;
        }

        for i in 0..N - shift {
            assert_eq!(
                poly.coeffs[i],
                out_poly.coeffs[i + shift],
                "poly not rotated correctly."
            )
        }
        for i in 0..shift {
            assert_eq!(
                poly.coeffs[N - shift + i],
                -out_poly.coeffs[i],
                "poly not rotated correctly."
            )
        }
    }

    #[test]
    fn test_poly_rotate() {
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;

        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        let mut pw = PartialWitness::new();

        let poly: GlwePoly<N> = GlwePoly::new_from_builder(&mut builder);
        let mask_element = builder.add_virtual_target();

        poly.register(&mut builder);
        builder.register_public_input(mask_element);

        let poly_vals = Poly::<F, D, N>::rand();
        let mask_val = F::rand();
        poly.assign(&mut pw, &poly_vals);
        pw.set_target(mask_element, mask_val);

        let z = rotate_poly::<F, D, N>(&mut builder, &poly, mask_element);
        z.register(&mut builder);

        let data = builder.build::<C>();
        let proof = data.prove(pw).unwrap();

        let out_poly_sclice = &proof.public_inputs[N + 1..2 * N + 1];
        let out_poly = Poly::<F, D, N>::from_slice(&out_poly_sclice);

        check_rotation(&poly_vals, &out_poly, &mask_val);
        let _ = data.verify(proof).unwrap();
    }

    #[test]
    fn test_blind_rot_step() {
        const LOGB: usize = 8;
        const ELL: usize = 8;
        const K: usize = 2;
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;

        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        let mut pw = PartialWitness::new();

        let glwe = GlweCt::new_from_builder(&mut builder);
        let ggsw = GgswCt::new_from_builder(&mut builder);
        let mask_element = builder.add_virtual_target();

        glwe.register(&mut builder);
        ggsw.register(&mut builder);
        builder.register_public_input(mask_element);

        let s = Glwe::<F, D, N, K>::key_gen();
        let bit = F::from_canonical_u64(rand::random::<u64>() % 2);
        let m_glwe = Poly::<F, D, N> {
            coeffs: from_fn(|i| F::from_canonical_usize(i)),
        };

        let m_ggsw = Poly::constant(&bit);
        let ct_glwe = Glwe::<F, D, N, K>::encrypt(&s, &m_glwe, 0f64);
        let ct_ggsw = Ggsw::<F, D, N, K, ELL>::encrypt::<LOGB>(&s, &m_ggsw, 0f64).ntt_forward();
        let ai = F::rand();

        glwe.assign(&mut pw, &ct_glwe);
        ggsw.assign(&mut pw, &ct_ggsw);
        pw.set_target(mask_element, ai);

        let z =
            blind_rotation_step::<F, D, LOGB, N, K, ELL>(&mut builder, &glwe, &ggsw, mask_element);
        z.register(&mut builder);

        let data = builder.build::<C>();
        let proof = data.prove(pw).unwrap();

        let _ = data.verify(proof.clone()).unwrap();

        let start = GlweCt::<N, K>::num_targets() + GgswCt::<N, K, ELL>::num_targets() + 1;
        let out_glwe_slice = &proof.public_inputs[start..start + GlweCt::<N, K>::num_targets()];
        let out_glwe = Glwe::<F, D, N, K>::from_slice(&out_glwe_slice);
        let m_out = out_glwe.decrypt(&s);
        println!("a: {ai}");
        println!("m_in: {:?}", m_glwe);
        println!("m_out: {:?}", m_out);
        if bit == F::ZERO {
            assert_eq!(m_glwe, m_out);
        } else {
            check_rotation(&m_glwe, &m_out, &ai);
        }
    }

    // this test is flaky due to rounding error in the mod switch
    #[test]
    fn test_blind_rot() {
        const LOGB: usize = 8;
        const ELL: usize = 8;
        const K: usize = 2;
        const n: usize = 2;
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;

        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        let mut pw = PartialWitness::new();

        let acc_in = GlweCt::new_from_builder(&mut builder);
        let bsk: [GgswCt<N, K, ELL>; n] = from_fn(|_| GgswCt::new_from_builder(&mut builder));
        let lwe_ct: [Target; n + 1] = from_fn(|_| builder.add_virtual_target());

        let mut accs = Vec::new();
        let b_negated = builder.neg(lwe_ct[n]);
        accs.push(rotate_glwe(&mut builder, &acc_in, b_negated));
        for i in 0..n {
            accs.push(blind_rotation_step::<F, D, LOGB, N, K, ELL>(
                &mut builder,
                accs.last().unwrap(),
                &bsk[i],
                lwe_ct[i],
            ));
        }

        accs.last().unwrap().register(&mut builder);
        acc_in.register(&mut builder);
        for ggsw in &bsk {
            ggsw.register(&mut builder);
        }

        for element in &lwe_ct {
            builder.register_public_input(*element);
        }

        let s = Glwe::<F, D, N, K>::key_gen();
        let s_lwe = key_gen::<F, D, n>();
        println!("lwe key: {:?}", s_lwe);
        let testv = Poly::<F, D, N> {
            coeffs: from_fn(|i| F::from_canonical_usize(i)),
        };

        println!("init acc: {:?}", testv);

        let test_ct = Glwe::trivial_ct(testv.clone());
        let bsk_vals = compute_bsk::<F, D, N, K, ELL, LOGB>(&s_lwe, &s, 0f64);
        let m = F::from_canonical_u64(random::<u64>() % (N as u64));
        let delta = F::from_noncanonical_biguint(F::order() >> log2_ceil(2 * N));
        let lwe_vals = encrypt::<F, D, n>(&s_lwe, &(delta * m), 0f64);
        println!("m: {m}, -Delta * m: {}", -delta * m);
        println!("lwe_ct: {:?}", lwe_vals);

        acc_in.assign(&mut pw, &test_ct);
        for (ggsw, ggsw_val) in bsk.iter().zip(bsk_vals.iter()) {
            ggsw.assign(&mut pw, ggsw_val);
        }

        for (element, ai) in lwe_ct.iter().zip(lwe_vals.iter()) {
            pw.set_target(*element, *ai);
        }

        let data = builder.build::<C>();
        let proof = data.prove(pw).unwrap();

        let _ = data.verify(proof.clone()).unwrap();

        let out_glwe_slice = &proof.public_inputs[..GlweCt::<N, K>::num_targets()];
        let out_glwe = Glwe::<F, D, N, K>::from_slice(&out_glwe_slice);
        let m_out = out_glwe.decrypt(&s);
        check_rotation(&testv, &m_out, &(-delta * m));
    }

    #[test]
    fn test_glwe_select() {
        const K: usize = 2;
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;

        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        let mut pw = PartialWitness::new();

        let glwe1: GlweCt<N, K> = GlweCt::new_from_builder(&mut builder);
        let glwe2: GlweCt<N, K> = GlweCt::new_from_builder(&mut builder);
        let counter = builder.add_virtual_target();
        let one = builder.one();
        let counter_is_zero = builder.is_equal(counter, one);

        glwe1.register(&mut builder);
        glwe2.register(&mut builder);
        builder.register_public_input(counter);

        let z = glwe_select(&mut builder, counter_is_zero, &glwe1, &glwe2);
        z.register(&mut builder);

        let poly1 = Poly::<F, D, N>::rand();
        let poly2 = Poly::<F, D, N>::rand();
        let s = Glwe::<F, D, N, K>::key_gen();
        let glwe_ct1 = Glwe::encrypt(&s, &poly1, 0f64);
        let glwe_ct2 = Glwe::encrypt(&s, &poly2, 0f64);
        let counter_val = F::TWO;

        glwe1.assign(&mut pw, &glwe_ct1);
        glwe2.assign(&mut pw, &glwe_ct2);
        pw.set_target(counter, counter_val);

        let data = builder.build::<C>();
        let proof = data.prove(pw).unwrap();
        let start = 2 * GlweCt::<N, K>::num_targets() + 1;
        let out_glwe_slice = &proof.public_inputs[start..start + GlweCt::<N, K>::num_targets()];
        let out_glwe = Glwe::from_slice(&out_glwe_slice);

        if counter_val == F::ONE {
            assert_eq!(out_glwe, glwe_ct1);
        } else {
            assert_eq!(out_glwe, glwe_ct2);
        }
    }

    #[test]
    fn test_key_switch() {
        const LOGB: usize = 8;
        const ELL: usize = 2;
        const n: usize = 2;

        const K: usize = 2;

        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;

        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        let mut pw = PartialWitness::new();

        let glwe: GlweCt<N, K> = GlweCt::new_from_builder(&mut builder);
        let ksk: [LevCt<n, ELL>; N] = from_fn(|_| LevCt::new_from_builder(&mut builder));

        glwe.register(&mut builder);
        glwe.set_to_random::<F, D>(&mut pw);

        for lev in &ksk {
            lev.register(&mut builder);
            lev.set_to_random::<F, D>(&mut pw);
        }

        let z = key_switch::<F, D, LOGB, n, ELL, N, K>(&mut builder, &glwe, &ksk);
        builder.register_public_inputs(&z);

        let data = builder.build::<C>();
        let proof = data.prove(pw).unwrap();

        let _ = data.verify(proof).unwrap();
    }
}
