use plonky2::field::extension::Extendable;
use plonky2::hash::hash_types::RichField;
use plonky2::iop::target::Target;
use plonky2::plonk::circuit_builder::CircuitBuilder;

pub fn vec_add<F: RichField + Extendable<D>, const D: usize>(
    cb: &mut CircuitBuilder<F, D>,
    left: &[Target],
    right: &[Target],
) -> Vec<Target> {
    left.into_iter()
        .zip(right.into_iter())
        .map(|(l, r)| cb.add(*l, *r))
        .collect()
}

// element-wise multiplication
pub fn vec_mul<F: RichField + Extendable<D>, const D: usize>(
    cb: &mut CircuitBuilder<F, D>,
    left: &[Target],
    right: &[Target],
) -> Vec<Target> {
    left.into_iter()
        .zip(right.into_iter())
        .map(|(l, r)| cb.mul(*l, *r))
        .collect()
}

pub fn scalar_mul<F: RichField + Extendable<D>, const D: usize>(
    cb: &mut CircuitBuilder<F, D>,
    left: Target,
    right: &[Target],
) -> Vec<Target> {
    right.into_iter().map(|r| cb.mul(left, *r)).collect()
}

// Add `n` vectors of `Target`s.
pub fn vec_add_many<F: RichField + Extendable<D>, const D: usize>(
    cb: &mut CircuitBuilder<F, D>,
    terms: &Vec<Vec<Target>>,
) -> Vec<Target> {
    let N = terms.into_iter().next().unwrap().len();
    let init = vec![cb.zero(); N];
    terms
        .into_iter()
        .fold(init, |acc: Vec<Target>, t| vec_add(cb, &acc, &t))
}

pub fn vec_inner<F: RichField + Extendable<D>, const D: usize>(
    cb: &mut CircuitBuilder<F, D>,
    left: &Vec<Vec<Target>>,
    right: &Vec<Vec<Target>>,
) -> Vec<Target> {
    let N = left.into_iter().next().unwrap().len();
    let N_ = right.into_iter().next().unwrap().len();
    assert_eq!(N, N_, "Vectors have different dimensions: {} != {}.", N, N_);

    let summands = &left
        .into_iter()
        .zip(right.into_iter())
        .map(|(l, r)| vec_mul(cb, l, r))
        .collect();
    vec_add_many(cb, summands)
}

#[cfg(test)]
mod tests {
    use super::*;
    use plonky2::field::types::Field;
    use plonky2::iop::witness::{PartialWitness, WitnessWrite};
    use plonky2::plonk::circuit_builder::CircuitBuilder;
    use plonky2::plonk::circuit_data::CircuitConfig;
    use plonky2::plonk::config::{GenericConfig, PoseidonGoldilocksConfig};

    #[test]
    fn test_vec_add() {
        const N: usize = 4;
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;

        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        let x = builder.add_virtual_targets(N);
        let y = builder.add_virtual_targets(N);

        let z = vec_add(&mut builder, &x, &y);
        
        builder.register_public_inputs(&x);
        builder.register_public_inputs(&y);
        builder.register_public_inputs(&z);
        let mut pw = PartialWitness::new();
        for xi in x.into_iter() {
            pw.set_target(xi, F::from_canonical_u32(rand::random()));
        }

        for yi in y.into_iter() {
            pw.set_target(yi, F::from_canonical_u32(rand::random()));
        }

        let data = builder.build::<C>();
        let proof = data.prove(pw).unwrap();

        let left = &proof.public_inputs[0..N];
        let right = &proof.public_inputs[N..2 * N];
        let out = &proof.public_inputs[2 * N..3 * N];

        for ((&l, &r), &o) in left.into_iter().zip(right.into_iter()).zip(out.into_iter()) {
            assert_eq!(l + r, o);
        }

        let _ = data.verify(proof).unwrap();
    }

    #[test]
    fn test_vec_mul() {
        const N: usize = 4;
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;

        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        let x = builder.add_virtual_targets(N);
        let y = builder.add_virtual_targets(N);

        let z = vec_mul(&mut builder, &x, &y);
        
        builder.register_public_inputs(&x);
        builder.register_public_inputs(&y);
        builder.register_public_inputs(&z);
        let mut pw = PartialWitness::new();
        for xi in x.into_iter() {
            pw.set_target(xi, F::from_canonical_u32(rand::random()));
        }

        for yi in y.into_iter() {
            pw.set_target(yi, F::from_canonical_u32(rand::random()));
        }

        let data = builder.build::<C>();
        let proof = data.prove(pw).unwrap();

        let left = &proof.public_inputs[0..N];
        let right = &proof.public_inputs[N..2 * N];
        let out = &proof.public_inputs[2 * N..3 * N];

        for ((&l, &r), &o) in left.into_iter().zip(right.into_iter()).zip(out.into_iter()) {
            assert_eq!(l * r, o);
        }

        let _ = data.verify(proof).unwrap();
    }

    #[test]
    fn test_vec_add_many() {
        const NUMV: usize = 3;
        const N: usize = 4;
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;

        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        let mut pw = PartialWitness::new();
        let mut targets = Vec::new();
        for _ in 0..NUMV {
            targets.push(builder.add_virtual_targets(N));
        }

        for x in targets.iter() {
            builder.register_public_inputs(&x);
            for xi in x.iter() {
                pw.set_target(*xi, F::from_canonical_u32(rand::random()));
            }
        }

        let z = vec_add_many(&mut builder, &targets);
        builder.register_public_inputs(&z);

        let data = builder.build::<C>();
        let proof = data.prove(pw).unwrap();

        for i in 0..N {
            let mut sum = F::ZERO;
            for j in 0..NUMV {
                sum += proof.public_inputs[j * N + i];
            }
            assert_eq!(sum, proof.public_inputs[NUMV * N + i]);
        }

        let _ = data.verify(proof).unwrap();
    }

    #[test]
    fn test_vec_inner() {
        const NUMV: usize = 3;
        const N: usize = 4;
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;

        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        let mut pw = PartialWitness::new();
        let mut ltargets = Vec::new();
        let mut rtargets = Vec::new();
        for targets in [&mut ltargets, &mut rtargets] {
            for _ in 0..NUMV {
                targets.push(builder.add_virtual_targets(N));
            }
        }

        for targets in [&mut ltargets, &mut rtargets] {
            for x in targets.iter() {
                builder.register_public_inputs(&x);
                for xi in x.iter() {
                    pw.set_target(*xi, F::from_canonical_u32(rand::random()));
                }
            }
        }

        let z = vec_inner(&mut builder, &ltargets, &rtargets);
        builder.register_public_inputs(&z);

        let data = builder.build::<C>();
        let proof = data.prove(pw).unwrap();

        for i in 0..N {
            let mut sum = F::ZERO;
            for j in 0..NUMV {
                sum += proof.public_inputs[j * N + i] * proof.public_inputs[(NUMV + j) * N + i];
            }
            assert_eq!(sum, proof.public_inputs[2 * NUMV * N + i]);
        }

        let _ = data.verify(proof).unwrap();
    }
}
