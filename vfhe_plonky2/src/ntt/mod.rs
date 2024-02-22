use plonky2::field::extension::Extendable;
use plonky2::hash::hash_types::RichField;
use plonky2::iop::target::Target;
use plonky2::plonk::circuit_builder::CircuitBuilder;

#[path = "params_1024.rs"]
pub mod params;

fn ntt_fw_update<F: RichField + Extendable<D>, const D: usize>(cb: &mut  CircuitBuilder<F, D>, input: &Vec<Target>, m: usize) -> Vec<Target> {
    let mut a = input.clone();
    let t = params::N / (2 * m);
    for i in 0..m {
        let j1 = 2 * i * t;
        let j2 = j1 + t;
        let root = params::ROOTS[m + i];
        let s = cb.constant(F::from_canonical_u64(root));
        for j in j1..j2 {
            let u = a[j];
            let v = cb.mul(a[j + t], s);
            a[j] = cb.add(u, v);
            a[j+t] = cb.sub(u, v);
        }
    }
    a
}

pub fn ntt_forward<F: RichField + Extendable<D>, const D: usize>(cb: &mut  CircuitBuilder<F, D>, input: &Vec<Target>) -> Vec<Target>
{
    let mut current = input.clone();
    for m in (0..params::LOGN).map(|i| {2usize.pow(i)}) {
        current = ntt_fw_update(cb, &current, m);
    }

    current
}


fn ntt_bw_update<F: RichField + Extendable<D>, const D: usize>(cb: &mut  CircuitBuilder<F, D>, input: &Vec<Target>, m: usize) -> Vec<Target> {
    let mut a = input.clone();
    let t = params::N / (2 * m);
    let mut j1 = 0usize;
    for i in 0..m {
        let j2 = j1 + t;
        let root = params::INVROOTS[m + i];
        let s = cb.constant(F::from_canonical_u64(root));
        for j in j1..j2 {
            let u = a[j];
            let v = a[j + t];
            a[j] = cb.add(u, v);
            let w = cb.sub(u, v);
            a[j+t] = cb.mul(w , s);
        }
        j1 += 2 * t;
    }
    a
}

pub fn ntt_backward<F: RichField + Extendable<D>, const D: usize>(cb: &mut  CircuitBuilder<F, D>, input: &Vec<Target>) -> Vec<Target>
{
    let mut current = input.clone();
    for m in (0..params::LOGN).rev().map(|i| {2usize.pow(i)}) {
        current = ntt_bw_update(cb, &current, m);
    }

    let n_inv = cb.constant(F::from_canonical_u64(params::NINV));
    current.into_iter().map(|g|{cb.mul(g, n_inv)}).collect()
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
    fn test_ntt_forward() {
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;
        let N = params::N;

        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        let x = builder.add_virtual_targets(N);

        let z = ntt_forward(&mut builder, &x);
        // Public inputs are the initial value (provided below) and the result (which is generated).
        builder.register_public_inputs(&x);
        builder.register_public_inputs(&z);
        let mut pw = PartialWitness::new();
        pw.set_target_arr(&x, &params::TESTG.map(|g| {F::from_canonical_u64(g)}));

        let data = builder.build::<C>();
        let proof = data.prove(pw).unwrap();
        // println!(
        //     "{:?} + {:?} = {:?}",
        //     &proof.public_inputs[0..n],
        //     &proof.public_inputs[n..2*n],
        //     &proof.public_inputs[2*n..3*n],
        // );
        let out = &proof.public_inputs[N..2 * N];

        for (&actual, expected ) in out.into_iter().zip(params::TESTGHAT) {
            assert_eq!(actual, F::from_canonical_u64(expected));
        }

        let _ = data.verify(proof).unwrap();
    }

    #[test]
    fn test_ntt_backward() {
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;
        let N = params::N;

        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        let x = builder.add_virtual_targets(N);

        let z = ntt_backward(&mut builder, &x);
        // Public inputs are the initial value (provided below) and the result (which is generated).
        builder.register_public_inputs(&x);
        builder.register_public_inputs(&z);
        let mut pw = PartialWitness::new();
        pw.set_target_arr(&x, &params::TESTGHAT.map(|g| {F::from_canonical_u64(g)}));

        let data = builder.build::<C>();
        let proof = data.prove(pw).unwrap();
        // println!(
        //     "{:?} + {:?} = {:?}",
        //     &proof.public_inputs[0..n],
        //     &proof.public_inputs[n..2*n],
        //     &proof.public_inputs[2*n..3*n],
        // );
        let out = &proof.public_inputs[N..2 * N];

        for (&actual, expected ) in out.into_iter().zip(params::TESTG) {
            assert_eq!(actual, F::from_canonical_u64(expected));
        }

        let _ = data.verify(proof).unwrap();
    }
}
