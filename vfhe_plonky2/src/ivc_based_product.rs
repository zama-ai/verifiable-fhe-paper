use hashbrown::HashMap;
use anyhow::Result;
use plonky2::field::extension::Extendable;
use plonky2::field::goldilocks_field::GoldilocksField;
use plonky2::field::types::{Field, Sample};
use plonky2::gates::noop::NoopGate;
use plonky2::gates::random_access::RandomAccessGate;
use plonky2::hash::hash_types::RichField;
use plonky2::iop::witness::{PartialWitness, WitnessWrite};
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2::plonk::circuit_data::{CircuitConfig, CommonCircuitData};
use plonky2::plonk::config::{AlgebraicHasher, GenericConfig, PoseidonGoldilocksConfig};
// use plonky2::recursion::cyclic_recursion::check_cyclic_proof_verifier_data;
use plonky2::recursion::dummy_circuit::cyclic_base_proof;

// Generates `CommonCircuitData` usable for recursion.
fn common_data_for_recursion<
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F = F>,
    const D: usize,
>() -> CommonCircuitData<F, D>
where
    C::Hasher: AlgebraicHasher<F>,
{
    let config = CircuitConfig::standard_recursion_config();
    let builder = CircuitBuilder::<F, D>::new(config);
    let data = builder.build::<C>();
    let config = CircuitConfig::standard_recursion_config();
    let mut builder = CircuitBuilder::<F, D>::new(config);
    let proof = builder.add_virtual_proof_with_pis(&data.common);
    let verifier_data =
        builder.add_virtual_verifier_data(data.common.config.fri_config.cap_height);
    builder.verify_proof::<C>(&proof, &verifier_data, &data.common);
    let data = builder.build::<C>();

    let config = CircuitConfig::standard_recursion_config();
    let mut builder = CircuitBuilder::<F, D>::new(config);
    let proof = builder.add_virtual_proof_with_pis(&data.common);
    let verifier_data =
        builder.add_virtual_verifier_data(data.common.config.fri_config.cap_height);
    builder.verify_proof::<C>(&proof, &verifier_data, &data.common);
    // let ra_gate2 = RandomAccessGate::<F, D>::new_from_config(&builder.config, 2);
    // let ra_gate3 = RandomAccessGate::<F, D>::new_from_config(&builder.config, 3);
    // let ra_gate4 = RandomAccessGate::<F, D>::new_from_config(&builder.config, 4);
    // builder.add_gate(ra_gate2, vec![]);
    // builder.add_gate(ra_gate3, vec![]);
    // builder.add_gate(ra_gate4, vec![]);
    while builder.num_gates() < 1 << 12 {
        builder.add_gate(NoopGate, vec![]);
    }
    builder.build::<C>().common
}

/// Uses cyclic recursion to build a hash chain.
/// The circuit has the following public input structure:
/// - Initial hash (4)
/// - Output for the tip of the hash chain (4)
/// - Chain length, i.e. the number of times the hash has been applied (1)
/// - VK for cyclic recursion (?)
fn main() -> Result<()> {
    const N: usize = 8;
    const D: usize = 2;
    type C = PoseidonGoldilocksConfig;
    type F = <C as GenericConfig<D>>::F;

    let config = CircuitConfig::standard_recursion_config();
    let mut builder = CircuitBuilder::<F, D>::new(config);
    let one = builder.one();

    // let mut numbers = Vec::new();
    // for _ in 0..N {
    //     numbers.push()
    // }

    // let initial_target = builder.add_virtual_public_input();
    // let initial_targets = builder.add_virtual_targets(N);
    // builder.register_public_inputs(&initial_targets);
    let condition = builder.add_virtual_bool_target_safe();
    let current_prod_in = builder.add_virtual_target();
    let counter = builder.add_virtual_public_input();
    // let current_factor = builder.select(condition, initial_targets[1], initial_targets[0]);
    // let current_factor = builder.random_access(counter, initial_targets.clone());
    let current_factor = builder.add_virtual_target();

    let current_prod_out =
        builder.mul(current_prod_in, current_factor);
    builder.register_public_input(current_prod_out);

    let mut common_data = common_data_for_recursion::<F, C, D>();
    let verifier_data_target = builder.add_verifier_data_public_inputs();
    common_data.num_public_inputs = builder.num_public_inputs();
    println!("{:?}", common_data);

    // Unpack inner proof's public inputs.
    let inner_cyclic_proof_with_pis = builder.add_virtual_proof_with_pis(&common_data);
    let inner_cyclic_pis = &inner_cyclic_proof_with_pis.public_inputs;
    // let inner_cyclic_initial_targets = &inner_cyclic_pis[0..N];
    let inner_cyclic_counter = inner_cyclic_pis[0];
    let inner_cyclic_latest_prod = inner_cyclic_pis[1];

    // Connect our initial hash to that of our inner proof. (If there is no inner proof, the
    // initial hash will be unconstrained, which is intentional.)
    // for (initial_target, inner_cyclic_initial_target) in initial_targets.iter().zip(inner_cyclic_initial_targets.into_iter()) {
    //    builder.connect(*initial_target, *inner_cyclic_initial_target);
    // }

    // The input hash is the previous hash output if we have an inner proof, or the initial hash
    // if this is the base case.
    let actual_prod_in =
        builder.select(condition, inner_cyclic_latest_prod, one);
    builder.connect(current_prod_in, actual_prod_in);

    // Our chain length will be inner_counter + 1 if we have an inner proof, or 1 if not.
    let new_counter = builder.mul_add(condition.target, inner_cyclic_counter, one);
    builder.connect(counter, new_counter);

    builder.conditionally_verify_cyclic_proof_or_dummy::<C>(
        condition,
        &inner_cyclic_proof_with_pis,
        &common_data,
    )?;

    let cyclic_circuit_data = builder.build::<C>();

    println!("all good until here.");

    let mut pw = PartialWitness::new();
    // let initial = [F::ONE, F::from_canonical_usize(3), F::from_canonical_usize(7), F::from_canonical_usize(5)];
    let mut initial = Vec::with_capacity(N);
    // initial.push(F::ONE);
    for _ in 0..initial.capacity() {
        initial.push(F::rand());
    };

    let factors = initial.clone();
    // let initial_pis = initial.into_iter().enumerate().collect();
    // println!("{:?}", initial_pis);
    println!("{:?}", initial);
    let mut initial_pis: HashMap<usize, GoldilocksField> = HashMap::new();
    pw.set_bool_target(condition, false);
    pw.set_target(current_factor, initial.pop().unwrap());
    pw.set_proof_with_pis_target::<C, D>(
        &inner_cyclic_proof_with_pis,
        &cyclic_base_proof(
            &common_data,
            &cyclic_circuit_data.verifier_only,
            initial_pis,
        ),
    );
    pw.set_verifier_data_target(&verifier_data_target, &cyclic_circuit_data.verifier_only);
    let mut proof = cyclic_circuit_data.prove(pw)?;
    // check_cyclic_proof_verifier_data(
    //     &proof,
    //     &cyclic_circuit_data.verifier_only,
    //     &cyclic_circuit_data.common,
    // )?;

    println!("still good");

    for x in 1..N {
        println!("loop {x}");
        // recursive layer.
        // cyclic_circuit_data.verify(proof.clone())?;
        let mut pw = PartialWitness::new();
        pw.set_bool_target(condition, true);
        pw.set_target(current_factor, initial.pop().unwrap());
        pw.set_proof_with_pis_target(&inner_cyclic_proof_with_pis, &proof);
        pw.set_verifier_data_target(&verifier_data_target, &cyclic_circuit_data.verifier_only);
        proof = cyclic_circuit_data.prove(pw)?;
        // check_cyclic_proof_verifier_data(
        //     &proof,
        //     &cyclic_circuit_data.verifier_only,
        //     &cyclic_circuit_data.common,
        // )?;
    }

    // Verify that the proof correctly computes a repeated hash.
    // let initial_hash = &proof.public_inputs[..4];
    // let hash = &proof.public_inputs[4..8];
    // let counter = proof.public_inputs[8];
    // let expected_hash: [F; 4] = iterate_poseidon(
    //     initial_hash.try_into().unwrap(),
    //     counter.to_canonical_u64() as usize,
    // );
    // assert_eq!(hash, expected_hash);
    // cyclic_circuit_data.verify(proof.clone())?;

    // let factor1 = proof.public_inputs[1];
    // let factor2 = proof.public_inputs[2];
    // let factors = &proof.public_inputs[0..N];
    // let prod = proof.public_inputs[N + 1];
    // let counter = proof.public_inputs[N];
    let counter = proof.public_inputs[0];
    let prod = proof.public_inputs[1];

    println!(
        "product of {:?} is {}, number of factors is {}",
        factors,
        prod,
        counter
    );

    println!(
        "proof size: {} bytes",
        proof.to_bytes().len()
    );
    Ok(())
}
