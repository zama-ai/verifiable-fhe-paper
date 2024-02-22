use anyhow::Result;
use log::{info, Level, LevelFilter};
use plonky2::field::types::{Field, Sample};
use plonky2::iop::witness::{PartialWitness, WitnessWrite};
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2::plonk::circuit_data::CircuitConfig;
use plonky2::plonk::config::{GenericConfig, PoseidonGoldilocksConfig};
use plonky2::plonk::prover::prove;
use plonky2::timed;
use plonky2::util::timing::TimingTree;

use ntt::params::N;

use crate::ntt::{ntt_backward, ntt_forward, params};
// use crate::vec_arithmetic::build_decomposition_lut;
use crate::vtfhe::blind_rotation_step;
use crate::vtfhe::crypto::ggsw::Ggsw;
use crate::vtfhe::crypto::glwe::Glwe;
use crate::vtfhe::crypto::lwe::{encrypt, key_gen};
use crate::vtfhe::crypto::poly::Poly;
use crate::vtfhe::ggsw_ct::GgswCt;
use crate::vtfhe::glwe_ct::GlweCt;

mod ntt;
mod vec_arithmetic;
mod vtfhe;

fn main() -> Result<()> {
    // let mut lbuilder = env_logger::Builder::from_default_env();
    // lbuilder.format_timestamp(None);
    // lbuilder.try_init()?;

    const LOGB: usize = 5;
    const ELL: usize = 4;
    const K: usize = 2;
    const D: usize = 2;
    const n: usize = 2;

    simple_logging::log_to_file(format!("logs/test_{n}.log"), LevelFilter::Debug);
    // simple_logging::log_to_stderr(LevelFilter::Debug);
    info!(
        "Parameters: n={n}, N={N}, k={}, logB={LOGB}, ell={ELL}",
        K - 1
    );

    type C = PoseidonGoldilocksConfig;
    type F = <C as GenericConfig<D>>::F;

    let config = CircuitConfig::standard_recursion_config();
    let mut builder = CircuitBuilder::<F, D>::new(config);
    let mut pw = PartialWitness::new();

    let glwe = GlweCt::new_from_builder(&mut builder);
    let mut bsk = Vec::new();
    let mut lwe_ct = Vec::new();

    let mut bsk_vals = Vec::new();

    let s_lwe = key_gen::<F, D, n>();
    let s_glwe = Glwe::<F, D, N, K>::key_gen();
    for si in &s_lwe {
        bsk.push(GgswCt::new_from_builder(&mut builder));
        lwe_ct.push(builder.add_virtual_target());

        bsk_vals.push(Ggsw::<F, D, N, K, ELL>::encrypt::<LOGB>(
            &s_glwe,
            &Poly::<F, D, N>::constant(si),
            0f64,
        ));
    }

    let m = F::rand();
    let ct_lwe = encrypt::<F, D, n>(&s_lwe, &m, 0f64);

    glwe.register(&mut builder);
    for (ggsw, val) in bsk.iter().zip(bsk_vals.iter()) {
        ggsw.register(&mut builder);
        // ggsw.set_to_random::<F, D>(&mut pw);
        ggsw.assign(&mut pw, val);
    }
    for (mask_element, val) in lwe_ct.iter().zip(ct_lwe.iter()) {
        builder.register_public_input(*mask_element);
        pw.set_target(*mask_element, *val);
    }

    // glwe.set_to_random::<F, D>(&mut pw);
    let mut glwe_vals = Vec::new();
    for _ in 0..K-1 {
        glwe_vals.extend(vec![F::ZERO; N])
    }
    glwe_vals.extend((0..N).map(|i| F::from_canonical_u64(i as u64)));
    glwe.assign(&mut pw, &Glwe::<F, D, N, K>::from_slice(&glwe_vals));

    // let mut z = Vec::new();
    // // for _ in 0..n {
    // for (mask_element, ggsw) in lwe_ct.iter().zip(bsk.iter()) {
    //     z.push(blind_rotation_step::<F, D, LOGB, N, K, ELL>(&mut builder, &glwe, ggsw, *mask_element));
    // }
    // z.last().unwrap().register(&mut builder);

    let z = lwe_ct[..n-1]
        .iter()
        .zip(bsk.iter())
        .fold(glwe, |acc, (mask_element, ggsw)| {
            blind_rotation_step::<F, D, LOGB, N, K, ELL>(&mut builder, &acc, ggsw, *mask_element)
        });

    // let z = blind_rotation_step::<F, D, LOGB, N, K, ELL>(&mut builder, &glwe, &ggsw, mask_element);
    z.register(&mut builder);

    info!("Number of gates: {}", builder.num_gates());
    let data = builder.build::<C>();
    // let proof = data.prove(pw).unwrap();
    let mut timing = TimingTree::new("prove", Level::Info);
    let proof = prove::<F, C, D>(&data.prover_only, &data.common, pw, &mut timing)?;
    timing.print();

    let proof_bytes: Vec<u8> = proof.to_bytes();
    info!("Proof length: {} bytes", proof_bytes.len());
    let mut timing: TimingTree = TimingTree::new("verify", Level::Info);
    let _ = timed!(timing, "verifying", data.verify(proof).unwrap());
    timing.print();
    Ok(())
}
