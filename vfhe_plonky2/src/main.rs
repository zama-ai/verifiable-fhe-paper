use anyhow::Result;
use log::{info, LevelFilter};
use plonky2::field::types::{Field, PrimeField64};
use plonky2::plonk::config::{GenericConfig, PoseidonGoldilocksConfig};
use plonky2::util::log2_ceil;
use rand::random;

use ntt::params::N;

use crate::vtfhe::crypto::ggsw::Ggsw;
use crate::vtfhe::crypto::glwe::Glwe;
use crate::vtfhe::crypto::lwe::{decrypt, encrypt, get_delta, get_error, key_gen, mod_switch_ct};
use crate::vtfhe::crypto::{compute_bsk, get_testv};
use crate::vtfhe::ivc_based_vpbs::{verified_pbs, verify_pbs};

mod ntt;
mod vec_arithmetic;
mod vtfhe;

fn main() -> Result<()> {
    // optimized parameters, use N=1024 (see ntt/mod.rs)
    const LOGB: usize = 5;
    const ELL: usize = 4;
    const K: usize = 2; // K = k + 1
    const D: usize = 2;
    const n: usize = 728;
    const p: usize = 2; // plaintext modulus
    let sigma_glwe = 4.99027217501041e-8;
    // let sigma_glwe = 0.0;
    let sigma_lwe = 0.0000117021618159313;
    // let sigma_lwe = (n as f64).sqrt() * sigma_glwe;
    type C = PoseidonGoldilocksConfig;
    type F = <C as GenericConfig<D>>::F;

    // simple_logging::log_to_file(format!("logs/test_w_noise_{n}.log"), LevelFilter::Debug);
    simple_logging::log_to_stderr(LevelFilter::Debug);
    let s_to = Glwe::<F, D, N, K>::partial_key(n);
    // let s_lwe = key_gen::<F, D, n>();
    let s_lwe = Glwe::<F, D, N, K>::flatten_partial_key(&s_to, n);
    info!("s_lwe: {:?}", s_lwe);

    let s_glwe = Glwe::<F, D, N, K>::key_gen();
    let bsk = compute_bsk::<F, D, N, K, ELL, LOGB>(&s_lwe, &s_glwe, sigma_glwe);
    // let s_to = Glwe::<F, D, N, K>::key_from_lwe_key(&s_lwe);
    let ksk = Ggsw::<F, D, N, K, ELL>::compute_ksk::<LOGB>(&s_to, &s_glwe, sigma_lwe);
    // let testv = Poly::<F, D, N> {
    //     coeffs: from_fn(|i| F::from_canonical_usize(i)),
    // };
    // let delta = F::from_noncanonical_biguint(F::order() >> log2_ceil(2*p));
    let delta = get_delta::<F, D>(2 * p);
    let testv = get_testv(p, delta);
    // println!("testv: {:?}", testv);
    // let m = F::from_canonical_usize(random::<usize>() % p);
    let m = F::ONE;
    // let m = F::from_canonical_usize(5);
    // println!("message: {delta} * {m} = {}", delta * m);
    let ct = encrypt::<F, D, n>(&s_lwe, &(delta * m), sigma_lwe);
    // let m = F::rand();
    // let ct = encrypt::<F, D, n>(&s_lwe, &(m));
    // println!("{:?}", ct);
    // println!("sanity check: {}", decrypt::<F, D, n>(&s_lwe, &ct));
    let (out_ct, proof, cd) =
        verified_pbs::<F, C, D, n, N, K, ELL, LOGB>(&ct, &testv, &bsk, &ksk, &s_glwe, &s_lwe, &s_to);

    verify_pbs::<F, C, D, n, N, K, ELL, LOGB>(&out_ct, &ct, &testv, &bsk, &ksk, &proof, &cd);
    // let m_out = out_ct.decrypt(&s_glwe).coeffs;
    let m_bar = out_ct.decrypt(&s_to).coeffs;
    // println!("output ct: {:?}", out_ct);
    // println!("output poly: {:?}", m_out);
    let m_out = F::from_canonical_usize(
        ((m_bar[0].to_canonical_u64() as f64) / (delta.to_canonical_u64() as f64)).round() as usize
            % (2 * p),
    );
    info!("in: {m} out: {m_out}");

    let lwe_out = out_ct.partial_sample_extract(n);
    // let s_flat = Glwe::<F, D, N, K>::flatten_key(&s_to);

    // check that the resulting ciphertext can be bootstrapped again
    info!(
        "error: {}",
        get_error::<F, D, n>(&lwe_out, &s_lwe, delta * m)
    );
    let c_small = mod_switch_ct::<F, D>(&lwe_out, N);
    // let m_out_small_bar = c_small[n]
    //     - c_small.iter().zip(s_flat).fold(0, |acc, (ai, si)| {
    //         acc + ai * (si.to_canonical_u64() as usize)
    //     }) % (2 * N);
    // let rotated_testv = testv.left_shift(m_out_small_bar);
    // info!("small ct decoded: {}", rotated_testv.coeffs[0] / delta);
    info!("out ct mod 2N: {:?}", c_small);
    Ok(())
}
