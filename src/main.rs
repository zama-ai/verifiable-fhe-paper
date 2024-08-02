use anyhow::Result;
use log::{info, LevelFilter};
use plonky2::field::types::{Field, PrimeField64};
use plonky2::plonk::config::{GenericConfig, PoseidonGoldilocksConfig};
use rand::random;

use ntt::params::N;

use crate::vtfhe::crypto::ggsw::Ggsw;
use crate::vtfhe::crypto::glwe::Glwe;
use crate::vtfhe::crypto::lwe::{encrypt, get_delta};
use crate::vtfhe::crypto::{compute_bsk, get_testv};
use crate::vtfhe::ivc_based_vpbs::{verified_pbs, verify_pbs};

mod ntt;
mod vec_arithmetic;
mod vtfhe;

fn main() -> Result<()> {
    // optimized parameters, use N=1024 (see ntt/mod.rs)

    // dcecomposition parameters
    const LOGB: usize = 5;
    const ELL: usize = 4;

    const K: usize = 2; // GLWE dimension (K = k + 1)
    const n: usize = 728; // LWE dimension
    const p: usize = 2; // plaintext modulus
    let sigma_glwe = 4.99027217501041e-8; // GLWE noise
    let sigma_lwe = 0.0000117021618159313; // LWE noise

    // plonky2 parameters
    const D: usize = 2;
    type C = PoseidonGoldilocksConfig;
    type F = <C as GenericConfig<D>>::F;

    simple_logging::log_to_stderr(LevelFilter::Debug);

    // partial GLWE key corresponding to LWE key
    let s_to = Glwe::<F, D, N, K>::partial_key(n);
    let s_lwe = Glwe::<F, D, N, K>::flatten_partial_key(&s_to, n);
    info!("s_lwe: {:?}", s_lwe);

    let s_glwe = Glwe::<F, D, N, K>::key_gen();
    let bsk = compute_bsk::<F, D, N, K, ELL, LOGB>(&s_lwe, &s_glwe, sigma_glwe);
    let ksk = Ggsw::<F, D, N, K, ELL>::compute_ksk::<LOGB>(&s_to, &s_glwe, sigma_lwe);
    
    let delta = get_delta::<F, D>(2 * p);
    let testv = get_testv(p, delta);
    let m_1 = F::from_canonical_usize(random::<usize>() % p);
    let m_2 = F::from_canonical_usize(random::<usize>() % p);
    let w_1 = F::ONE;
    let w_2 = F::TWO;
    let ct_1 = encrypt::<F, D, n>(&s_lwe, &(delta * m_1), sigma_lwe);
    let ct_2 = encrypt::<F, D, n>(&s_lwe, &(delta * m_2), sigma_lwe);

    // prove a PBS
    let (out_ct, proof, cd) =
        verified_pbs::<F, C, D, n, N, K, ELL, LOGB>(&ct_1, &ct_2, &w_1, &w_2, &testv, &bsk, &ksk, &s_glwe, &s_lwe, &s_to);

    // verify the PBS
    verify_pbs::<F, C, D, n, N, K, ELL, LOGB>(&out_ct, &ct_1, &ct_2, &w_1, &w_2, &testv, &bsk, &ksk, &proof, &cd);
    let m_bar = out_ct.decrypt(&s_to).coeffs;

    let m_out = F::from_canonical_usize(
        ((m_bar[0].to_canonical_u64() as f64) / (delta.to_canonical_u64() as f64)).round() as usize
            % (2 * p),
    );
    info!("in: {m_1} * {w_1} + {m_2} * {w_2} out: {m_out}");
    Ok(())
}
