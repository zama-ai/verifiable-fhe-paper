use log::debug;
use plonky2::{field::extension::Extendable, hash::hash_types::RichField};

use self::{ggsw::Ggsw, poly::Poly};

pub mod ggsw;
pub mod glev;
pub mod glwe;
pub mod lwe;
pub mod poly;

pub fn get_testv<F: RichField + Extendable<D>, const D: usize, const N: usize>(
    p: usize,
    delta: F,
) -> Poly<F, D, N> {
    let block_size = N / p;
    let coeffs: Vec<F> = (0..p)
        .flat_map(|i| vec![F::from_canonical_usize(i) * delta; block_size])
        .collect();

    Poly::from_slice(&coeffs).left_shift(block_size / 2)
}

pub fn compute_bsk<
    F: RichField + Extendable<D>,
    const D: usize,
    const N: usize,
    const K: usize,
    const ELL: usize,
    const LOGB: usize,
>(
    s_lwe: &[F],
    s_glwe: &[Poly<F, D, N>],
    sigma: f64,
) -> Vec<Ggsw<F, D, N, K, ELL>> {
    s_lwe
        .iter()
        .map(|si| Ggsw::encrypt::<LOGB>(s_glwe, &Poly::constant(si), sigma).ntt_forward())
        .collect()
}
