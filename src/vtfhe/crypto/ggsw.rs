use std::array::from_fn;

use plonky2::{field::extension::Extendable, hash::hash_types::RichField};

use super::{glev::Glev, poly::Poly};

#[derive(Debug)]
pub struct Ggsw<
    F: RichField + Extendable<D>,
    const D: usize,
    const N: usize,
    const K: usize,
    const ELL: usize,
> {
    pub glevs: [Glev<F, D, N, K, ELL>; K],
}

impl<
        F: RichField + Extendable<D>,
        const D: usize,
        const N: usize,
        const K: usize,
        const ELL: usize,
    > Ggsw<F, D, N, K, ELL>
{
    pub fn encrypt<const LOGB: usize>(s: &[Poly<F, D, N>], m: &Poly<F, D, N>, sigma: f64) -> Self {
        Ggsw {
            glevs: from_fn(|i| {
                if i < K - 1 {
                    Glev::<F, D, N, K, ELL>::encrypt::<LOGB>(s, &m.mul(&s[i]), sigma)
                } else {
                    Glev::<F, D, N, K, ELL>::encrypt::<LOGB>(s, &m, sigma)
                }
            }),
        }
    }

    pub fn compute_ksk<const LOGB: usize>(s_to: &[Poly<F, D, N>], s_from: &[Poly<F, D, N>], sigma: f64) -> Self {
        Ggsw {
            glevs: from_fn(|i| {
                if i < K - 1 {
                    Glev::<F, D, N, K, ELL>::encrypt::<LOGB>(s_to, &s_from[i], sigma)
                } else {
                    Glev::<F, D, N, K, ELL>::encrypt::<LOGB>(s_to, &Poly::constant(&F::ONE), sigma)
                }
            }),
        }.ntt_forward()
    }

    pub fn ntt_forward(&self) -> Self {
        Ggsw {
            glevs: from_fn(|i| self.glevs[i].ntt_forward()),
        }
    }

    pub fn dummy_ct() -> Self {
        Ggsw {
            glevs: from_fn(|_| Glev::dummy_ct()),
        }
    }

    pub fn flatten(&self) -> Vec<F> {
        self.glevs.iter().flat_map(|glev| glev.flatten()).collect()
    }
}
