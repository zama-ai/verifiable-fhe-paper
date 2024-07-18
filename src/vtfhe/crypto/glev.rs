use std::array::from_fn;

use plonky2::{field::extension::Extendable, hash::hash_types::RichField, util::ceil_div_usize};

use super::{glwe::Glwe, poly::Poly};

#[derive(Debug)]
pub struct Glev<
    F: RichField + Extendable<D>,
    const D: usize,
    const N: usize,
    const K: usize,
    const ELL: usize,
> {
    pub glwes: [Glwe<F, D, N, K>; ELL],
}

impl<
        F: RichField + Extendable<D>,
        const D: usize,
        const N: usize,
        const K: usize,
        const ELL: usize,
    > Glev<F, D, N, K, ELL>
{
    pub fn encrypt<const LOGB: usize>(s: &[Poly<F, D, N>], m: &Poly<F, D, N>, sigma: f64) -> Self {
        let base = F::TWO.exp_u64(LOGB as u64);
        let first_limb = ceil_div_usize(F::BITS, LOGB) - ELL;
        Glev {
            glwes: from_fn(|i| {
                Glwe::encrypt(
                    s,
                    &m.scalar_mul(&base.exp_u64((first_limb + i) as u64)),
                    sigma,
                )
            }),
        }
    }

    pub fn ntt_forward(&self) -> Self {
        Glev {
            glwes: from_fn(|i| self.glwes[i].ntt_forward()),
        }
    }

    pub fn dummy_ct() -> Self {
        Glev {
            glwes: from_fn(|_| Glwe::dummy_ct()),
        }
    }

    pub fn flatten(&self) -> Vec<F> {
        self.glwes.iter().flat_map(|glwe| glwe.flatten()).collect()
    }
}
