use itertools::max;
use plonky2::{field::extension::Extendable, hash::hash_types::RichField};
use std::array::from_fn;

use super::poly::Poly;

#[derive(Debug, PartialEq)]
pub struct Glwe<F: RichField + Extendable<D>, const D: usize, const N: usize, const K: usize> {
    pub polys: [Poly<F, D, N>; K],
}

impl<F: RichField + Extendable<D>, const D: usize, const N: usize, const K: usize>
    Glwe<F, D, N, K>
{
    pub fn key_gen() -> Vec<Poly<F, D, N>> {
        (0..K - 1).map(|_| Poly::rand_bin()).collect()
    }

    pub fn partial_key(nz: usize) -> Vec<Poly<F, D, N>> {
        let mut key = Vec::new();
        for _ in 0..(nz / N).min(K) {
            key.push(Poly::rand_bin());
        }

        if nz / N < K {
            let mut poly = Poly::rand_bin();
            for i in nz % N..N {
                poly.coeffs[i] = F::ZERO;
            }
            key.push(poly);

            for _ in nz / N + 1..K {
                key.push(Poly::constant(&F::ZERO));
            }
        }

        key
    }

    fn poly_inner(s: &[Poly<F, D, N>], a: &[Poly<F, D, N>]) -> Poly<F, D, N> {
        a.iter()
            .zip(s.iter())
            .map(|(ai, si)| ai.mul(si))
            .reduce(|acc, x| acc.add(&x))
            .unwrap()
    }

    // noiseless
    pub fn encrypt(s: &[Poly<F, D, N>], m: &Poly<F, D, N>, sigma: f64) -> Self {
        let mut mask: Vec<Poly<F, D, N>> = (0..K - 1).map(|_| Poly::rand()).collect();
        let error = Poly::rand_error(sigma);
        let body = Glwe::<F, D, N, K>::poly_inner(s, &mask).add(&error);
        mask.push(body.add(m));
        Glwe {
            polys: mask.try_into().unwrap(),
        }
    }

    // noisy decryption
    pub fn decrypt(&self, s: &[Poly<F, D, N>]) -> Poly<F, D, N> {
        let mask = Glwe::<F, D, N, K>::poly_inner(s, &self.polys[0..K - 1]);
        self.polys[K - 1].sub(&mask)
    }

    pub fn get_max_error(&self, s: &[Poly<F, D, N>], m: &Poly<F, D, N>) -> f64 {
        let mbar = self.decrypt(s);
        let errors = m
            .coeffs
            .iter()
            .zip(mbar.coeffs.iter())
            .map(|(left, right)| {
                let left64 = left.to_canonical_u64();
                let right64 = right.to_canonical_u64();
                let diff = left64.max(right64) - left64.min(right64);
                diff.min(F::ORDER - diff)
            });
        (max(errors).unwrap() as f64) / (F::ORDER as f64)
    }

    pub fn get_avg_error(&self, s: &[Poly<F, D, N>], m: &Poly<F, D, N>) -> f64 {
        let mbar = self.decrypt(s);
        // let errors =
        (m.coeffs
            .iter()
            .zip(mbar.coeffs.iter())
            .map(|(left, right)| {
                let left64 = left.to_canonical_u64();
                let right64 = right.to_canonical_u64();
                let diff = left64.max(right64) - left64.min(right64);
                diff.min(F::ORDER - diff)
            })
            .sum::<u64>() as f64)
            / ((F::ORDER as f64) * (N as f64))
    }

    pub fn sample_extract(&self) -> Vec<F> {
        let mut a = Vec::new();
        for poly in &self.polys[..K - 1] {
            a.push(poly.coeffs[0]);
            for ai in poly.coeffs[1..].iter().rev() {
                a.push(-*ai);
            }
        }
        a.push(self.polys[K - 1].coeffs[0]);
        a
    }

    pub fn partial_sample_extract(&self, nz: usize) -> Vec<F> {
        let full_sample = self.sample_extract();
        let mut mask = full_sample[..nz].to_vec();
        mask.push(*full_sample.last().unwrap());
        mask
    }

    pub fn from_slice(slice: &[F]) -> Self {
        Glwe {
            polys: from_fn(|i| Poly::from_slice(&slice[i * N..(i + 1) * N])),
        }
    }

    pub fn dummy_ct() -> Self {
        Glwe {
            polys: from_fn(|_| Poly::constant(&F::ZERO)),
        }
    }

    pub fn trivial_ct(m: Poly<F, D, N>) -> Self {
        let mut ct = Glwe::dummy_ct();
        ct.polys[K - 1] = m;
        ct
    }

    pub fn flatten(&self) -> Vec<F> {
        self.polys.iter().flat_map(|poly| poly.coeffs).collect()
    }

    pub fn flatten_key(s: &[Poly<F, D, N>]) -> Vec<F> {
        let mut s0 = Vec::new();
        for poly in s {
            s0.extend(poly.coeffs);
        }
        s0
    }

    pub fn flatten_partial_key(s: &[Poly<F, D, N>], nz: usize) -> Vec<F> {
        Glwe::<F, D, N, K>::flatten_key(&s)[..nz].to_vec()
    }

    pub fn ntt_forward(&self) -> Self {
        Glwe {
            polys: from_fn(|i| self.polys[i].ntt_fw()),
        }
    }

    pub fn ntt_backward(&self) -> Self {
        Glwe {
            polys: from_fn(|i| self.polys[i].ntt_bw()),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ntt::params::N;
    use crate::vtfhe::crypto::lwe::decrypt;
    use plonky2::field::goldilocks_field::GoldilocksField;

    #[test]
    fn test_glwe_ct() {
        const K: usize = 3;
        const D: usize = 2;
        const n: usize = (K - 1) * N;
        type F = GoldilocksField;

        let s = Glwe::<F, D, N, K>::key_gen();
        let m = Poly::<F, D, N>::rand();

        let c = Glwe::<F, D, N, K>::encrypt(&s, &m, 0f64);
        let m_ = c.decrypt(&s);
        assert_eq!(m, m_);

        let c0 = c.sample_extract();

        let s0 = Glwe::<F, D, N, K>::flatten_key(&s);

        let m0 = decrypt::<F, D, n>(&s0, &c0);
        assert_eq!(m0, m.coeffs[0]);

        let c = Glwe::<F, D, N, K>::encrypt(&s, &m, 0.00000004990272175010415);
        println!("max error: {}", c.get_max_error(&s, &m));
    }

    #[test]
    fn test_partial_key() {
        const K: usize = 3;
        const D: usize = 2;
        const n: usize = (K - 2) * N + N / 2;
        type F = GoldilocksField;

        let s = Glwe::<F, D, N, K>::partial_key(n);
        let m = Poly::<F, D, N>::rand();

        let c = Glwe::<F, D, N, K>::encrypt(&s, &m, 0f64);
        let m_ = c.decrypt(&s);
        assert_eq!(m, m_);

        let c0 = c.partial_sample_extract(n);

        let s0 = Glwe::<F, D, N, K>::flatten_partial_key(&s, n);

        let m0 = decrypt::<F, D, n>(&s0, &c0);
        assert_eq!(m0, m.coeffs[0]);
    }
}
