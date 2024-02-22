use rand_distr::{Distribution, Normal};
use std::array::from_fn;

use plonky2::{field::extension::Extendable, hash::hash_types::RichField};

use crate::ntt::params;

use super::lwe::error_sample;

fn ntt_fw_update<F: RichField + Extendable<D>, const D: usize>(input: &[F], m: usize) -> Vec<F> {
    let mut a = input.to_vec();
    let t = params::N / (2 * m);
    for i in 0..m {
        let j1 = 2 * i * t;
        let j2 = j1 + t;
        let root = params::ROOTS[m + i];
        let s = F::from_canonical_u64(root);
        for j in j1..j2 {
            let u = a[j];
            let v = a[j + t] * s;
            a[j] = u + v;
            a[j + t] = u - v;
        }
    }
    a
}

pub fn ntt_forward<F: RichField + Extendable<D>, const D: usize>(input: &[F]) -> Vec<F> {
    let mut current = input.to_vec();
    for m in (0..params::LOGN).map(|i| 2usize.pow(i)) {
        current = ntt_fw_update(&current, m);
    }

    current
}

fn ntt_bw_update<F: RichField + Extendable<D>, const D: usize>(input: &[F], m: usize) -> Vec<F> {
    let mut a = input.to_vec();
    let t = params::N / (2 * m);
    let mut j1 = 0usize;
    for i in 0..m {
        let j2 = j1 + t;
        let root = params::INVROOTS[m + i];
        let s = F::from_canonical_u64(root);
        for j in j1..j2 {
            let u = a[j];
            let v = a[j + t];
            a[j] = u + v;
            let w = u - v;
            a[j + t] = w * s;
        }
        j1 += 2 * t;
    }
    a
}

pub fn ntt_backward<F: RichField + Extendable<D>, const D: usize>(input: &[F]) -> Vec<F> {
    let mut current = input.to_vec();
    for m in (0..params::LOGN).rev().map(|i| 2usize.pow(i)) {
        current = ntt_bw_update(&current, m);
    }

    let n_inv = F::from_canonical_u64(params::NINV);
    current.into_iter().map(|g| g * n_inv).collect()
}

#[derive(Debug, PartialEq, Clone)]
pub struct Poly<F: RichField + Extendable<D>, const D: usize, const N: usize> {
    pub coeffs: [F; N],
}

impl<F: RichField + Extendable<D>, const D: usize, const N: usize> Poly<F, D, N> {
    pub fn rand() -> Self {
        Poly {
            coeffs: from_fn(|_| F::rand()),
        }
    }

    pub fn rand_bin() -> Self {
        Poly {
            coeffs: from_fn(|_| F::from_canonical_u64(rand::random::<u64>() % 2)),
        }
    }

    pub fn rand_error(sigma: f64) -> Self {
        Poly {
            coeffs: from_fn(|_| error_sample(sigma)),
        }
    }

    pub fn constant(m: &F) -> Self {
        let mut pol = Poly {
            coeffs: from_fn(|_| F::ZERO),
        };
        pol.coeffs[0] = *m;
        pol
    }

    pub fn from_slice(m: &[F]) -> Self {
        Poly {
            coeffs: from_fn(|i| m[i]),
        }
    }

    pub fn add(&self, other: &Poly<F, D, N>) -> Self {
        let range: [usize; N] = core::array::from_fn(|i| i);
        Poly {
            coeffs: range.map(|i| self.coeffs[i] + other.coeffs[i]),
        }
    }

    pub fn scalar_mul(&self, scalar: &F) -> Self {
        let range: [usize; N] = core::array::from_fn(|i| i);
        Poly {
            coeffs: range.map(|i| *scalar * self.coeffs[i]),
        }
    }

    pub fn sub(&self, other: &Poly<F, D, N>) -> Self {
        let range: [usize; N] = core::array::from_fn(|i| i);
        Poly {
            coeffs: range.map(|i| self.coeffs[i] - other.coeffs[i]),
        }
    }

    pub fn ntt_fw(&self) -> Self {
        assert_eq!(N, params::N);
        Poly {
            coeffs: ntt_forward(&self.coeffs).try_into().unwrap(),
        }
    }

    pub fn ntt_bw(&self) -> Self {
        assert_eq!(N, params::N);
        Poly {
            coeffs: ntt_backward(&self.coeffs).try_into().unwrap(),
        }
    }

    pub fn pointwise_mul(&self, other: &Poly<F, D, N>) -> Self {
        let range: [usize; N] = core::array::from_fn(|i| i);
        Poly {
            coeffs: range.map(|i| self.coeffs[i] * other.coeffs[i]),
        }
    }

    pub fn mul(&self, other: &Poly<F, D, N>) -> Self {
        let self_hat = self.ntt_fw();
        let other_hat = other.ntt_fw();
        self_hat.pointwise_mul(&other_hat).ntt_bw()
    }

    fn reduce_shift(&self, shift: usize) -> (Self, usize) {
        if shift < N {
            (self.clone(), shift)
        } else {
            (self.scalar_mul(&(-F::ONE)), shift % N)
        }
    }
    
    pub fn left_shift(&self, shift: usize) -> Self {
        let (poly, reduced_shift) = self.reduce_shift(shift);
        Poly {
            coeffs: from_fn(|i| {
                if i < N - reduced_shift {
                    poly.coeffs[i + reduced_shift]
                } else {
                    -poly.coeffs[i - N + reduced_shift]
                }
            }),
        }
    }

    pub fn right_shift(&self, shift: usize) -> Self {
        let (poly, reduced_shift) = self.reduce_shift(shift);
        Poly {
            coeffs: from_fn(|i| {
                if i < reduced_shift {
                    -poly.coeffs[N - reduced_shift + i]
                } else {
                    poly.coeffs[i - reduced_shift]
                }
            }),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ntt::params::{N, TESTG, TESTGHAT};
    use plonky2::field::goldilocks_field::GoldilocksField;
    use plonky2::field::types::{Field, PrimeField64, Sample};

    #[test]
    fn test_ntt() {
        const D: usize = 2;
        type F = GoldilocksField;
        let test = Poly::<F, D, N> {
            coeffs: TESTG.map(|x| F::from_canonical_u64(x)),
        };

        let test_hat = Poly::<F, D, N> {
            coeffs: TESTGHAT.map(|x| F::from_canonical_u64(x)),
        };

        assert_eq!(test.ntt_fw().coeffs, test_hat.coeffs);
        assert_eq!(test_hat.ntt_bw().coeffs, test.coeffs);
    }
}
