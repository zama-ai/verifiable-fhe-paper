use plonky2::{field::extension::Extendable, hash::hash_types::RichField, util::log2_ceil};
use rand_distr::{Distribution, Normal};

pub fn inner_product<F: RichField + Extendable<D>, const D: usize>(left: &[F], right: &[F]) -> F {
    left.iter()
        .zip(right.iter())
        .fold(F::ZERO, |acc, (li, ri)| acc + (*li * *ri))
}

pub fn key_gen<F: RichField + Extendable<D>, const D: usize, const n: usize>() -> Vec<F> {
    (0..n)
        .map(|_| F::from_canonical_u64(rand::random::<u64>() % 2))
        .collect()
}

pub fn get_error<F: RichField + Extendable<D>, const D: usize, const n: usize>(
    ct: &[F],
    s: &[F],
    m: F,
) -> f64 {
    let mbar = decrypt::<F, D, n>(s, ct);
    let m64 = m.to_canonical_u64();
    let mbar64 = mbar.to_canonical_u64();
    let error = (m64.max(mbar64) - m64.min(mbar64)) as f64;
    error / (F::ORDER as f64)
}

pub fn mod_switch_element<F: RichField + Extendable<D>, const D: usize>(element: F, p: usize) -> usize{
    let mut shift = element.to_canonical_u64() as usize;
    shift >>= F::BITS - log2_ceil(p) - 2;
    let carry = shift % 2;
    shift >>= 1;
    shift + carry
}

pub fn mod_switch_ct<F: RichField + Extendable<D>, const D: usize>(ct: &[F], p: usize) -> Vec<usize> {
    ct.iter().map(|element| mod_switch_element(*element, p)).collect()
}

pub fn error_sample<F: RichField + Extendable<D>, const D: usize>(sigma: f64) -> F {
    let q = F::ORDER as f64;
    let normal = Normal::new(0.0, sigma * q).unwrap();
    F::from_noncanonical_i64(normal.sample(&mut rand::thread_rng()).round() as i64)
}

pub fn get_delta<F: RichField + Extendable<D>, const D: usize>(p: usize) -> F {
    F::from_noncanonical_biguint(F::order() >> log2_ceil(p))
}

pub fn encrypt<F: RichField + Extendable<D>, const D: usize, const n: usize>(
    s: &[F],
    m: &F,
    sigma: f64,
) -> Vec<F> {
    let mut mask: Vec<F> = (0..n).map(|_| F::rand()).collect();
    let body = inner_product(s, &mask) + *m + error_sample(sigma);
    mask.push(body);
    mask
}

// noisy decryption
pub fn decrypt<F: RichField + Extendable<D>, const D: usize, const n: usize>(
    s: &[F],
    ct: &[F],
) -> F {
    let mut mask = ct.to_vec();
    let body = mask.pop().unwrap();
    body - inner_product(s, &mask)
}

pub fn multiply_constant<F: RichField + Extendable<D>, const D: usize>(c: &[F], k: &F) -> Vec<F> {
    c.iter().map(|c| *c * *k).collect()
}

pub fn add<F: RichField + Extendable<D>, const D: usize>(left: &[F], right: &[F]) -> Vec<F> {
    left.iter().zip(right).map(|(l, r)| *l + *r).collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use plonky2::field::goldilocks_field::GoldilocksField;
    use plonky2::field::types::{Field, PrimeField64};
    use rand::random;

    #[test]
    fn test_lwe_ct() {
        const n: usize = 722;
        const D: usize = 2;
        type F = GoldilocksField;
        let sigma = 0.000013071021089943935;
        let p = 4;
        let delta = get_delta::<F, D>(p);

        let s = key_gen::<F, D, n>();
        let m1 = F::from_canonical_usize(random::<usize>() % p);
        let m2 = F::from_canonical_usize(random::<usize>() % p);

        let c1 = encrypt::<F, D, n>(&s, &(delta * m1), sigma);
        let c2 = encrypt::<F, D, n>(&s, &(delta * m2), sigma);

        println!("error 1: {}", get_error::<F, D, n>(&c1, &s, delta * m1));
        println!("error 2: {}", get_error::<F, D, n>(&c2, &s, delta * m2));

        let c: Vec<F> = c1
            .into_iter()
            .zip(c2.into_iter())
            .map(|(x, y)| x + y)
            .collect();

        println!(
            "error out: {}",
            get_error::<F, D, n>(&c, &s, delta * (m1 + m2))
        );

        let m_noisy = decrypt::<F, D, n>(&s, &c);
        let m =
            (m_noisy.to_canonical_u64() as f64 / delta.to_canonical_u64() as f64).round() as usize % p;
        assert_eq!(m as u64, (m1 + m2).to_canonical_u64() % p as u64);
    }
}
