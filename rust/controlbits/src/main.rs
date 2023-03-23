#![deny(clippy::pedantic)]
#![allow(clippy::many_single_char_names)]
#![allow(clippy::must_use_candidate)]
use permutation::Permutation;
use simple_error::SimpleError;
use std::cmp::min;
use std::iter::zip;

fn cb_exp(l: usize) -> usize {
    if l == 0 {
        0
    } else {
        let mut m = 1;
        while (2 * m - 1) << (m - 1) < l {
            m += 1;
        }
        m
    }
}

fn checked_cb_exp(l: usize) -> Option<usize> {
    let m = cb_exp(l);
    ((m != 0) && ((2 * m - 1) << (m - 1) == l)).then_some(m)
}

#[derive(Clone, Debug)]
pub struct ControlBits {
    exp: usize,
    bits: Vec<bool>,
}

impl ControlBits {
    pub fn len(&self) -> usize {
        self.bits.len()
    }
    pub fn valid(&self) -> bool {
        let m = self.exp;
        (2 * m - 1) << (m - 1) == self.len()
    }

    pub fn checked_mk_bits(bits: Vec<bool>) -> Option<ControlBits> {
        let l = bits.len();
        let exp = checked_cb_exp(l)?;
        Some(ControlBits { exp, bits })
    }

    pub fn apply_slice<T>(&self, a: &mut [T]) {
        let m = self.exp;
        let gaps = (0..m).chain((0..(m - 1)).rev());
        for (ch, gap) in self.bits.chunks(1 << (m - 1)).zip(gaps) {
            for (j, &b) in ch.iter().enumerate() {
                if b {
                    let pos: usize = j + ((j >> gap) << gap);
                    a.swap(pos, pos + (1 << gap));
                }
            }
        }
    }
}

fn perm_exp(n: usize) -> usize {
    n.trailing_zeros() as usize
}

fn checked_perm_exp(n: usize) -> Option<usize> {
    (n.count_ones() == 1).then_some(n.trailing_zeros() as usize)
}

fn get_permutation_exponent(pi: Permutation) -> Option<usize> {
    let n = pi.len();
    checked_perm_exp(n)
}

fn permutation(c: ControlBits) -> Permutation {
    let m = get_controlbits_exponent(c)?;
    let mut pi: Vec<_> = (0..(1 << m)).collect();
    permute_using(&mut pi, c)?;
    Ok(pi)
}

fn composeinv<T: Copy>(c: &[T], pi: &[usize]) -> Result<Vec<T>, SimpleError> {
    let n = get_permutation_length(pi)?;
    if n == c.len() {
        let mut s: Vec<_> = pi.iter().zip(c.iter()).collect();
        s.sort_unstable_by_key(|(&a, _)| a);
        let k: Vec<T> = s.into_iter().map(|(_, &b)| b).collect();
        Ok(k)
    } else {
        Err(SimpleError::new(
            "Permutation length does not match length of permuted vector",
        ))
    }
}

fn permute_ind_nct<T: Copy>(c: &[T], pi: &[usize]) -> Result<Vec<T>, SimpleError> {
    let n = get_permutation_length(pi)?;
    if n != c.len() {
        return Err(SimpleError::new(
            "Permutation length does not match length of permuted vector",
        ));
    }

    let s: Vec<T> = pi.iter().map(|&i| c[i]).collect();
    Ok(s)
}

fn inverse_nct(pi: &[usize]) -> Vec<usize> {
    let mut s = vec![0; pi.len()];
    for (i, &p) in pi.iter().enumerate() {
        s[p] = i;
    }
    s
}

fn permute_inv_ind_nct<T: Copy>(c: &[T], pi: &[usize]) -> Result<Vec<T>, SimpleError> {
    let n = get_permutation_length(pi)?;
    if n != c.len() {
        return Err(SimpleError::new(
            "Permutation length does not match length of permuted vector",
        ));
    }
    let piinv = inverse_nct(pi);
    permute_ind_nct(c, &piinv)
}

fn cyclemin_pibar(pi: &[usize]) -> Result<Vec<usize>, SimpleError> {
    let m = get_permutation_exponent(pi)?;
    let mut pi_xor = pi.to_vec();
    for pair in pi_xor.chunks_exact_mut(2) {
        pair.swap(0, 1);
    }
    let mut xor_pi: Vec<_> = pi.iter().map(|&x| x ^ 1).collect();
    let mut c: Vec<_> = (0..(1 << m)).collect();

    for _ in 0..m {
        let pi_xor_copy = composeinv(&pi_xor, &xor_pi)?;
        xor_pi = composeinv(&xor_pi, &pi_xor)?;
        pi_xor = pi_xor_copy;
        let cp = composeinv(&c, &xor_pi)?;
        c = zip(c, cp).map(|(a, b)| min(a, b)).collect();
    }
    Ok(c)
}

fn x_if(bits: &[bool]) -> Vec<usize> {
    let n = 2 * bits.len();
    (0..n)
        .map(|x| if bits[x >> 1] { x ^ 1 } else { x })
        .collect()
}

type FlmDecomp = (Vec<bool>, Vec<usize>, Vec<bool>);

fn flm_decomp(pi: &[usize]) -> Result<FlmDecomp, SimpleError> {
    let m = get_permutation_exponent(pi)?;
    let c = cyclemin_pibar(pi)?;
    let f: Vec<_> = (0..(1 << (m - 1))).map(|x| c[2 * x] % 2 == 1).collect();
    let f_perm = x_if(&f);
    let piinv = composeinv(&(0..(1 << m)).collect::<Vec<_>>(), pi)?;
    let f_perm_pi = composeinv(&f_perm, &piinv)?;
    let l: Vec<_> = (0..(1 << (m - 1)))
        .map(|x| f_perm_pi[2 * x] % 2 == 1)
        .collect();
    let l_perm = x_if(&l);
    let m_perm = composeinv(&f_perm_pi, &l_perm)?;
    Ok((f, m_perm, l))
}

fn controlbits(pi_init: &[usize]) -> Result<Vec<bool>, SimpleError> {
    let m_init = get_permutation_exponent(pi_init)?;
    let mut control_bits: Vec<bool> = Vec::with_capacity((2 * m_init - 1) << (m_init - 1));
    control_bits.resize((2 * m_init - 1) << (m_init - 1), false);
    let mut stack: Vec<(usize, Vec<usize>)> = vec![(0, pi_init.to_vec())];
    while let Some((pos, pi_curr)) = stack.pop() {
        let m_curr = get_permutation_exponent(&pi_curr)?;
        if 0 < m_curr {
            let (first_bits, middle_perm, last_bits) = flm_decomp(&pi_curr)?;
            control_bits
                .iter_mut()
                .skip(pos)
                .step_by(1 << (m_init - m_curr))
                .take(1 << (m_curr - 1))
                .zip(first_bits.iter())
                .for_each(|(a, &b)| *a = b);
            control_bits
                .iter_mut()
                .skip(pos + ((m_curr - 1) << m_init))
                .step_by(1 << (m_init - m_curr))
                .take(1 << (m_curr - 1))
                .zip(last_bits.iter())
                .for_each(|(a, &b)| *a = b);
            let even_perm: Vec<usize> = middle_perm.iter().step_by(2).map(|&x| x >> 1).collect();
            let odd_perm: Vec<usize> = middle_perm
                .iter()
                .skip(1)
                .step_by(2)
                .map(|&x| x >> 1)
                .collect();
            stack.push((pos + (1 << (m_init - 1)), even_perm));
            stack.push((
                pos + (1 << (m_init - 1)) + (1 << (m_init - m_curr)),
                odd_perm,
            ));
        }
    }
    Ok(control_bits)
}
#[allow(clippy::unreadable_literal)]
fn main() {
    let pi = vec![2, 3, 1, 0];
    println!("{pi:?}");
    if let Ok(c) = controlbits(&pi) {
        println!("{c:?}");
        if let Ok(p2) = permutation(&c) {
            println!("{p2:?}");
        }
    }
    let pi = vec![7, 13, 0, 2, 12, 1, 3, 14, 4, 10, 11, 5, 15, 6, 8, 9];
    println!("{pi:?}");
    if let Ok(c) = controlbits(&pi) {
        println!("{c:?}");
        if let Ok(p2) = permutation(&c) {
            println!("{p2:?}");
        }
    }
}

#[cfg(kani)]
#[kani::proof]
fn check_estimate_size() {
    let c: [usize; 10] = kani::any();
    let pi: [usize; 10] = kani::any();
    if let (Ok(v), Ok(v2)) = (composeinv(&c, &pi), permute_inv_ind_nct(&c, &pi)) {
        for i in 0..10 {
            assert!(v[i] == v2[i]);
        }
    }
}
