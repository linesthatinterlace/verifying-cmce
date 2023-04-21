//#![deny(clippy::pedantic)]
pub use permutation::Permutation;
use std::cmp::{min, Ordering};
use std::iter::zip;

#[derive(Clone)]
pub struct ControlBits {
    exp: usize,
    bits: Vec<bool>,
}

impl ControlBits {
    #[must_use]
    pub fn valid(&self) -> bool {
        let len = self.bits.len();
        let exp = self.exp;
        (exp == 0 && len == 0) || len == (2 * exp - 1) << (exp - 1)
    }

    pub fn from_bits<V>(bv: V) -> ControlBits
    where
        V: Into<Vec<bool>>,
    {
        let bits = bv.into();
        let len = bits.len();
        let exp = (0..).find(|&exp| (2 * exp + 1) << exp > len).unwrap_or(0);
        let result = ControlBits { exp, bits };
        debug_assert!(result.valid());

        result
    }
    #[must_use]
    pub fn inverse(&self) -> ControlBits {
        let exp = self.exp;
        let mut bits = Vec::new();
        for chunk in self.bits.chunks(1 << (exp - 1)).rev() {
            bits.extend_from_slice(chunk);
        }
        ControlBits { exp, bits }
    }

    pub fn apply_slice_in_place<T>(&self, a: &mut [T]) {
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

    pub fn apply_inv_slice_in_place<T>(&self, a: &mut [T]) {
        let m = self.exp;
        let gaps = (0..m).chain((0..(m - 1)).rev());
        for (ch, gap) in self.bits.chunks(1 << (m - 1)).rev().zip(gaps) {
            for (j, &b) in ch.iter().enumerate() {
                if b {
                    let pos: usize = j + ((j >> gap) << gap);
                    a.swap(pos, pos + (1 << gap));
                }
            }
        }
    }

    pub fn apply_slice<T: Clone, S>(&self, slice: S) -> Vec<T>
    where
        S: AsRef<[T]>,
    {
        let s = slice.as_ref();
        let mut result: Vec<T> = s.to_vec();
        self.apply_slice_in_place(&mut result);
        result
    }

    pub fn apply_slice_inv<T: Clone, S>(&self, slice: S) -> Vec<T>
    where
        S: AsRef<[T]>,
    {
        let s = slice.as_ref();
        let mut result: Vec<T> = s.to_vec();
        self.apply_inv_slice_in_place(&mut result);
        result
    }

    pub fn interleve(&self, c: &ControlBits) -> ControlBits {
        let bits = self
            .bits
            .iter()
            .zip(c.bits.clone())
            .flat_map(|(&a, b)| [a, b])
            .collect();
        let exp = min(self.exp, c.exp) + 1;
        ControlBits { exp, bits }
    }
}

impl IntoIterator for ControlBits {
    type Item = bool;
    type IntoIter = std::vec::IntoIter<Self::Item>;

    fn into_iter(self) -> Self::IntoIter {
        self.bits.into_iter()
    }
}

fn permutation(c: &ControlBits) -> Permutation {
    let m = c.exp;
    let mut pi: Vec<_> = (0..(1 << m)).collect();
    c.apply_slice_in_place(&mut pi);
    Permutation::oneline(pi)
}

fn get_permutation_exponent(pi: &Permutation) -> Option<usize> {
    let n = pi.len();
    n.is_power_of_two().then_some(n.trailing_zeros() as usize)
}

fn xor_perm(half_len: usize) -> Permutation {
    let indices: Vec<_> = (0..half_len)
        .flat_map(|i| {
            let n = i << 1;
            [n + 1, n]
        })
        .collect();
    Permutation::oneline(indices)
}

fn cyclemin_pibar(pi: Permutation) -> Vec<usize> {
    let pi = pi.normalize(true);
    let m = get_permutation_exponent(&pi).unwrap();
    let xor = xor_perm(1 << (m - 1));
    let mut c: Vec<usize> = (0..(1 << m)).collect();
    let mut pow_pibar = &(&pi * &xor) * &(&pi.inverse() * &xor);
    for _ in 0..m {
        let cp = pow_pibar.apply_slice(&c);
        c = zip(c, cp).map(|(a, b)| min(a, b)).collect();
        pow_pibar = &pow_pibar * &pow_pibar;
    }
    c
}

fn x_if<V>(bv: V) -> Permutation
where
    V: IntoIterator<Item = bool>,
{
    let indices: Vec<_> = bv
        .into_iter()
        .enumerate()
        .flat_map(|(i, b)| {
            let n = i << 1;
            if b {
                [n + 1, n]
            } else {
                [n, n + 1]
            }
        })
        .collect();
    Permutation::oneline(indices)
}

type FlmDecomp = (Vec<bool>, Permutation, Vec<bool>);

fn flm_decomp(pi: &Permutation) -> FlmDecomp {
    let m = get_permutation_exponent(pi).unwrap();
    let c = cyclemin_pibar(pi.clone());
    let f: Vec<_> = (0..(1 << (m - 1))).map(|x| c[2 * x] % 2 == 1).collect();
    let f_result = f.clone();
    let f_perm = x_if(f);
    let f_perm_pi = &f_perm * pi;
    let l: Vec<_> = (0..(1 << (m - 1)))
        .map(|x| f_perm_pi.apply_idx(2 * x) % 2 == 1)
        .collect();
    let l_result = l.clone();
    let l_perm = x_if(l);
    let m_perm = &f_perm_pi * &l_perm;
    (f_result, m_perm, l_result)
}

/*
#[must_use]
fn controlbits_stack(pi_init: Permutation) -> ControlBits {
    let m_init = get_permutation_exponent(&pi_init).unwrap();
    let mut control_bits: Vec<bool> = Vec::with_capacity((2 * m_init - 1) << (m_init - 1));
    control_bits.resize((2 * m_init - 1) << (m_init - 1), false);
    let mut stack: Vec<(usize, Permutation)> = vec![(0, pi_init)];
    while let Some((pos, pi_curr)) = stack.pop() {
        let m_curr = get_permutation_exponent(&pi_curr).unwrap();
        if 0 < m_curr {
            let (first_bits, middle_perm, last_bits) = flm_decomp(&pi_curr);
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
            let indices = (0..1 << m_curr).map(|i| middle_perm.apply_idx(i));
            let even_indices: Vec<usize> = indices.clone().step_by(2).map(|x| x >> 1).collect();
            let odd_indices: Vec<usize> = indices.skip(1).step_by(2).map(|x| x >> 1).collect();
            let even_perm = Permutation::oneline(even_indices);
            let odd_perm = Permutation::oneline(odd_indices);
            stack.push((pos + (1 << (m_init - 1)), even_perm));
            stack.push((
                pos + (1 << (m_init - 1)) + (1 << (m_init - m_curr)),
                odd_perm,
            ));
        }
    }
    ControlBits::from_bits(control_bits)
}
 */
#[must_use]
fn controlbits_recur(pi: Permutation) -> ControlBits {
    let pi = pi.normalize(false);
    let m = get_permutation_exponent(&pi).unwrap();
    match m.cmp(&1) {
        Ordering::Less => ControlBits::from_bits(vec![]),
        Ordering::Equal => ControlBits::from_bits(vec![pi.apply_idx(0) != 0]),
        Ordering::Greater => {
            let (first_bits, middle_perm, last_bits) = flm_decomp(&pi);
            let middle_perm = middle_perm.normalize(false);
            let even_indices = (0..1 << m)
                .step_by(2)
                .map(|x| middle_perm.apply_idx(x) >> 1);
            let odd_indices = (0..1 << m)
                .skip(1)
                .step_by(2)
                .map(|x| middle_perm.apply_idx(x) >> 1);
            let even_perm = Permutation::oneline(even_indices.collect::<Vec<usize>>());
            let odd_perm = Permutation::oneline(odd_indices.collect::<Vec<usize>>());
            let middle_bits = controlbits_recur(even_perm)
                .into_iter()
                .zip(controlbits_recur(odd_perm))
                .flat_map(|(a, b)| [a, b]);
            let bits: Vec<_> = first_bits
                .into_iter()
                .chain(middle_bits)
                .chain(last_bits)
                .collect();
            ControlBits::from_bits(bits)
        }
    }
}

pub fn controlbits(pi_init: Permutation) -> ControlBits {
    controlbits_recur(pi_init)
}

fn main() {
    let c1 = ControlBits::from_bits(vec![false, false, true, false, true, false]);
    //println!("c1: {c1:?}");
    let c2 = controlbits(permutation(&c1));

    //println!("c2: {c2:?}");

    let p1 = Permutation::oneline(vec![2, 3, 1, 0]);
    //println!("p1: {p1:?}");
    let p2 = permutation(&controlbits(p1));
    //println!("p2: {p2:?}");
}
