#![deny(clippy::pedantic)]
pub use permutation::Permutation;
use std::cmp::{min, Ordering};
use std::iter::repeat;
use std::iter::zip;
#[derive(Clone, PartialEq)]
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

    /// Converts a bitvector into a packaged `ControlBits` representation, checking its validity
    /// against a specified size.
    ///
    /// # Panics
    ///
    /// Panics if `exp` is not compatible with the size of bv.
    pub fn from_bits<V>(bv: V, exp: usize) -> ControlBits
    where
        V: Into<Vec<bool>>,
    {
        let bits = bv.into();
        let result = ControlBits { exp, bits };
        assert!(result.valid());

        result
    }

    #[must_use]
    pub fn inverse(&self) -> ControlBits {
        let exp = self.exp;
        let mut bits = Vec::new();
        for chunk in self.bits.rchunks(1 << (exp - 1)) {
            bits.extend(chunk);
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
        for (ch, gap) in self.bits.rchunks(1 << (m - 1)).zip(gaps) {
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

    #[must_use]
    pub fn interleve(&self, c: &ControlBits) -> Option<ControlBits> {
        (self.exp == c.exp).then_some({
            let bits = self
                .bits
                .iter()
                .zip(c.bits.iter())
                .flat_map(|(&a, &b)| [a, b])
                .collect();
            let exp = self.exp + 1;
            ControlBits { exp, bits }
        })
    }
}

impl IntoIterator for ControlBits {
    type Item = bool;
    type IntoIter = std::vec::IntoIter<Self::Item>;

    fn into_iter(self) -> Self::IntoIter {
        self.bits.into_iter()
    }
}

impl From<&ControlBits> for Permutation {
    fn from(cb: &ControlBits) -> Permutation {
        let m = cb.exp;
        let pi: Vec<_> = (0..(1 << m)).collect();
        let v = cb.apply_slice(pi);
        Permutation::oneline(v)
    }
}

fn get_permutation_exponent(pi: &Permutation) -> Option<usize> {
    let n = pi.len();
    n.is_power_of_two().then_some(n.trailing_zeros() as usize)
}

fn x_if<V: IntoIterator<Item = bool>>(bv: V) -> Permutation
where
{
    let indices: Vec<_> = bv
        .into_iter()
        .enumerate()
        .flat_map(|(i, b)| {
            let n = i << 1;
            let m = n + 1;
            if b {
                [m, n]
            } else {
                [n, m]
            }
        })
        .collect();
    Permutation::oneline(indices)
}

fn xor_perm(half_len: usize) -> Permutation {
    let bits = repeat(false).take(half_len);
    x_if(bits)
}

type FlmDecomp = (Vec<bool>, Permutation, Vec<bool>);

fn flm_decomp(pi: &Permutation) -> FlmDecomp {
    let m = get_permutation_exponent(pi).unwrap();
    if m == 0 {
        (vec![], Permutation::oneline([0]), vec![])
    } else {
        let c = {
            let pi_inv = &pi.clone().inverse();
            let xor = &xor_perm(1 << (m - 1));
            let mut c: Vec<usize> = (0..(1 << m)).collect();
            let mut pow_pibar = &(pi * xor) * &(pi_inv * xor);
            for _ in 0..m {
                let cp = pow_pibar.apply_slice(&c);
                c = zip(c, cp).map(|(a, b)| min(a, b)).collect();
                pow_pibar = &pow_pibar * &pow_pibar;
            }
            c
        };
        let f: Vec<_> = (0..(1 << (m - 1))).map(|x| c[2 * x] % 2 == 1).collect();
        let f_bits = f.clone();
        let f_perm = &x_if(f);
        let f_perm_pi = &(f_perm * pi);
        let l: Vec<_> = (0..(1 << (m - 1)))
            .map(|x| f_perm_pi.apply_idx(2 * x) % 2 == 1)
            .collect();
        let l_bits = l.clone();
        let l_perm = &x_if(l);
        let m_perm = f_perm_pi * l_perm;
        (f_bits, m_perm, l_bits)
    }
}

fn controlbits_stack(pi_init: &Permutation) -> ControlBits {
    let m_init = get_permutation_exponent(pi_init).unwrap();
    let mut control_bits: Vec<bool> = Vec::with_capacity((2 * m_init - 1) << (m_init - 1));
    control_bits.resize((2 * m_init - 1) << (m_init - 1), false);
    let mut stack: Vec<(usize, Permutation)> = vec![(0, pi_init.clone())];
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
    ControlBits::from_bits(control_bits, m_init)
}

#[must_use]
fn controlbits_recur(pi: &Permutation) -> ControlBits {
    let m = get_permutation_exponent(pi).unwrap();
    match m.cmp(&1) {
        Ordering::Less => ControlBits::from_bits([], 0),
        Ordering::Equal => ControlBits::from_bits([pi.apply_idx(0) != 0], 1),
        Ordering::Greater => {
            let (first_bits, middle_perm, last_bits) = flm_decomp(pi);
            let even_perm = Permutation::oneline(
                (0..1 << m)
                    .step_by(2)
                    .map(|x| middle_perm.apply_idx(x) >> 1)
                    .collect::<Vec<_>>(),
            );
            let even_bits = controlbits_recur(&even_perm);
            let odd_perm = Permutation::oneline(
                (0..1 << m)
                    .skip(1)
                    .step_by(2)
                    .map(|x| middle_perm.apply_idx(x) >> 1)
                    .collect::<Vec<usize>>(),
            );
            let odd_bits = controlbits_recur(&odd_perm);
            let middle_bits = even_bits.interleve(&odd_bits).unwrap();
            let bits: Vec<_> = first_bits
                .into_iter()
                .chain(middle_bits)
                .chain(last_bits)
                .collect();
            ControlBits::from_bits(bits, m)
        }
    }
}

#[must_use]
pub fn controlbits(pi_init: &Permutation) -> ControlBits {
    controlbits_recur(pi_init)
}

fn main() {
    let c1 = ControlBits::from_bits([false, false, true, false, true, false], 2);
    assert!(c1 == controlbits(&Permutation::from(&c1)));
    let p1 = Permutation::oneline([2, 3, 1, 0]);
    assert!(p1 == (&controlbits(&p1)).into());
    let c2 = c1.inverse();
    assert!(Permutation::one(4) == &Permutation::from(&c1) * &Permutation::from(&c2));
    assert!(Permutation::one(3) == Permutation::oneline([0, 1, 2, 4, 3]));
    assert!(controlbits_recur(&p1) == controlbits_stack(&p1));
}
