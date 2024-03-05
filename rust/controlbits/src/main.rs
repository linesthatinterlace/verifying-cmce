#![deny(clippy::pedantic)]
pub use permutation::Permutation;
use std::cmp::min;
use std::iter::repeat;
use std::iter::zip;
#[derive(Clone, Debug, PartialEq)]
pub struct ControlBits {
    layer: usize,
    bits: Vec<bool>,
}

fn add_bit(i: usize, b: bool, k: usize) -> usize {
    let top_bits = k >> i << i;

    (top_bits << 1) | usize::from(b) << i | (k ^ top_bits)
}

impl ControlBits {
    fn valid(&self) -> bool {
        let len = self.bits.len();
        let layer = self.layer;
        len == (2 * layer + 1) << layer
    }

    /// Converts a bitvector into a packaged `ControlBits` representation, checking its validity
    /// against a specified size.
    ///
    /// # Panics
    ///
    /// Panics if `layer` is not compatible with the size of bv.
    pub fn from_bits<V>(layer: usize, bv: V) -> ControlBits
    where
        V: IntoIterator<Item = bool>,
    {
        let bits = bv.into_iter().collect();
        let result = ControlBits { layer, bits };
        assert!(result.valid());

        result
    }

    #[must_use]
    pub fn inverse(&self) -> ControlBits {
        Self::from_bits(
            self.layer,
            self.bits
                .rchunks_exact(1 << self.layer)
                .flatten()
                .copied()
                .collect::<Vec<_>>(),
        )
    }

    pub fn apply_slice_in_place<T>(&self, a: &mut [T]) {
        let layer = self.layer;
        for (i, ch) in self.bits.chunks_exact(1 << layer).enumerate() {
            let gap = layer - layer.abs_diff(i);
            for (j, &b) in ch.iter().enumerate() {
                a.swap(add_bit(gap, false, j), add_bit(gap, b, j));
            }
        }
    }

    pub fn apply_inv_slice_in_place<T>(&self, a: &mut [T]) {
        let inv = self.inverse();
        inv.apply_slice_in_place(a);
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
        let m = cb.layer;
        let mut pi: Vec<_> = (0..2 << m).collect();
        cb.apply_slice_in_place(pi.as_mut());
        Permutation::oneline(pi)
    }
}

fn get_permutation_layer(pi: &Permutation) -> Option<usize> {
    let n = pi.len() >> 1;
    n.is_power_of_two().then_some(n.trailing_zeros() as usize)
}

fn x_if(bv: &[bool]) -> Permutation {
    let mut pi: Vec<_> = (0..2 * bv.len()).collect();
    for (j, &b) in bv.iter().enumerate() {
        pi.swap(add_bit(0, false, j), add_bit(0, b, j));
    }
    Permutation::oneline(pi)
}

fn xor_perm(half_len: usize) -> Permutation {
    let bits = repeat(true).take(half_len).collect::<Vec<_>>();
    x_if(&bits)
}

type FlmDecomp = (Vec<bool>, Permutation, Vec<bool>);

fn flm_decomp(m: usize, pi: &Permutation) -> FlmDecomp {
    assert!(pi.len() == 2 << m);
    let c = {
        let pi_inv = &pi.clone().inverse();
        let xor = &xor_perm(1 << m);
        let mut c: Vec<usize> = (0..(2 << m)).collect();
        let mut pow_pibar = &(pi * xor) * &(pi_inv * xor);
        for _ in 0..=m {
            let cp = pow_pibar.apply_slice(&c);
            c = zip(c, cp).map(|(a, b)| min(a, b)).collect();
            pow_pibar = &pow_pibar * &pow_pibar;
        }
        c
    };
    let f: Vec<_> = (0..(1 << m)).map(|x| c[2 * x] % 2 == 1).collect();
    let f_bits = f.clone();
    let f_perm = &x_if(&f);
    let f_perm_pi = &(f_perm * pi);
    let l: Vec<_> = (0..(1 << m))
        .map(|x| f_perm_pi.apply_idx(2 * x) % 2 == 1)
        .collect();
    let l_bits = l.clone();
    let l_perm = &x_if(&l);
    let m_perm = f_perm_pi * l_perm;
    (f_bits, m_perm, l_bits)
}

/*
fn controlbits_stack(m_init: usize, pi_init: &Permutation) -> ControlBits {
    assert!(pi_init.len() == 2 << m_init);

    let mut control_bits: Vec<bool> = Vec::with_capacity((2 * m_init + 1) << m_init);
    control_bits.resize((2 * m_init + 1) << m_init, false);
    let mut stack: Vec<(usize, usize, Permutation)> = vec![(m_init, 0, pi_init.clone())];
    while let Some((m_curr, pos, pi_curr)) = stack.pop() {
        let (first_bits, middle_perm, last_bits) = flm_decomp(m_curr, &pi_curr);
        control_bits
            .iter_mut()
            .skip(pos)
            .step_by(1 << (m_init - m_curr))
            .take(1 << m_curr)
            .zip(first_bits.iter())
            .for_each(|(a, &b)| *a = b);
        control_bits
            .iter_mut()
            .skip(pos + ((2 * m_curr) << m_init))
            .step_by(1 << (m_init - m_curr))
            .take(1 << m_curr)
            .zip(last_bits.iter())
            .for_each(|(a, &b)| *a = b);
        let indices = (0..2 << m_curr).map(|i| middle_perm.apply_idx(i));
        let even_indices: Vec<usize> = indices.clone().step_by(2).map(|x| x >> 1).collect();
        let odd_indices: Vec<usize> = indices.skip(1).step_by(2).map(|x| x >> 1).collect();
        let even_perm = Permutation::oneline(even_indices);
        let odd_perm = Permutation::oneline(odd_indices);
        if m_curr != 0 {
            stack.push((m_curr - 1, pos + (1 << m_init), even_perm));
            stack.push((
                m_curr - 1,
                pos + (1 << m_init) + (1 << (m_init - m_curr)),
                odd_perm,
            ));
        };
    }
    ControlBits::from_bits(m_init, control_bits)
}*/

fn controlbits_recur(m_init: usize, pi_init: &Permutation) -> ControlBits {
    assert!(pi_init.len() == 2 << m_init);

    let (first_bits, middle_perm, last_bits) = flm_decomp(m_init, pi_init);
    if m_init == 0 {
        ControlBits::from_bits(0, last_bits)
    } else {
        let even_perm = Permutation::oneline(
            (0..2 << m_init)
                .step_by(2)
                .map(|x| middle_perm.apply_idx(x) >> 1)
                .collect::<Vec<_>>(),
        );
        let odd_perm = Permutation::oneline(
            (0..2 << m_init)
                .skip(1)
                .step_by(2)
                .map(|x| middle_perm.apply_idx(x) >> 1)
                .collect::<Vec<usize>>(),
        );
        let even_bits = controlbits_recur(m_init - 1, &even_perm);
        let odd_bits = controlbits_recur(m_init - 1, &odd_perm);
        let middle_bits = zip(even_bits.bits, odd_bits.bits).flat_map(|(a, b)| [a, b]);
        let bits: Vec<_> = first_bits
            .into_iter()
            .chain(middle_bits)
            .chain(last_bits)
            .collect();
        ControlBits::from_bits(m_init, bits)
    }
}

#[must_use]
pub fn controlbits(pi_init: &Permutation) -> Option<ControlBits> {
    let m_init = get_permutation_layer(pi_init)?;
    Some(controlbits_recur(m_init, pi_init))
}

fn main() {
    let c1 = ControlBits::from_bits(1, [false, false, false, false, false, true]);
    assert!(c1 == controlbits(&Permutation::from(&c1)).unwrap());
    let p1 = Permutation::oneline([2, 3, 1, 0]);
    assert!(p1 == Permutation::from(&controlbits(&p1).unwrap()));
    //assert!(controlbits_recur(1, &p1) == controlbits_stack(1, &p1));
}
