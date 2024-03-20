#![deny(clippy::pedantic)]
#![warn(clippy::style)]
#![allow(clippy::missing_panics_doc)]
use std::cmp::min;
use std::iter::zip;

fn add_zero_at(k: usize, i: usize) -> usize {
    let top_bits = (k >> i) << i;

    (top_bits << 1) | (k ^ top_bits)
}

fn add_one_at(k: usize, i: usize) -> usize {
    add_zero_at(k, i) | (1 << i)
}

fn add_bit_at(k: usize, i: usize, b: bool) -> usize {
    add_zero_at(k, i) | (usize::from(b) << i)
}

fn remove_at(k: usize, i: usize) -> usize {
    let top_bits = (k >> (i + 1)) << (i + 1);
    let bottom_bits = ((k ^ top_bits) | (1 << i)) ^ (1 << i);

    (top_bits >> 1) | bottom_bits
}

fn composeinv<S: Ord + Clone, T: Ord>(a: &[S], b: &[T]) -> Vec<S> {
    let mut pairs: Vec<(&T, &S)> = zip(b, a).collect();
    pairs.sort_unstable();
    let (_, result): (Vec<&T>, Vec<&S>) = pairs.into_iter().unzip();

    result.into_iter().cloned().collect()
}

fn cyclemin_pibar(pi: &[usize]) -> Vec<usize> {
    let num_elements = pi.len();
    let mut c: Vec<usize> = (0..num_elements).collect();
    let mut p = pi.to_vec();
    for ch in p.chunks_exact_mut(2) {
        ch.swap(0, 1);
    }
    let mut q: Vec<usize> = pi.iter().map(|&x| x ^ 1).collect();
    for _ in 0..(num_elements >> 1).trailing_zeros() {
        (p, q) = (composeinv(&p, &q), composeinv(&q, &p));
        let cp = composeinv(&c, &q);
        for (x, y) in zip(&mut c, cp) {
            *x = min(*x, y);
        }
    }

    c
}

#[derive(Clone, Debug, PartialEq)]
pub struct Layer(Vec<bool>);

impl Layer {
    #[must_use]
    pub fn new(bits: &[bool]) -> Layer {
        let len = bits.len();
        let size = len.trailing_zeros();

        assert!(len == 1 << size);

        Layer(bits.to_vec())
    }

    #[must_use]
    pub fn num_bits(&self) -> usize {
        self.0.len()
    }

    #[must_use]
    pub fn size(&self) -> usize {
        self.num_bits().trailing_zeros() as usize
    }

    pub fn apply_idx<T>(&self, gap: usize, slice: &mut [T]) {
        assert!(gap <= self.size());
        for (j, &b) in self.0.iter().enumerate() {
            let p = add_zero_at(j, gap);
            let q = add_bit_at(j, gap, b);
            slice.swap(p, q);
        }
    }

    pub fn apply(&self, gap: usize, slice: &mut [usize]) {
        assert!(gap <= self.size());
        for s in slice {
            *s ^= usize::from(self.0[remove_at(*s, gap)]) << gap;
        }
    }

    pub fn zero_apply_idx<T>(&self, slice: &mut [T]) {
        for (j, &b) in self.0.iter().enumerate() {
            let low = j << 1;
            let high = low | usize::from(b);
            slice.swap(low, high);
        }
    }

    pub fn zero_apply(&self, slice: &mut [usize]) {
        for s in slice {
            *s ^= usize::from(self.0[*s >> 1]);
        }
    }

    #[must_use]
    pub fn interlace(&self, l: &Layer) -> Layer {
        assert!(self.size() == l.size());
        zip(self.0.iter(), l.0.iter())
            .flat_map(|(&a, &b)| [a, b])
            .collect()
    }
}

impl IntoIterator for Layer {
    type Item = bool;
    type IntoIter = std::vec::IntoIter<Self::Item>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl FromIterator<bool> for Layer {
    fn from_iter<I: IntoIterator<Item = bool>>(iter: I) -> Self {
        let k: Vec<bool> = iter.into_iter().collect();
        Layer::new(&k)
    }
}

fn flm_decomp(pi: &[usize]) -> (Layer, Vec<usize>, Vec<usize>, Layer) {
    let mut middle_perm = pi.to_vec();
    let cs = cyclemin_pibar(pi);
    let f_layer: Layer = cs.iter().step_by(2).map(|&c| c & 1 == 1).collect();
    f_layer.zero_apply(&mut middle_perm);
    let l_layer: Layer = middle_perm.iter().step_by(2).map(|&k| k & 1 == 1).collect();
    l_layer.zero_apply_idx(&mut middle_perm);
    for t in &mut middle_perm {
        *t >>= 1;
    }
    let even_perm: Vec<usize> = middle_perm.iter().step_by(2).copied().collect();
    let odd_perm: Vec<usize> = middle_perm.iter().skip(1).step_by(2).copied().collect();
    (f_layer, even_perm, odd_perm, l_layer)
}

#[derive(Clone, Debug, PartialEq)]
pub struct ControlBits(Vec<Layer>);

impl ControlBits {
    #[must_use]
    fn new(layers: &[Layer]) -> ControlBits {
        let num_layers = layers.len();
        let size = num_layers >> 1;
        assert!(num_layers == (size << 1) + 1);
        assert!(layers.iter().all(|l| l.size() == size));

        ControlBits(layers.to_vec())
    }

    #[must_use]
    pub fn new_from_bits(bits: &[bool]) -> ControlBits {
        let size = bits.len().trailing_zeros() as usize;
        let layers = bits.chunks_exact(1 << size).map(Layer::new).collect();

        layers
    }

    #[must_use]
    pub fn random(size: usize) -> ControlBits {
        let num_bits = (2 * size + 1) << size;
        let mut bits = Vec::new();
        for _ in 0..num_bits {
            bits.push(rand::random::<bool>());
        }

        ControlBits::new_from_bits(&bits)
    }

    #[must_use]
    pub fn num_layers(&self) -> usize {
        self.0.len()
    }

    #[must_use]
    pub fn size(&self) -> usize {
        self.num_layers() >> 1
    }

    #[must_use]
    pub fn num_bits_per_layer(&self) -> usize {
        1 << self.size()
    }

    #[must_use]
    pub fn num_bits(&self) -> usize {
        self.num_layers() * self.num_bits_per_layer()
    }

    pub fn inverse(&mut self) {
        self.0.reverse();
    }

    pub fn apply_control_bits<T>(&self, slice: &mut [T]) {
        for (i, l) in self.0.iter().enumerate() {
            let gap = min(i, 2 * self.size() - i);
            l.apply_idx(gap, slice);
        }
    }

    #[must_use]
    pub fn interlace(&self, cb: &ControlBits, fl: &Layer, ll: &Layer) -> ControlBits {
        let mut k: Vec<Layer> = zip(self.0.iter(), cb.0.iter())
            .map(|(a, b)| a.interlace(b))
            .collect();
        k.push(ll.clone());
        k.insert(0, fl.clone());
        ControlBits::new(&k)
    }

    #[must_use]
    pub fn permutation(&self) -> Vec<usize> {
        let mut pi: Vec<usize> = (0..self.num_bits_per_layer() << 1).collect();
        self.apply_control_bits(&mut pi);

        pi
    }

    #[must_use]
    pub fn test(&self) -> bool {
        Self::test_perm(&self.permutation())
    }

    #[must_use]
    pub fn from_perm(pi: &[usize]) -> ControlBits {
        assert!(pi.len().is_power_of_two() && pi.len() >= 2);

        if pi.len() == 2 {
            ControlBits::new(&[Layer::new(&[pi[0] == 1])])
        } else {
            let (first_bits, even_perm, odd_perm, last_bits) = flm_decomp(pi);

            ControlBits::interlace(
                &ControlBits::from_perm(&even_perm),
                &ControlBits::from_perm(&odd_perm),
                &first_bits,
                &last_bits,
            )
        }
    }

    #[must_use]
    pub fn test_random(size: usize) -> bool {
        let cb = ControlBits::random(size);

        cb.test()
    }

    #[must_use]
    pub fn test_randoms(size: usize, test_num: u32) -> bool {
        for _ in 0..test_num {
            if !Self::test_random(size) {
                return false;
            }
        }

        true
    }

    #[must_use]
    fn test_perm(p: &[usize]) -> bool {
        let cb = Self::from_perm(p);

        *p == cb.permutation()
    }
}

impl IntoIterator for ControlBits {
    type Item = Layer;
    type IntoIter = std::vec::IntoIter<Self::Item>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl FromIterator<Layer> for ControlBits {
    fn from_iter<I: IntoIterator<Item = Layer>>(iter: I) -> Self {
        let layers: Vec<Layer> = iter.into_iter().collect();
        ControlBits::new(&layers)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    #[allow(clippy::should_panic_without_expect)]
    #[should_panic]
    fn panic_empty_cb() {
        let _cb = ControlBits::new(&[]);
    }

    #[test]
    fn create_cb_size_zero() {
        let cb = ControlBits::new_from_bits(&[false]);
        assert_eq!(cb, ControlBits::new(&[Layer::new(&[false])]));
    }

    #[test]
    fn create_cb_size_one() {
        let cb = ControlBits::new_from_bits(&[false, true, true, false, false, true]);
        assert_eq!(
            cb,
            ControlBits::new(&[
                Layer::new(&[false, true]),
                Layer::new(&[true, false]),
                Layer::new(&[false, true])
            ])
        );
    }

    #[test]
    fn create_cb_size_two() {
        let cb = ControlBits::new_from_bits(&[
            false, true, true, false, false, true, false, false, false, true, true, false, true,
            false, true, false, true, false, true, false,
        ]);
        assert_eq!(
            cb,
            ControlBits::new(&[
                Layer::new(&[false, true, true, false]),
                Layer::new(&[false, true, false, false]),
                Layer::new(&[false, true, true, false]),
                Layer::new(&[true, false, true, false]),
                Layer::new(&[true, false, true, false])
            ])
        );
    }

    #[test]
    fn calculate_cb_size_one_trivial() {
        let p: Vec<usize> = vec![0, 1];
        let cb = ControlBits::from_perm(&p);
        assert_eq!(cb, ControlBits::new(&[Layer::new(&[false])]));
    }

    #[test]
    fn calculate_cb_size_one_nontrivial() {
        let p: Vec<usize> = vec![1, 0];
        let cb = ControlBits::from_perm(&p);
        assert_eq!(cb, ControlBits::new(&[Layer::new(&[true])]));
    }

    #[test]
    fn calculate_cb_size_two_trivial() {
        let p: Vec<usize> = vec![0, 1, 2, 3];
        let cb = ControlBits::from_perm(&p);
        assert_eq!(
            cb,
            ControlBits::new(&[
                Layer::new(&[false, false]),
                Layer::new(&[false, false]),
                Layer::new(&[false, false])
            ])
        );
    }

    #[test]
    fn calculate_cb_size_two_nontrivial() {
        let p: Vec<usize> = vec![1, 2, 3, 0];
        let cb = ControlBits::from_perm(&p);
        assert_eq!(
            cb,
            ControlBits::new(&[
                Layer::new(&[false, false]),
                Layer::new(&[true, false]),
                Layer::new(&[true, true])
            ])
        );
    }
    #[test]
    fn calculate_cb_size_three_trivial() {
        let p: Vec<usize> = vec![0, 1, 2, 3, 4, 5, 6, 7];
        let cb = ControlBits::from_perm(&p);
        assert_eq!(
            cb,
            ControlBits::new(&[
                Layer::new(&[false, false, false, false]),
                Layer::new(&[false, false, false, false]),
                Layer::new(&[false, false, false, false]),
                Layer::new(&[false, false, false, false]),
                Layer::new(&[false, false, false, false])
            ])
        );
    }

    #[test]
    fn calculate_cb_size_three_nontrivial() {
        let p: Vec<usize> = vec![7, 4, 1, 2, 3, 5, 0, 6];
        let cb = ControlBits::from_perm(&p);
        assert_eq!(
            cb,
            ControlBits::new(&[
                Layer::new(&[false, false, true, true]),
                Layer::new(&[false, false, true, true]),
                Layer::new(&[true, false, false, true]),
                Layer::new(&[false, true, true, true]),
                Layer::new(&[false, true, true, false])
            ])
        );
    }

    #[test]
    fn calculate_perm_size_three_nontrivial() {
        let cb = ControlBits::new(&[
            Layer::new(&[false, false, true, true]),
            Layer::new(&[false, false, true, true]),
            Layer::new(&[true, false, false, true]),
            Layer::new(&[false, true, true, true]),
            Layer::new(&[false, true, true, false]),
        ]);
        let p = cb.permutation();
        assert_eq!(p, vec![7, 4, 1, 2, 3, 5, 0, 6]);
    }

    #[test]
    fn calculate_perm_size_eleven_trivial() {
        let bits = [false; 47104];

        let cb = ControlBits::new_from_bits(&bits);
        let p = cb.permutation();
        let vec: Vec<usize> = (0..4096).collect();
        assert_eq!(p, vec);
    }

    #[test]
    fn perm_bits_perm_eq_perm() {
        let p: Vec<usize> = vec![4, 7, 1, 3, 6, 0, 2, 5];
        assert!(ControlBits::test_perm(&p));
    }

    #[test]
    fn random_size_thirteen() {
        assert!(ControlBits::test_random(13));
    }

    #[test]
    fn ten_thousand_random_size_fours() {
        assert!(ControlBits::test_randoms(4, 10000));
    }

    #[test]
    fn gap_check_one_second() {
        let k: usize = 30;
        let i: usize = 1;
        let p = add_one_at(k, i);
        let q = remove_at(p, i);
        assert!(q == k);
    }

    #[test]
    fn gap_check_one_third() {
        let k: usize = 0;
        let i: usize = 0;
        let p = add_zero_at(k, i);
        let q = p | (1 << i);
        assert!(remove_at(q, i) == k);
    }
}

#[cfg(kani)]
#[kani::proof]
fn gap_check_zero() {
    let k: usize = kani::any();
    kani::assume(k <= usize::MAX >> 1);
    let i: usize = kani::any();
    kani::assume(i < 63);
    assert!(remove_at(add_zero_at(k, i), i) == k);
}

#[cfg(kani)]
#[kani::proof]
fn gap_check_one() {
    let k: usize = kani::any();
    kani::assume(k <= usize::MAX >> 1);
    let i: usize = kani::any();
    kani::assume(i < 63);
    let p = add_one_at(k, i);
    assert!(remove_at(p, i) == k);
}

#[cfg(kani)]
#[kani::proof]
fn bit_add_check() {
    let k: usize = kani::any();
    kani::assume(k <= usize::MAX >> 1);
    let i: usize = kani::any();
    kani::assume(i < 63);
    let b: bool = kani::any();
    let p = add_bit_at(k, i, b);
    assert!(remove_at(p, i) == k);
}

#[cfg(kani)]
#[kani::proof]
fn bit_add_eq_branch() {
    let k: usize = kani::any();
    kani::assume(k <= usize::MAX >> 1);
    let i: usize = kani::any();
    kani::assume(i < 63);
    let b: bool = kani::any();
    let p = if b {
        add_one_at(k, i)
    } else {
        add_zero_at(k, i)
    };
    let p2 = add_bit_at(k, i, b);
    assert!(p == p2);
}

#[cfg(kani)]
#[kani::proof]
fn layer_size_two_involution() {
    let bits: [bool; 8] = kani::any();
    let cb = Layer::new(&bits);
    let mut slice: [u64; 16] = kani::any();
    let slice_copy = slice.to_vec();
    cb.zero_apply_idx(&mut slice);
    cb.zero_apply_idx(&mut slice);
    assert!(slice_copy == slice);
}

/*
#[cfg(kani)]
#[kani::proof]
fn control_bits_size_two_test() {
    let x1: usize = kani::any();
    let x2: usize = kani::any();
    kani::assume(x1 == 0 || x1 == 1);
    kani::assume(x2 == 0 || x2 == 1);
    kani::assume(x1 != x2);
    let p = [x1, x2];
    let cb = ControlBits::from_perm(&p);
    assert!(p == *cb.permutation());
}*/
