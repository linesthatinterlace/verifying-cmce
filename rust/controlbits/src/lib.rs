#![deny(clippy::pedantic)]
#![warn(clippy::style)]

mod control_bits {
    use std::cmp::min;
    use std::iter::zip;

    fn add_gap_at(k: usize, i: usize) -> usize {
        let top_bits = (k >> i) << i;

        (top_bits << 1) | (k ^ top_bits)
    }

    fn remove_at(k: usize, i: usize) -> usize {
        let top_bits = (k >> i) << i;

        (top_bits >> 1) | (k ^ top_bits)
    }

    type Perm = Vec<usize>;

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
                let p = add_gap_at(j, gap);
                let q = p | (usize::from(b) << gap);
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
                let p = j << 1;
                let q = p | usize::from(b);
                slice.swap(p, q);
            }
        }

        pub fn zero_apply(&self, slice: &mut [usize]) {
            for s in slice {
                *s ^= usize::from(self.0[*s >> 1]);
            }
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

    #[derive(Clone, Debug, PartialEq)]
    pub struct ControlBits(Vec<Layer>);

    impl ControlBits {
        #[must_use]
        pub fn new(layers: &[Layer]) -> ControlBits {
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

        pub fn bits(self) -> std::iter::Flatten<std::vec::IntoIter<Layer>> {
            self.0.into_iter().flatten()
        }

        #[must_use]
        pub fn permutation(&self) -> Perm {
            let mut pi: Perm = (0..self.num_bits_per_layer() << 1).collect();
            self.apply_control_bits(&mut pi);

            pi
        }

        pub fn test(&self) -> bool {
            let p = self.permutation();
            test_perm(&p)
        }
    }

    impl From<ControlBits> for Vec<bool> {
        fn from(cb: ControlBits) -> Self {
            cb.bits().collect()
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

    impl FromIterator<bool> for ControlBits {
        fn from_iter<I: IntoIterator<Item = bool>>(iter: I) -> Self {
            let bv: Vec<bool> = iter.into_iter().collect();
            ControlBits::new_from_bits(&bv)
        }
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
        let mut p: Perm = pi.to_vec();
        for ch in p.chunks_exact_mut(2) {
            ch.swap(0, 1);
        }
        let mut q: Perm = pi.iter().map(|&x| x ^ 1).collect();
        for _ in 0..(num_elements >> 1).trailing_zeros() {
            (p, q) = (composeinv(&p, &q), composeinv(&q, &p));
            let cp = composeinv(&c, &q);
            for (x, y) in zip(&mut c, cp) {
                *x = min(*x, y);
            }
        }

        c
    }

    fn flm_decomp(pi: &[usize]) -> (Layer, Vec<usize>, Layer) {
        let mut middle_perm = pi.to_vec();
        let cs = cyclemin_pibar(pi);
        let f_layer: Layer = cs.iter().step_by(2).map(|&c| c & 1 == 1).collect();
        f_layer.zero_apply(&mut middle_perm);
        let l_layer: Layer = middle_perm.iter().step_by(2).map(|&k| k & 1 == 1).collect();
        l_layer.zero_apply_idx(&mut middle_perm);
        for t in &mut middle_perm {
            *t >>= 1;
        }
        (f_layer, middle_perm, l_layer)
    }

    pub fn from_perm(pi: &[usize]) -> ControlBits {
        assert!(pi.len() >= 2);

        if pi.len() == 2 {
            ControlBits::new_from_bits(&[pi[0] == 1])
        } else {
            let (first_bits, middle_perm, last_bits) = flm_decomp(pi);
            let even_perm: Perm = middle_perm.iter().step_by(2).copied().collect();
            let odd_perm: Perm = middle_perm.iter().skip(1).step_by(2).copied().collect();

            let even_bits = from_perm(&even_perm);
            let odd_bits = from_perm(&odd_perm);
            let middle_bits = zip(even_bits.bits(), odd_bits.bits()).flat_map(|(a, b)| [a, b]);

            first_bits
                .into_iter()
                .chain(middle_bits)
                .chain(last_bits)
                .collect()
        }
    }

    pub fn test_perm(p: &[usize]) -> bool {
        let cb = from_perm(p);

        *p == cb.permutation()
    }

    #[cfg(test)]
    mod tests {
        use super::*;

        fn random(size: usize) -> ControlBits {
            let num_bits = (2 * size + 1) << size;
            let mut bits = Vec::new();
            for _ in 0..num_bits {
                bits.push(rand::random::<bool>());
            }

            ControlBits::new_from_bits(&bits)
        }

        pub fn test_random(size: usize) -> bool {
            let cb = random(size);

            cb.test()
        }

        pub fn test_randoms(size: usize, test_num: u32) -> bool {
            for _ in 0..test_num {
                if !test_random(size) {
                    return false;
                }
            }

            true
        }

        #[test]
        #[allow(clippy::should_panic_without_expect)]
        #[should_panic]
        fn panic_empty_cb() {
            let _cb = ControlBits::new_from_bits(&[]);
        }

        #[test]
        fn create_cb_size_zero() {
            let cb = ControlBits::new_from_bits(&[false]);
            assert_eq!(cb, ControlBits(vec![Layer(vec![false])]));
        }

        #[test]
        fn create_cb_size_one() {
            let cb = ControlBits::new_from_bits(&[false, true, true, false, false, true]);
            assert_eq!(
                cb,
                ControlBits(vec![
                    Layer(vec![false, true]),
                    Layer(vec![true, false]),
                    Layer(vec![false, true])
                ])
            );
        }

        #[test]
        fn create_cb_size_two() {
            let cb = ControlBits::new_from_bits(&[
                false, true, true, false, false, true, false, false, false, true, true, false,
                true, false, true, false, true, false, true, false,
            ]);
            assert_eq!(
                cb,
                ControlBits(vec![
                    Layer(vec![false, true, true, false]),
                    Layer(vec![false, true, false, false]),
                    Layer(vec![false, true, true, false]),
                    Layer(vec![true, false, true, false]),
                    Layer(vec![true, false, true, false])
                ])
            );
        }

        #[test]
        fn calculate_cb_size_one_trivial() {
            let p: Perm = vec![0, 1];
            let cb = from_perm(&p);
            assert_eq!(cb, ControlBits(vec![Layer(vec![false])]));
        }

        #[test]
        fn calculate_cb_size_one_nontrivial() {
            let p: Perm = vec![1, 0];
            let cb = from_perm(&p);
            assert_eq!(cb, ControlBits(vec![Layer(vec![true])]));
        }

        #[test]
        fn calculate_cb_size_two_trivial() {
            let p: Perm = vec![0, 1, 2, 3];
            let cb = from_perm(&p);
            assert_eq!(
                cb,
                ControlBits(vec![
                    Layer(vec![false, false]),
                    Layer(vec![false, false]),
                    Layer(vec![false, false])
                ])
            );
        }

        #[test]
        fn calculate_cb_size_two_nontrivial() {
            let p: Perm = vec![1, 2, 3, 0];
            let cb = from_perm(&p);
            assert_eq!(
                cb,
                ControlBits(vec![
                    Layer(vec![false, false]),
                    Layer(vec![true, false]),
                    Layer(vec![true, true])
                ])
            );
        }
        #[test]
        fn calculate_cb_size_three_trivial() {
            let p: Perm = vec![0, 1, 2, 3, 4, 5, 6, 7];
            let cb = from_perm(&p);
            assert_eq!(
                cb,
                ControlBits(vec![
                    Layer(vec![false, false, false, false]),
                    Layer(vec![false, false, false, false]),
                    Layer(vec![false, false, false, false]),
                    Layer(vec![false, false, false, false]),
                    Layer(vec![false, false, false, false])
                ])
            );
        }

        #[test]
        fn calculate_cb_size_three_nontrivial() {
            let p: Perm = vec![7, 4, 1, 2, 3, 5, 0, 6];
            let cb = from_perm(&p);
            assert_eq!(
                cb,
                ControlBits(vec![
                    Layer(vec![false, false, true, true]),
                    Layer(vec![false, false, true, true]),
                    Layer(vec![true, false, false, true]),
                    Layer(vec![false, true, true, true]),
                    Layer(vec![false, true, true, false])
                ])
            );
        }

        #[test]
        fn perm_bits_perm_eq_perm() {
            let p: Perm = vec![4, 7, 1, 3, 6, 0, 2, 5];
            assert!(test_perm(&p));
        }

        #[test]
        fn random_size_thirteen() {
            assert!(test_random(13));
        }

        #[test]
        fn ten_thousand_random_size_threes() {
            assert!(test_randoms(3, 10000));
        }
    }

    #[cfg(kani)]
    #[kani::proof]
    fn gap_check() {
        let k: usize = kani::any();
        kani::assume(k <= usize::MAX >> 1);
        let i: usize = kani::any();
        kani::assume(i < 64);
        assert!(remove_at(add_gap_at(k, i), i) == k);
    }

    #[cfg(kani)]
    #[kani::proof]
    fn control_bits_size_two_test() {
        let bits: [bool; 8] = kani::any();
        let cb = Layer::new(&bits);
        let mut slice: [u64; 16] = kani::any();
        let slice_copy = slice.to_vec();
        cb.zero_apply_idx(&mut slice);
        cb.zero_apply_idx(&mut slice);
        assert!(slice_copy == slice);
    }
}
