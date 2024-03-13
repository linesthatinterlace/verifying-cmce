#![deny(clippy::pedantic)]
#![allow(clippy::missing_panics_doc)]

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
        fn bits(&self) -> &Vec<bool> {
            &self.0
        }

        #[must_use]
        pub fn num_bits(&self) -> usize {
            self.bits().len()
        }

        #[must_use]
        pub fn size(&self) -> usize {
            self.num_bits().trailing_zeros() as usize
        }

        pub fn layer_index_mut<T>(&self, gap: usize, slice: &mut impl AsMut<[T]>) {
            assert!(gap <= self.size());
            for (j, &b) in self.bits().iter().enumerate() {
                let p = add_gap_at(j, gap);
                let q = p | (usize::from(b) << gap);
                slice.as_mut().swap(p, q);
            }
        }

        pub fn zero_layer_index_mut<T>(&self, slice: &mut impl AsMut<[T]>) {
            for (j, &b) in self.bits().iter().enumerate() {
                let p = j << 1;
                let q = p | usize::from(b);
                slice.as_mut().swap(p, q);
            }
        }

        pub fn layer_index<T: Clone>(&self, gap: usize, slice: impl AsRef<[T]>) -> Vec<T> {
            let s = slice.as_ref();
            let mut result: Vec<T> = s.to_vec();
            self.layer_index_mut(gap, &mut result);

            result
        }

        pub fn zero_layer_index<T: Clone>(&self, slice: impl AsRef<[T]>) -> Vec<T> {
            let s = slice.as_ref();
            let mut result: Vec<T> = s.to_vec();
            self.zero_layer_index_mut(&mut result);

            result
        }

        pub fn layer_contents_mut(&self, gap: usize, slice: &mut impl AsMut<[usize]>) {
            assert!(gap <= self.size());
            for s in slice.as_mut() {
                *s ^= usize::from(self.bits()[remove_at(*s, gap)]) << gap;
            }
        }

        pub fn zero_layer_contents_mut(&self, slice: &mut impl AsMut<[usize]>) {
            for s in slice.as_mut() {
                *s ^= usize::from(self.bits()[*s >> 1]);
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
            let layers = bits
                .chunks_exact(1 << size)
                .map(Layer::new)
                .collect();

            layers
        }

        fn layers(&self) -> &[Layer] {
            &self.0
        }

        #[must_use]
        pub fn num_layers(&self) -> usize {
            self.layers().len()
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

        pub fn inverse_mut(&mut self) {
            self.0.reverse();
        }

        #[must_use]
        pub fn inverse(&self) -> ControlBits {
            let mut rls: Vec<_> = self.layers().to_vec();
            rls.reverse();

            ControlBits(rls)
        }

        pub fn apply_control_bits_mut<T>(&self, slice: &mut impl AsMut<[T]>) {
            for (i, l) in self.layers().iter().enumerate() {
                let gap = min(i, 2 * self.size() - i);
                l.layer_index_mut(gap, slice);
            }
        }

        pub fn apply_control_bits<T: Clone>(&self, slice: impl AsRef<[T]>) -> Vec<T> {
            let s = slice.as_ref();
            let mut result: Vec<T> = s.to_vec();
            self.apply_control_bits_mut(&mut result);

            result
        }

        pub fn bits(self) -> std::iter::Flatten<std::vec::IntoIter<Layer>> {
            self.0.into_iter().flatten()
        }

        #[must_use]
        pub fn permutation(&self) -> Perm {
            let mut pi: Perm = (0..self.num_bits_per_layer() << 1).collect();
            self.apply_control_bits_mut(&mut pi);

            pi
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
            let layers: Vec<_> = iter.into_iter().collect();
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
        let mut q: Perm = pi.to_vec();
        for j in 0..num_elements / 2 {
            let low = j << 1;
            let high = low | 1;
            p.swap(low, high);
        }
        for x in &mut q {
            *x ^= 1;
        }
        for _ in 0..(num_elements >> 1).trailing_zeros() {
            (p, q) = (composeinv(&p, &q), composeinv(&q, &p));
            c = zip(&c, composeinv(&c, &q))
                .map(|(&a, b)| min(a, b))
                .collect();
        }

        c
    }

    type FlmDecomp = (Layer, Perm, Layer);

    fn flm_decomp(pi: &Perm) -> FlmDecomp {
        let mut m = pi.clone();
        let cs = cyclemin_pibar(pi);
        let f: Vec<bool> = cs.iter().step_by(2).map(|&c| c & 1 == 1).collect();
        let f_layer = Layer::new(&f);
        f_layer.zero_layer_contents_mut(&mut m);
        let l: Vec<bool> = m.iter().step_by(2).map(|&k| k & 1 == 1).collect();
        let l_layer = Layer::new(&l);
        l_layer.zero_layer_index_mut(&mut m);

        (f_layer, m, l_layer)
    }

    pub fn from_perm(pi: &Perm) -> ControlBits {
        assert!(pi.len() >= 2);

        if pi.len() == 2 {
            ControlBits::new_from_bits(&[pi[0] == 1])
        } else {
            let (first_bits, mut m, last_bits) = flm_decomp(pi);
            for t in &mut m {
                *t >>= 1;
            }
            let even_perm: Perm = m.iter().step_by(2).copied().collect();
            let odd_perm: Perm = m.iter().skip(1).step_by(2).copied().collect();

            let even_bits = from_perm(&even_perm);
            let odd_bits = from_perm(&odd_perm);
            let middle_bits = zip(even_bits.bits(), odd_bits.bits()).flat_map(|(a, b)| [a, b]);

            let bits: Vec<_> = first_bits
                .into_iter()
                .chain(middle_bits)
                .chain(last_bits)
                .collect();
            ControlBits::new_from_bits(&bits)
        }
    }

    pub fn random(size: usize) -> ControlBits {
        let num_bits = (2 * size + 1) << size;
        let mut bits = Vec::new();
        for _ in 0..num_bits {
            bits.push(rand::random::<bool>());
        }

        ControlBits::new_from_bits(&bits)
    }

    pub fn test_random(size: usize, test_num: u32) {
        let mut fail = 0;
        for _ in 0..test_num {
            let cb = random(size);
            let p = cb.permutation();
            let cb2 = from_perm(&p);
            let pback = cb2.permutation();
            if p != pback {
                fail += 1;
            }
        }
        let successes = test_num - fail;
        println!("Tested {test_num} times with size parameter {size}.");
        println!("Failures: {fail}");
        println!("Successes: {successes}");
    }
}

fn main() {
    let c1 = control_bits::ControlBits::new_from_bits(&[false, false, false, false, false, true]);
    println!("{c1:?}");
    println!("{:?}", c1.permutation());
    assert!(c1 == control_bits::from_perm(&c1.permutation()));
    let p1 = vec![2, 3, 1, 0];
    let c2 = control_bits::from_perm(&p1);
    println!("{c2:?}");
    assert!(p1 == control_bits::from_perm(&p1).permutation());
    let c3 = control_bits::ControlBits::new_from_bits(&[
        false, false, false, false, false, true, false, false, false, false, false, true, false,
        false, false, false, false, false, true, false,
    ]);
    println!("{c3:?}");
    println!("{:?}", c3.permutation());
    let p2 = vec![5, 0, 3, 7, 6, 2, 4, 1]; //[0, 3, 2, 7, 5, 4, 6, 1];
    let c4 = control_bits::from_perm(&p2);
    println!("{:?}", control_bits::from_perm(&p2));
    println!("{:?}", c4.permutation());

    let c5 = control_bits::random(1);
    let p5 = c5.permutation();
    let c5b = control_bits::from_perm(&p5);
    let p5bs = c5b.permutation();
    println!("{p5:?}");
    println!("{p5bs:?}");
    println!("{:?}", p5 == p5bs);

    control_bits::test_random(2, 10000);
}
