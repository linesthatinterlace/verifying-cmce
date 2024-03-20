use control_bits::ControlBits;

fn main() {
    /*let cb = ControlBits::new_from_bits(&[
        false, false, true, true, false, false, true, true, true, false, false, true, false, true,
        true, true, false, true, true, false,
    ]);*/
    //let p: Vec<usize> = vec![7, 4, 1, 2, 3, 5, 0, 6];
    //let p = cb.permutation();
    //let _ = ControlBits::from_perm(&p);
    let _ = ControlBits::test_randoms(8, 1000);
}
