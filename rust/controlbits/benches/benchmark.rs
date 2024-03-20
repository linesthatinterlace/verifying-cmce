use control_bits::ControlBits;
use criterion::{black_box, criterion_group, criterion_main, Criterion};

fn criterion_benchmark(c: &mut Criterion) {
    c.bench_function("size 7", |b| {
        b.iter(|| black_box(ControlBits::random(10)).test())
    });
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
