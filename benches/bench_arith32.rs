use std::time::Duration;

use arithmetify::{
    ArithmeticDecoder, ArithmeticEncoder, Distribution, SequenceModel,
};
use criterion::{
    black_box, criterion_group, criterion_main, BenchmarkId, Criterion,
    Throughput,
};
use rand::thread_rng;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Alphabet {
    A,
    B,
    C,
}

#[derive(Debug, Clone, Copy)]
struct PD;
impl PD {
    const WEIGHTS: [u32; 4] = [1, 1000, 10, 1];

    fn sample(&self, rng: &mut impl rand::Rng) -> Option<Alphabet> {
        let p = rng.gen_range(0..self.denominator());
        self.symbol_lookup(p)
    }

    fn denominator() -> u32 {
        Self.denominator()
    }

    fn symbol_lookup(p: u32) -> Option<Alphabet> {
        Self.symbol_lookup(p)
    }

    fn numerator_range(symbol: Option<&Alphabet>) -> std::ops::Range<u32> {
        Self.numerator_range(symbol)
    }
}

impl Distribution<Alphabet, u32> for PD {
    fn denominator(&self) -> u32 {
        Self::WEIGHTS.iter().sum()
    }

    fn numerator_range(
        &self,
        symbol: Option<&Alphabet>,
    ) -> std::ops::Range<u32> {
        use Alphabet::*;
        let index = symbol
            .map(|s| match s {
                A => 1,
                B => 2,
                C => 3,
            })
            .unwrap_or(0);

        let cum = Self::WEIGHTS.iter().take(index).sum();
        cum..cum + Self::WEIGHTS[index]
    }

    fn symbol_lookup(&self, p: u32) -> Option<Alphabet> {
        use Alphabet::*;
        let mut cums = vec![0];
        cums.extend(Self::WEIGHTS);
        (1..cums.len()).for_each(|i| cums[i] += cums[i - 1]);
        let idx = cums.binary_search(&p).unwrap_or_else(|idx| idx - 1);

        match idx {
            0 => None,
            1 => Some(A),
            2 => Some(B),
            3 => Some(C),
            _ => panic!(
                "Cummulative probability density (p={p}) is out of bounds (0..{})",
                Self::denominator()
            ),
        }
    }
}

struct SM(Vec<Alphabet>);
impl SM {
    fn new() -> Self {
        Self(Vec::new())
    }

    pub fn sample(mut self, rng: &mut impl rand::Rng) -> Self {
        while let Some(s) = self.pd().sample(rng) {
            let p_range = PD::numerator_range(Some(&s));
            assert!(
                p_range.start < p_range.end,
                "pd has empty range for {s:?}"
            );
            self.push(s)
        }

        self
    }

    pub fn into_sequence(self) -> Vec<Alphabet> {
        self.0
    }
}
impl SequenceModel<Alphabet, u32> for SM {
    type ProbabilityDensity = PD;

    fn push(&mut self, symbol: Alphabet) {
        self.0.push(symbol)
    }

    fn pd(&self) -> Self::ProbabilityDensity {
        PD
    }
}

const SYMBOLS_COUNT: usize = 1_000_000; // Number of symbols to encode/decode

fn criterion_benchmark(c: &mut Criterion) {
    let mut group = c.benchmark_group("encoding_decoding");
    group.sample_size(10);
    group.measurement_time(Duration::new(10, 0));

    let distributions = vec![
        PD, // Add more distributions here as needed
    ];

    for pd in distributions.iter() {
        let parameter = format!("{pd:?}");

        let symbols: Vec<Alphabet> =
            SM::new().sample(&mut thread_rng()).into_sequence();

        let mut encoder = ArithmeticEncoder::new();
        let mut sm = SM(Vec::new());
        encoder.encode(&mut sm, symbols.iter().copied());
        let bytes = encoder.finalize();

        group.throughput(Throughput::Bytes(bytes.len() as u64));

        // Benchmark for encoding
        group.bench_function(BenchmarkId::new("encode", &parameter), |b| {
            b.iter(|| {
                let mut encoder = ArithmeticEncoder::new();
                let mut sm = SM(Vec::new());
                encoder.encode(&mut sm, black_box(symbols.iter().copied()));
                black_box(encoder.finalize());
            });
        });

        group.throughput(Throughput::Bytes(bytes.len() as u64));

        // Benchmark for decoding
        group.bench_function(BenchmarkId::new("decode", &parameter), |b| {
            b.iter(|| {
                let mut decoder =
                    ArithmeticDecoder::new(black_box(bytes.iter().copied()));

                let mut sm = SM(Vec::new());
                decoder.decode(&mut sm);
                black_box(&sm.0);
            });
        });
    }

    group.finish();
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
