use std::io::Write;

use rand::{thread_rng, Rng};

use super::*;
use crate::{
    ArithmeticDecoder, ArithmeticEncoder, Distribution, SequenceModel,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Alphabet {
    A,
    B,
    C,
}

struct PD;
impl PD {
    const WEIGHTS: [u32; 4] = [10, 1000, 10, 1];

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
    pub fn sample(&mut self, rng: &mut impl rand::Rng) {
        while let Some(s) = self.pd().sample(rng) {
            let p_range = PD::numerator_range(Some(&s));
            assert!(
                p_range.start < p_range.end,
                "pd has empty range for {s:?}"
            );
            self.push(s)
        }
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

fn test_symbols(symbols: &[Alphabet]) {
    let mut encoder = ArithmeticEncoder32::new();
    let mut sm = SM(Vec::new());
    encoder.encode(&mut sm, symbols.iter().copied());

    let bytes = encoder.finalize();

    let mut decoder = ArithmeticDecoder32::new(bytes);
    let mut sm = SM(Vec::new());
    decoder.decode(&mut sm);

    assert_eq!(&sm.0, &symbols);
}

#[test]
fn test_as() {
    test_symbols(&[Alphabet::A; 320]);
}

#[test]
fn test_cs() {
    test_symbols(&[Alphabet::C; 640]);
}

#[test]
pub fn test_random() {
    let rng = &mut thread_rng();
    let num_tests = 100000;
    let mut last_print = std::time::Instant::now();

    println!();
    for i in 0..num_tests {
        let mut sm = SM(Vec::new());
        sm.sample(rng);
        let symbols = sm.into_sequence();

        test_symbols(&symbols);
        if last_print.elapsed() > std::time::Duration::from_millis(200) {
            print!("\r{}/{num_tests}", i + 1);
            last_print = std::time::Instant::now();
            let _ = std::io::stdout().flush();
        }
    }

    println!("{num_tests}/{num_tests}");
}

#[test]
fn test_encode_by_weight() {
    test_distribution(&[100, 345, 102, 534, 435]);
    test_distribution(&[10]);
    test_distribution(&[1, 1, 1]);
}

fn test_distribution(weights: &[u32]) {
    let rng = &mut thread_rng();
    let mut cum_weights: Box<[u32]> = weights.into();
    for i in 1..cum_weights.len() {
        cum_weights[i] += cum_weights[i - 1];
    }

    let total_weights = *cum_weights
        .last()
        .expect("There should be at least one symbol");

    let mut input = Vec::new();
    loop {
        let p = rng.gen_range(0..total_weights);
        let symbol = match cum_weights.binary_search(&p) {
            Ok(sym) => sym + 1,
            Err(sym) => sym,
        };

        input.push(symbol);
        let 1.. = symbol else { break };
    }

    let mut encoder = ArithmeticEncoder::new();
    for symbol in &input {
        encoder.encode_by_weights(weights.iter().copied(), *symbol);
    }

    let compressed = encoder.finalize();
    let mut decoder = ArithmeticDecoder::new(compressed);

    let mut decoded = vec![];
    loop {
        let symbol = decoder.decode_by_weights(weights.iter().copied());
        decoded.push(symbol);

        let 1.. = symbol else { break };
    }

    assert_eq!(input, decoded.as_slice());
}
