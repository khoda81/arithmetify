use std::ops::Range;

pub trait Distribution<Symbol, P> {
    fn denominator(&self) -> P;
    fn numerator_range(&self, symbol: Option<&Symbol>) -> Range<P>;
    fn symbol_lookup(&self, p: P) -> Option<Symbol>;
}

pub trait SequenceModel<Symbol, P> {
    type ProbabilityDensity: Distribution<Symbol, P>;

    fn push(&mut self, symbol: Symbol);
    fn pd(&self) -> Self::ProbabilityDensity;
}

mod arith32;

pub type ArithmeticEncoder = arith32::ArithmeticEncoder32;
pub type ArithmeticDecoder<I> = arith32::ArithmeticDecoder32<I>;
