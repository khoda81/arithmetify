//! # Arithmetic Coding Library
//!
//! This library provides an implementation of arithmetic encoding and decoding using a 32-bit precision. Arithmetic coding is a form of entropy encoding that represents sequences of symbols as a single number in a fractional number range. It is particularly effective for data compression.
//!
//! # Core Components
//!
//! - `Distribution`: Defines how symbols are mapped to a probability range.
//! - `SequenceModel`: Provides a way to manage sequences of symbols and their distributions.
//! - `ArithmeticEncoder`: Encodes sequences of symbols into a compressed bitstream.
//! - `ArithmeticDecoder`: Decodes a compressed bitstream back into the original sequence of symbols.
//!
//! # Example Usage
//! This example demonstrates how to use the provided arithmetic encoder and decoder with a custom model.
//!
//! ```rust
//! use arithmetify::{ArithmeticEncoder, ArithmeticDecoder, SequenceModel, Distribution};
//! use std::ops::Range;
//!
//! #[derive(Debug, Clone, Copy, PartialEq, Eq)]
//! enum Alphabet {
//!     A,
//!     B,
//!     C,
//! }
//!
//! /// A simple probability distribution for `Alphabet` symbols, where each symbol has a weight that defines its probability.
//! struct PD;
//!
//! impl PD {
//!     /// Weights for each symbol, representing their relative probabilities.
//!     const WEIGHTS: [u32; 4] = [10, 1000, 10, 1];  // Includes an extra weight for end-of-stream
//! }
//!
//! impl Distribution<Alphabet, u32> for PD {
//!     /// Returns the total range (denominator) of all weights.
//!     fn denominator(&self) -> u32 {
//!         Self::WEIGHTS.iter().sum()
//!     }
//!
//!     /// Provides the range of cumulative probabilities for a given symbol.
//!     fn numerator_range(
//!         &self,
//!         symbol: Option<&Alphabet>,
//!     ) -> Range<u32> {
//!         use Alphabet::*;
//!         let index = symbol
//!             .map(|s| match s {
//!                 A => 1,
//!                 B => 2,
//!                 C => 3,
//!             })
//!             .unwrap_or(0);  // Default to end-of-stream if no symbol is provided
//!
//!         let cum = Self::WEIGHTS.iter().take(index).sum();
//!         cum..cum + Self::WEIGHTS[index]
//!     }
//!
//!     /// Maps a cumulative probability to a symbol.
//!     fn symbol_lookup(&self, p: u32) -> Option<Alphabet> {
//!         let mut cums = vec![0];
//!         cums.extend(Self::WEIGHTS);
//!         (1..cums.len()).for_each(|i| cums[i] += cums[i - 1]);
//!         let idx = cums.binary_search(&p).unwrap_or_else(|idx| idx - 1);
//!
//!         use Alphabet::*;
//!         match idx {
//!             0 => None,
//!             1 => Some(A),
//!             2 => Some(B),
//!             3 => Some(C),
//!             _ => panic!("Cumulative probability (p={p}) is out of bounds (0..{})", self.denominator()),
//!         }
//!     }
//! }
//!
//! /// A simple sequence model that uses the `PD` probability distribution and maintains a sequence of symbols.
//! struct SM(Vec<Alphabet>);
//!
//! impl SequenceModel<Alphabet, u32> for SM {
//!     type ProbabilityDensity = PD;
//!
//!     /// Adds a symbol to the sequence.
//!     fn push(&mut self, symbol: Alphabet) {
//!         self.0.push(symbol)
//!     }
//!
//!     /// Returns the probability distribution for the model.
//!     fn pd(&self) -> Self::ProbabilityDensity {
//!         PD
//!     }
//! }
//!
//! // Example usage:
//! let symbols = vec![Alphabet::A, Alphabet::B, Alphabet::C, Alphabet::A];
//!
//! // Create an encoder and encode the symbols.
//! let mut encoder = ArithmeticEncoder::new();
//! let mut sm = SM(Vec::new());
//! encoder.encode(&mut sm, symbols.iter().copied());
//! let bytes = encoder.finalize();
//!
//! // Create a decoder and decode the symbols back.
//! let mut decoder = ArithmeticDecoder::new(bytes);
//! let mut sm = SM(Vec::new());
//! decoder.decode(&mut sm);
//!
//! // Verify that the decoded symbols match the original input.
//! assert_eq!(&sm.0, &symbols);
//! ```
//!
//! This example defines a custom probability distribution (`PD`) and a sequence model (`SM`) to encode and decode a sequence of symbols using arithmetic coding. The `PD` distribution assigns weights to symbols, and `SM` manages the sequence of symbols and provides the distribution.

use std::ops::Range;

/// Describes how symbols are mapped to a probability range in arithmetic coding.
///
/// This trait must be implemented for any distribution model used by the encoder/decoder.
/// The `denominator` function returns the total range of probabilities, while `numerator_range`
/// gives the range for a specific symbol.
pub trait Distribution<Symbol, P> {
    fn denominator(&self) -> P;
    fn numerator_range(&self, symbol: Option<&Symbol>) -> Range<P>;
    fn symbol_lookup(&self, p: P) -> Option<Symbol>;
}

/// A model for sequences of symbols used in arithmetic coding.
///
/// Implementing this trait allows the encoder/decoder to track and update the probability
/// distributions of symbols as they are processed.
pub trait SequenceModel<Symbol, P> {
    type ProbabilityDensity: Distribution<Symbol, P>;

    fn push(&mut self, symbol: Symbol);
    fn pd(&self) -> Self::ProbabilityDensity;
}

/// 32-bit arithmetic encoder and decoder.
pub mod arith32;

/// Type alias for the 32-bit arithmetic encoder.
pub type ArithmeticEncoder = arith32::ArithmeticEncoder32;
/// Type alias for the 32-bit arithmetic decoder with a generic iterator for bytes.
pub type ArithmeticDecoder<I> = arith32::ArithmeticDecoder32<I>;
