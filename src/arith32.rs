//! This module implements a 32-bit arithmetic encoder and decoder for compressing data based on symbol probabilities.
//!
//! # Overview
//! Arithmetic encoding compresses data by representing sequences of symbols with intervals in a continuous range of real numbers. The probability of each symbol determines the size of the interval it occupies. This module provides:
//!
//! - `ArithmeticEncoder32`: Encodes symbols into a compressed bitstream using arithmetic encoding.
//! - `ArithmeticDecoder32`: Decodes compressed data back into the original symbols using arithmetic decoding.
//!
//! # Example Usage
//! ```
//! // Define symbol weights corresponding to their probabilities.
//! let weights = [2, 4, 6, 8];  // Example weights for symbols
//! // Input symbols to encode.
//! let input = [1, 1, 2, 3, 2, 1, 0];  // Sequence of symbols to be encoded
//!
//! // Create a new encoder instance.
//! let mut encoder = ArithmeticEncoder::new();
//! // Encode each symbol in the input sequence by its weights.
//! for symbol in input {
//!     encoder.encode_by_weights(weights, symbol);
//! }
//!
//! // Finalize the encoding process and obtain the compressed data.
//! let compressed = encoder.finalize();
//!
//! // Create a new decoder instance from the compressed data.
//! let mut decoder = ArithmeticDecoder::new(compressed);
//!
//! // Decode the compressed data back to symbols.
//! let mut decoded = vec![];
//! loop {
//!     let symbol = decoder.decode_by_weights(weights);  // Decode the next symbol
//!     decoded.push(symbol);  // Store the decoded symbol
//!     if symbol == 0 {  // Stop decoding when reaching the end-of-sequence symbol
//!         break;
//!     }
//! }
//!
//! // Verify that the original input matches the decoded symbols.
//! assert_eq!(input, decoded.as_slice());
//! ```

use std::{collections::VecDeque, fmt::Debug, ops::Range};

use super::SequenceModel;
use crate::Distribution as _;

const WHOLE: u64 = 0x1_0000_0000_u64;
const HALF: u64 = WHOLE / 2;
const QUARTER: u64 = WHOLE / 4;

/// A 32-bit arithmetic encoder that compresses data by encoding symbols
/// into a bitstream based on their probabilities.
///
/// # Example:
/// ```
/// use arithmetify::arith32::ArithmeticEncoder32;
///
/// let weights = [2, 1, 1];
/// let mut encoder = ArithmeticEncoder32::new();
/// encoder.encode_by_weights(weights, 2);
/// encoder.encode_by_weights(weights, 2);
/// encoder.encode_by_weights(weights, 1);
/// encoder.encode_by_weights(weights, 1);
/// encoder.encode_by_weights(weights, 0);
/// let compressed_data = encoder.finalize();
/// assert_eq!(compressed_data, [0b11111010]);
/// ```
#[derive(Clone)]
pub struct ArithmeticEncoder32 {
    /// Finalized bytes
    encoded: VecDeque<u8>,
    /// Bit mask for the fractoinal
    bit_index: u8,
    current: u8,
    /// Lower bound of the current interval
    a: u64,
    /// Upper bound of the current interval
    b: u64,
    /// Counter for follow bits
    scales: u64,
}

impl ArithmeticEncoder32 {
    pub fn new() -> Self {
        Self {
            encoded: [].into(),
            current: 0,
            bit_index: 0b10000000,
            a: 0,
            b: WHOLE,
            scales: 0,
        }
    }

    /// Pushes a single bit to the output stream.
    /// This is used internally during encoding.
    #[inline]
    fn emit_bit(&mut self, is_one: bool) {
        if is_one {
            self.current |= self.bit_index;
        }

        self.bit_index >>= 1;

        // Check if this bit
        if self.bit_index == 0 {
            self.bit_index = 0b10000000;
            self.encoded.push_back(self.current);
            self.current = 0;
        }
    }

    /// Pushes the current bit followed by a sequence of follow bits.
    ///
    /// The follow bits are determined by the value of `self.scales`.
    /// If `one_follow` is true, it will push a `1` followed by `self.scales` number of `0` bits.
    /// If `one_follow` is false, it will push a `0` followed by `self.scales` number of `1` bits.
    fn push_hot(&mut self, one_hot: bool) {
        self.emit_bit(one_hot);
        while self.scales > 0 {
            self.emit_bit(!one_hot);
            self.scales -= 1;
        }
    }

    /// Encodes a sequence of symbols using the provided sequence model `sm`.
    ///
    /// # Parameters:
    /// - `sequence_model`: The sequence model used for encoding
    /// - `symbols`: An iterable collection of symbols to encode
    pub fn encode<S>(
        &mut self,
        sequence_model: &mut impl SequenceModel<S, u32>,
        symbols: impl IntoIterator<Item = S>,
    ) {
        let mut symbols = symbols.into_iter();

        loop {
            let symbol = symbols.next();
            let is_eof = symbol.is_none();

            let pd = sequence_model.pd();
            let denominator = pd.denominator();
            let Range { start, end } = pd.numerator_range(symbol.as_ref());
            debug_assert!(start < end);
            debug_assert!(end <= denominator);

            self.push_interval(start..end, denominator);
            if is_eof {
                break;
            }
        }
    }

    // TODO: Encode untill pop

    /// Encodes a symbol based on a list of weights and the index of the symbol.
    ///
    /// # Parameters:
    /// - `weights`: A collection of weights corresponding to the probabilities of each symbol
    /// - `symbol_idx`: The index of the symbol to encode
    ///
    /// # Example:
    /// ```
    /// use arithmetify::arith32::ArithmeticEncoder32;
    ///
    /// let mut encoder = ArithmeticEncoder32::new();
    /// let weights = vec![2, 3, 5]; // Probabilities for each symbol
    /// encoder.encode_by_weights(weights, 1); // Encode the second symbol (index 1)
    /// ```
    pub fn encode_by_weights(
        &mut self,
        weights: impl IntoIterator<IntoIter = impl Iterator<Item = u32>>,
        symbol_idx: usize,
    ) {
        let mut weights = weights.into_iter();
        let s = (&mut weights).take(symbol_idx).sum::<u32>();
        let e = s + weights.next().expect(
            "weights should have at least as many elements as symbol_idx",
        );
        let d = e + weights.sum::<u32>();

        self.push_interval(s..e, d)
    }

    #[allow(clippy::assign_op_pattern)]
    fn push_interval(
        &mut self,
        Range { start, end }: Range<u32>,
        denominator: u32,
    ) {
        // Calculate new interval bounds
        let w = self.b - self.a;
        self.b = self.a + w * end as u64 / denominator as u64;
        self.a = self.a + w * start as u64 / denominator as u64;

        // Emit bits and rescale
        // Since a < b is always true, we don't need to compare both against HALF point
        // TODO: We can emit bits even if b is equal to HALF
        // NOTE: Do we rescale even if we don't usinclude HALF
        while self.b < HALF || HALF < self.a {
            self.push_hot(HALF < self.a);

            if HALF < self.a {
                self.a -= HALF;
                self.b -= HALF;
            }

            // Rescale the interval
            self.a *= 2;
            self.b *= 2;
        }

        // E3 scaling
        while QUARTER < self.a && self.b < HALF + QUARTER {
            self.scales += 1;
            self.a *= 2;
            self.b *= 2;

            self.a -= HALF;
            self.b -= HALF;
        }
    }

    pub fn pop_byte(&mut self) -> Option<u8> {
        self.encoded.pop_front()
    }

    /// Finalizes the encoding process and returns the encoded data as a byte stream.
    pub fn finalize(mut self) -> VecDeque<u8> {
        self.scales += 1;

        if QUARTER < self.a {
            self.emit_bit(true);
        } else {
            self.push_hot(false);
        }

        if self.bit_index < 0x80 {
            self.encoded.push_back(self.current)
        }

        self.encoded
    }
}

impl Default for ArithmeticEncoder32 {
    fn default() -> Self {
        Self::new()
    }
}

/// A 32-bit arithmetic decoder that decompresses data based on the encoded bitstream.
///
/// # Example:
/// ```
/// use arithmetify::arith32::ArithmeticDecoder32;
///
/// let weights = [2, 1, 1];
/// let mut decoder = ArithmeticDecoder32::new([0b11111010]);
///
/// assert_eq!(decoder.decode_by_weights(weights), 2);
/// assert_eq!(decoder.decode_by_weights(weights), 2);
/// assert_eq!(decoder.decode_by_weights(weights), 1);
/// assert_eq!(decoder.decode_by_weights(weights), 1);
/// assert_eq!(decoder.decode_by_weights(weights), 0);
/// ```
#[derive(Clone)]
pub struct ArithmeticDecoder32<I> {
    to_decode: I,
    /// Bit mask for the fractoinal
    bit_index: u8,
    current: u8,
    /// Lower bound of the current interval
    a: u64,
    /// Upper bound of the current interval
    b: u64,
    z: u64,
}

impl<I> ArithmeticDecoder32<I>
where
    I: Iterator<Item = u8>,
{
    /// Creates a new `ArithmeticDecoder32` with the given byte stream.
    ///
    /// # Parameters:
    /// - `bytes`: An iterator of bytes that represents the encoded data
    ///
    /// # Example:
    /// ```
    /// use arithmetify::arith32::ArithmeticDecoder32;
    ///
    /// let encoded_data = vec![/* some encoded bytes */];
    /// let mut decoder = ArithmeticDecoder32::new(encoded_data);
    /// ```
    pub fn new(bytes: impl IntoIterator<Item = u8, IntoIter = I>) -> Self {
        let mut z = 0;
        let mut to_decode = bytes.into_iter();

        // Initialize z with the first 32 bits of the encoded data
        for _ in 0..4 {
            z <<= 8;

            if let Some(byte) = to_decode.next() {
                z |= byte as u64;
            }
        }

        Self {
            to_decode,
            current: 0,
            bit_index: 0,
            a: 0,
            b: WHOLE,
            z,
        }
    }

    /// Decodes symbols using the provided sequence model `sm`.
    ///
    /// # Parameters:
    /// - `sequence_model`: A reference to an implementation of `SequenceModel`
    /// ```
    pub fn decode<S>(
        &mut self,
        sequence_model: &mut impl SequenceModel<S, u32>,
    ) {
        loop {
            let pd = sequence_model.pd();
            let denominator = pd.denominator();

            debug_assert!(self.a <= self.z);
            debug_assert!(self.z < self.b);

            // Find the symbol
            let p = (self.z - self.a) * denominator as u64 / (self.b - self.a);
            let symbol = pd.symbol_lookup(p as u32);

            // Update the model
            let Range { start, end } = pd.numerator_range(symbol.as_ref());
            debug_assert!(start < end);
            debug_assert!(end <= denominator);

            self.push_interval(start..end, denominator);

            if let Some(symbol) = symbol {
                sequence_model.push(symbol);
            } else {
                break;
            }
        }
    }

    /// Decodes a symbol based on a list of weights representing symbol probabilities.
    ///
    /// This method uses cumulative weights to determine which symbol corresponds to
    /// the current interval and decodes it.
    ///
    /// # Parameters:
    /// - `weights`: A collection of weights that represent the probabilities for each symbol.
    ///
    /// # Returns:
    /// - The index of the decoded symbol based on the weights.
    ///
    /// # Example:
    /// ```
    /// use arithmetify::arith32::ArithmeticDecoder32;
    ///
    /// let encoded_bytes = [0b_0101_0000]; // Encoded data
    /// let weights = [2, 3, 5]; // Probabilities for each symbol
    ///
    /// let mut decoder = ArithmeticDecoder32::new(encoded_bytes);
    /// let decoded_symbol = decoder.decode_by_weights(weights);
    /// assert_eq!(decoded_symbol, 1); // Decodes to the second symbol (index 1)
    /// ```
    pub fn decode_by_weights(
        &mut self,
        weights: impl IntoIterator<Item = u32>,
    ) -> usize {
        let mut cum_weights = Vec::from_iter(weights);

        for i in 1..cum_weights.len() {
            cum_weights[i] += cum_weights[i - 1];
        }

        let denominator = *cum_weights.last().unwrap();

        let p = (self.z - self.a) * denominator as u64 / (self.b - self.a);
        let symbol_index = match cum_weights.binary_search(&(p as u32)) {
            Ok(index) => index + 1,
            Err(index) => index,
        };

        let start = match symbol_index.checked_sub(1) {
            Some(index) => cum_weights[index],
            None => 0,
        };
        let end = cum_weights[symbol_index];

        self.push_interval(start..end, denominator);

        symbol_index
    }

    fn rescale(&mut self) {
        self.a *= 2;
        self.b *= 2;
        self.z *= 2;

        if self.bit_index == 0 {
            self.bit_index = 0x80;
            self.current = self.to_decode.next().unwrap_or(0);
        }

        if self.bit_index & self.current != 0 {
            self.z += 1;
            debug_assert!(self.z < self.b);
        }

        self.bit_index >>= 1;
    }

    #[allow(clippy::assign_op_pattern)]
    fn push_interval(
        &mut self,
        Range { start, end }: Range<u32>,
        denominator: u32,
    ) {
        // Calculate new interval bounds
        let w = self.b - self.a;
        self.b = self.a + end as u64 * w / denominator as u64;
        self.a = self.a + start as u64 * w / denominator as u64;

        debug_assert!(self.a <= self.z);
        debug_assert!(self.z <= self.b);

        // Emit bits and rescale
        while self.b < HALF || HALF < self.a {
            if HALF < self.a {
                self.a -= HALF;
                self.b -= HALF;
                self.z -= HALF;
            }

            // Rescale the interval
            self.rescale();
        }

        // E3 scaling
        while QUARTER < self.a && self.b < HALF + QUARTER {
            self.rescale();
            self.a -= HALF;
            self.b -= HALF;
            self.z -= HALF;
        }
    }
}

#[cfg(test)]
mod test_arith32;
