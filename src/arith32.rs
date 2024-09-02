use std::{collections::VecDeque, fmt::Debug, ops::Range};

use super::SequenceModel;
use crate::Distribution as _;

const WHOLE: u64 = 0x1_0000_0000_u64;
const HALF: u64 = WHOLE / 2;
const QUARTER: u64 = HALF / 2;

pub struct ArithmeticEncoder32 {
    /// Finalized bytes
    encoded: VecDeque<u8>,
    /// Bit mask for the fractoinal
    bit: u8,
    current: u8,
    /// Lower bound of the current interval
    a: u64,
    /// Upper bound of the current interval
    b: u64,
    /// Counter for follow bits
    scales: u32,
}

impl ArithmeticEncoder32 {
    pub fn new() -> Self {
        Self {
            encoded: [].into(),
            current: 0,
            bit: 0x80,
            a: 0,
            b: WHOLE,
            scales: 0,
        }
    }

    fn push_bit(&mut self, is_one: bool) {
        if is_one {
            self.current |= self.bit;
        }

        self.bit >>= 1;

        if self.bit == 0 {
            self.bit = 0x80;
            self.encoded.push_back(self.current);
            self.current = 0;
        }
    }

    fn push_hot(&mut self, one_hot: bool) {
        self.push_bit(one_hot);
        while self.scales > 0 {
            self.push_bit(!one_hot);
            self.scales -= 1;
        }
    }

    pub fn encode<S>(
        &mut self,
        sm: &mut impl SequenceModel<S, u32>,
        symbols: impl IntoIterator<Item = S>,
    ) {
        let mut symbols = symbols.into_iter();
        let mut remaining = true;

        while remaining {
            let symbol = symbols.next();
            remaining = symbol.is_some();

            let pd = sm.pd();
            let denominator = pd.denominator();
            let Range { start, end } = pd.numerator_range(symbol.as_ref());
            debug_assert!(start < end);
            debug_assert!(end <= denominator);

            self.encode_interval(start as u64..end as u64, denominator as u64);
        }
    }

    fn encode_interval(&mut self, Range { start, end }: Range<u64>, denominator: u64) {
        // Calculate new interval bounds
        let w = self.b - self.a;
        self.b = self.a + w * end / denominator;
        self.a = self.a + w * start / denominator;

        // Emit bits and rescale
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

    pub fn finalyze(mut self) -> VecDeque<u8> {
        self.scales += 1;
        self.push_hot(QUARTER < self.a);

        if self.bit < 0x80 {
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

pub struct ArithmeticDecoder32<I> {
    to_decode: I,
    /// Bit mask for the fractoinal
    bit: u8,
    current: u8,
    /// Lower bound of the current interval
    a: u64,
    /// Upper bound of the current interval
    b: u64,
    /// Counter for follow bits
    scales: u32,
    z: u64,
}

impl<I> ArithmeticDecoder32<I>
where
    I: Iterator<Item = u8>,
{
    pub fn new(bytes: impl IntoIterator<Item = u8, IntoIter = I>) -> Self {
        let mut z = 0;
        let mut to_decode = bytes.into_iter();

        // Initialize z with the first 32 bits of the encoded data
        for _ in 0..4 {
            z <<= 8;

            let byte = to_decode.next().unwrap_or(0);
            z |= byte as u64;
        }

        Self {
            to_decode,
            current: 0,
            bit: 0,
            a: 0,
            b: WHOLE,
            z,
            scales: 0,
        }
    }

    pub fn decode<S>(&mut self, sm: &mut impl SequenceModel<S, u32>)
    where
        // TODO: Remove
        S: Debug,
    {
        loop {
            let pd = sm.pd();
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

            self.encode_interval(start as u64..end as u64, denominator as u64);

            if let Some(symbol) = symbol {
                sm.push(symbol);
            } else {
                break;
            }
        }
    }

    fn rescale(&mut self) {
        self.a *= 2;
        self.b *= 2;
        self.z *= 2;

        debug_assert!(self.a <= self.z);
        debug_assert!(self.z < self.b);

        if self.bit == 0 {
            self.bit = 0x80;
            self.current = self.to_decode.next().unwrap_or(0);
        }

        debug_assert!(self.bit > 0);

        if self.bit & self.current != 0 {
            self.z += 1;
            debug_assert!(self.a <= self.z);
            debug_assert!(self.z < self.b);
        }

        self.bit >>= 1;
    }

    fn encode_interval(&mut self, Range { start, end }: Range<u64>, denominator: u64) {
        // Calculate new interval bounds
        debug_assert!(self.a <= self.z);
        debug_assert!(self.z < self.b);

        debug_assert!(start < end);
        debug_assert!(end <= denominator);

        let w = self.b - self.a;
        self.b = self.a + end * w / denominator;
        self.a = self.a + start * w / denominator;

        debug_assert!(self.a <= self.z);
        debug_assert!(self.z < self.b);

        // Emit bits and rescale
        while self.b < HALF || HALF < self.a {
            if HALF < self.a {
                self.subtract_half();
            }

            // Rescale the interval
            self.rescale();
        }

        // E3 scaling
        while QUARTER < self.a && self.b < HALF + QUARTER {
            self.scales += 1;
            self.rescale();
            self.subtract_half();
        }
    }

    fn subtract_half(&mut self) {
        self.a -= HALF;
        self.b -= HALF;
        self.z -= HALF;
    }
}

#[cfg(test)]
mod test_arith32;
