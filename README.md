## arithmetify

A simple implementation of arithmetic coding in Rust.

### Features

- Efficient entropy coding using arithmetic coding.
- Customizable distribution models.
- Simple API for encoding and decoding sequences.

### Installation

Add `arithmetify` to your `Cargo.toml`:

```toml
[dependencies]
arithmetify = "0.1.0"
```

### Usage

Here is a simple example demonstrating how to use `arithmetify` to encode and decode a sequence:

```rust
use arithmetify::{ArithmeticEncoder, ArithmeticDecoder};

fn main() {
    // Define symbol weights representing their probabilities.
    let weights = [2, 4, 6, 8];
    
    // The input sequence to be encoded.
    let input = [1, 1, 2, 3, 2, 1, 0];

    // Initialize the arithmetic encoder.
    let mut encoder = ArithmeticEncoder::new();
    
    // Encode each symbol in the input sequence using the defined weights.
    for &symbol in &input {
        encoder.encode_by_weights(weights, symbol);
    }

    // Finalize the encoding process and get the compressed data.
    let compressed = encoder.finalize();

    // Initialize the arithmetic decoder with the compressed data.
    let mut decoder = ArithmeticDecoder::new(compressed);

    // Decode the compressed data back into a sequence.
    let mut decoded = vec![];
    loop {
        let symbol = decoder.decode_by_weights(weights);
        decoded.push(symbol);
        if symbol == 0 { // Assuming 0 as a termination symbol for this example.
            break;
        }
    }

    // Verify that the decoded sequence matches the original input.
    assert_eq!(input, decoded.as_slice());
}
```
