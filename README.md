# Intel HEX Format Parser/Writer

A robust Rust library for parsing and writing Intel HEX format files. This library provides a safe and efficient way to handle Intel HEX format data, commonly used in embedded systems programming.

## Installation

Add this to your Cargo.toml:

```toml
[dependencies]
intelhex = "0.1.0"
```

## Usage

### Basic Example

```rust
use intelhex::IntelHex;

// Parse Intel HEX format text
let hex_text = ":10010000214601360121470136007EFE09D2190140\n:00000001FF";
let intel_hex = IntelHex::from_intel_hex_text(hex_text).unwrap();

// Access memory contents
let memory = intel_hex.memory_cells();
if let Some(&value) = memory.get(&0x0100) {
    println!("Value at 0x100: {:02X}", value);
}

// Write back to Intel HEX format
let output = intel_hex.to_intel_hex_text().unwrap();
```

### Working with Memory Blocks

```rust
use intelhex::{IntelHex, MemoryDataBlock};

let mut intel_hex = IntelHex::new();

// Add a memory block
let block = MemoryDataBlock {
    address: 0x1000,
    data: vec![0x12, 0x34, 0x56],
};
intel_hex.add_memory_block(&block).unwrap();

// Get continuous memory blocks
let blocks = intel_hex.memory_blocks();
for block in blocks {
    println!("Block at {:08X}, length: {}", block.address, block.data.len());
}
```

### File I/O

```rust
use std::fs::File;
use intelhex::IntelHex;

// Read from file
let file = File::open("firmware.hex").unwrap();
let intel_hex = IntelHex::from_reader(file).unwrap();

// Write to file
let output = File::create("output.hex").unwrap();
intel_hex.to_writer(output, 16).unwrap();  // 16 bytes per data record
```


## Documentation

For detailed API documentation, run:

```bash
cargo doc --open
```


## Testing

Run the test suite with:

```bash
cargo test
```

## License

This project is licensed under the MIT License. See the [LICENSE](LICENSE) file for details.

## Contributing

We welcome contributions to improve the library. Please feel free to submit a Pull Request.
