use intelhex::{ExecutionStartAddress, IntelHex, MemoryDataBlock};
use std::io::Cursor;

// Test reading and writing Intel HEX format
#[test]
fn test_read_write_roundtrip() {
    // Create test data
    let original_hex = "\
        :10010000214601360121470136007EFE09D2190140\n\
        :100110002146017EB7C20001FF5F16002148011988\n\
        :00000001FF";

    // Read the test data
    let hex = IntelHex::from_intel_hex_text(original_hex).unwrap();

    // Write it back to string
    let output = hex.to_intel_hex_text().unwrap();

    // Read the output again
    let hex2 = IntelHex::from_intel_hex_text(&output).unwrap();

    // Compare memory contents
    assert_eq!(hex.memory_cells(), hex2.memory_cells());
}

// Test reading from a reader
#[test]
fn test_reader_interface() {
    let data = ":10010000214601360121470136007EFE09D2190140\n:00000001FF";
    let cursor = Cursor::new(data);

    let hex = IntelHex::from_reader(cursor).unwrap();
    assert_eq!(hex.memory_cells().get(&0x0100), Some(&0x21));
}

// Test writing to a writer
#[test]
fn test_writer_interface() {
    let mut hex = IntelHex::new();
    let block = MemoryDataBlock {
        address: 0x0100,
        data: vec![0x21, 0x46, 0x01],
    };
    hex.add_memory_block(&block).unwrap();

    let mut output = Vec::new();
    hex.to_writer(&mut output, 16).unwrap();

    let output_str = String::from_utf8(output).unwrap();
    assert!(output_str.contains(":03010000214601"));
}

// Test handling of large files
#[test]
fn test_large_file_handling() {
    let mut hex = IntelHex::new();

    // Create a large memory block (64KB)
    let mut data = Vec::with_capacity(65536);
    for i in 0..=65535u16 {
        data.push(i as u8);
    }

    let block = MemoryDataBlock { address: 0, data };
    hex.add_memory_block(&block).unwrap();

    // Write to memory and read back
    let output = hex.to_intel_hex_text().unwrap();
    let hex2 = IntelHex::from_intel_hex_text(&output).unwrap();

    assert_eq!(hex.memory_cells(), hex2.memory_cells());
}

// Test execution start address handling
#[test]
fn test_execution_start_address() {
    let mut hex = IntelHex::new();

    // Add some data
    let block = MemoryDataBlock {
        address: 0x1000,
        data: vec![0x11, 0x22, 0x33],
    };
    hex.add_memory_block(&block).unwrap();

    // Write to string
    let output = hex.to_intel_hex_text().unwrap();

    // Read back and verify no execution start address
    let hex2 = IntelHex::from_intel_hex_text(&output).unwrap();
    assert!(hex2.execution_start_address().is_none());

    // Test with start segment address
    let hex_with_start = "\
        :10010000214601360121470136007EFE09D2190140\n\
        :0400000300100020C9\n\
        :00000001FF";

    let hex3 = IntelHex::from_intel_hex_text(hex_with_start).unwrap();
    match hex3.execution_start_address().unwrap() {
        ExecutionStartAddress::StartSegmentAddress { cs, ip } => {
            assert_eq!(*cs, 0x0010);
            assert_eq!(*ip, 0x0020);
        }
        _ => panic!("Wrong execution start address type"),
    }
}

// Test error conditions in real file scenarios
#[test]
fn test_error_conditions() {
    // Test empty file
    let result = IntelHex::from_intel_hex_text("");
    assert!(result.is_ok());

    // Test file with only EOF record
    let result = IntelHex::from_intel_hex_text(":00000001FF");
    assert!(result.is_ok());

    // Test invalid record type
    let result = IntelHex::from_intel_hex_text(":0200000699FFFF");
    assert!(result.is_err());
}
