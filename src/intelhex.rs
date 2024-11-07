use std::collections::BTreeMap;
use std::io::{BufRead, BufReader, BufWriter, Write};

use super::error::{IntelHexError, MemoryError, ParseError};

/// Represents the execution start address in Intel HEX format
#[derive(Debug)]
pub enum ExecutionStartAddress {
    /// Segment address (CS:IP) for 20-bit addressing
    StartSegmentAddress { cs: u16, ip: u16 },
    /// Linear address (EIP) for 32-bit addressing
    StartLinearAddress { eip: u32 },
}

/// Represents a continuous block of memory data
#[derive(Debug)]
pub struct MemoryDataBlock {
    /// Starting address of the memory block
    pub address: u32,
    /// Continuous data bytes stored in this block
    pub data: Vec<u8>,
}

/// Main structure for handling Intel HEX format data
pub struct IntelHex {
    /// Optional execution start address (if specified in the HEX file)
    execution_start_address: Option<ExecutionStartAddress>,
    /// Map of memory addresses to their corresponding data bytes
    memory_data_cells: BTreeMap<u32, u8>,
}

enum AddressMode {
    SegmentAddress(u32),
    LinearAddress(u32),
}

impl IntelHex {
    /// Creates a new empty IntelHex instance
    ///
    /// Initializes a new IntelHex object with:
    /// * An empty memory cells map (no data bytes stored)
    /// * No execution start address
    ///
    /// # Returns
    ///
    /// Returns a new empty IntelHex instance
    ///
    /// # Examples
    ///
    /// ```
    /// use intelhex::IntelHex;
    ///
    /// let intel_hex = IntelHex::new();
    ///
    /// // Memory cells map is empty
    /// assert!(intel_hex.memory_cells().is_empty());
    ///
    /// // No execution start address
    /// assert!(intel_hex.execution_start_address().is_none());
    /// ```
    pub fn new() -> IntelHex {
        Self {
            execution_start_address: None,
            memory_data_cells: BTreeMap::new(),
        }
    }

    /// Returns a reference to the memory cells map
    ///
    /// The memory cells are stored in a BTreeMap where:
    /// * Keys (u32) are memory addresses
    /// * Values (u8) are the data bytes stored at those addresses
    /// * Addresses are automatically sorted in ascending order
    ///
    /// # Returns
    ///
    /// Returns a reference to the BTreeMap containing all memory cells data
    ///
    /// # Examples
    ///
    /// ```
    /// use intelhex::IntelHex;
    ///
    /// let hex_text = ":10010000214601360121470136007EFE09D2190140\n:00000001FF";
    /// let intel_hex = IntelHex::from_intel_hex_text(hex_text).unwrap();
    ///
    /// // Access memory cells
    /// let memory = intel_hex.memory_cells();
    ///
    /// // Check if an address contains data
    /// if let Some(&value) = memory.get(&0x100) {
    ///     println!("Value at 0x100: {:02X}", value);
    /// }
    ///
    /// // Iterate through all memory cells in address order
    /// for (&addr, &value) in memory.iter() {
    ///     println!("Address: {:08X}, Value: {:02X}", addr, value);
    /// }
    /// ```
    pub fn memory_cells(&self) -> &BTreeMap<u32, u8> {
        &self.memory_data_cells
    }

    /// Returns a reference to the execution start address if it exists
    ///
    /// The execution start address can be either a segment address (CS:IP) or
    /// a linear address (EIP), as defined in the Intel HEX format.
    ///
    /// # Returns
    ///
    /// * `Some(&ExecutionStartAddress)` - A reference to the execution start address if it was specified
    /// * `None` - If no execution start address was specified
    ///
    /// # Examples
    ///
    /// ```
    /// use intelhex::IntelHex;
    /// use intelhex::ExecutionStartAddress;
    ///
    /// let hex_text = ":0400000300100020C9\n:00000001FF";  // Contains a start segment address
    /// let intel_hex = IntelHex::from_intel_hex_text(hex_text).unwrap();
    ///
    /// if let Some(start_addr) = intel_hex.execution_start_address() {
    ///     match start_addr {
    ///         ExecutionStartAddress::StartSegmentAddress { cs, ip } => {
    ///             println!("CS:{:04X}, IP:{:04X}", cs, ip)
    ///         },
    ///         ExecutionStartAddress::StartLinearAddress { eip } => {
    ///             println!("EIP:{:08X}", eip)
    ///         },
    ///     }
    /// }
    /// ```
    pub fn execution_start_address(&self) -> Option<&ExecutionStartAddress> {
        self.execution_start_address.as_ref()
    }

    /// Creates an IntelHex instance from a reader
    ///
    /// # Arguments
    ///
    /// * `reader` - Any type that implements the `Read` trait
    ///
    /// # Returns
    ///
    /// * `Ok(IntelHex)` - A new IntelHex instance containing the parsed data
    /// * `Err(IntelHexError)` - If there was an error reading or parsing the data
    ///
    /// # Examples
    ///
    /// ```
    /// use std::fs::File;
    /// use intelhex::IntelHex;
    ///
    /// let file = File::open("tests/fixtures/firmware.hex").unwrap();
    /// let intel_hex = IntelHex::from_reader(file).unwrap();
    /// ```
    pub fn from_reader<R>(reader: R) -> Result<IntelHex, IntelHexError>
    where
        R: std::io::Read,
    {
        let mut intelhex = IntelHex::new();
        let reader = BufReader::new(reader);

        let mut base_address = AddressMode::LinearAddress(0);
        for line in reader.lines() {
            let line = line?;
            if line.is_empty() {
                continue;
            }

            match intelhex.decode_record(&line, &mut base_address) {
                Ok(true) => break,
                Err(error) => return Err(error),
                _ => (),
            }
        }

        Ok(intelhex)
    }

    /// Creates an IntelHex instance from Intel HEX format text
    ///
    /// # Arguments
    ///
    /// * `hex_text` - A string slice containing Intel HEX formatted data
    ///
    /// # Returns
    ///
    /// * `Ok(IntelHex)` - A new IntelHex instance containing the parsed data
    /// * `Err(IntelHexError)` - If the input string is not a valid Intel HEX format
    ///
    /// # Examples
    ///
    /// ```
    /// use intelhex::IntelHex;
    ///
    /// let hex_text = ":10010000214601360121470136007EFE09D2190140\n:00000001FF";
    /// let result = IntelHex::from_intel_hex_text(hex_text).unwrap();
    /// ```
    pub fn from_intel_hex_text(hex_text: &str) -> Result<IntelHex, IntelHexError> {
        Self::from_reader(hex_text.as_bytes())
    }

    /// Decodes a single Intel HEX record line
    ///
    /// # Arguments
    ///
    /// * `line` - A string slice containing a single Intel HEX record
    /// * `base_address` - A mutable reference to the current base address
    ///
    /// # Returns
    ///
    /// * `Ok(bool)` - Returns `true` if this is an End of File record, `false` otherwise
    /// * `Err(IntelHexError)` - If there was an error decoding the record
    ///
    /// # Record Types Supported
    ///
    /// * 00 - Data Record
    /// * 01 - End of File Record
    /// * 02 - Extended Segment Address Record
    /// * 03 - Start Segment Address Record
    /// * 04 - Extended Linear Address Record
    /// * 05 - Start Linear Address Record
    fn decode_record(
        &mut self,
        line: &str,
        base_address: &mut AddressMode,
    ) -> Result<bool, IntelHexError> {
        let mut line_chars_iter = line.chars();

        // Check for start code
        if let Some(':') = line_chars_iter.next() {
        } else {
            return Err(ParseError::MissingStartCode.into());
        }

        // Validate hex characters and length
        let mut hexdigit_length = 0;
        while let Some(c) = line_chars_iter.next() {
            hexdigit_length += 1;
            if !c.is_ascii_hexdigit() {
                return Err(ParseError::InvalidCharacters.into());
            }
        }

        // Validate record length
        if hexdigit_length < ((1 + 2 + 1 + 1) * 2) {
            return Err(ParseError::RecordTooShort.into());
        } else if hexdigit_length > ((1 + 2 + 1 + 255 + 1) * 2) {
            return Err(ParseError::RecordTooLong.into());
        } else if hexdigit_length % 2 != 0 {
            return Err(ParseError::RecordNotEvenLength.into());
        }

        // Convert hex characters to bytes
        let mut record_bytes = Vec::new();
        for i in (1..hexdigit_length).step_by(2) {
            record_bytes.push(u8::from_str_radix(&line[i..i + 2], 16).unwrap());
        }

        // Verify checksum
        let expected_chksum = record_bytes.pop().unwrap();
        let chksum = (0 as u8).wrapping_sub(
            record_bytes
                .iter()
                .fold(0, |acc: u8, x| acc.wrapping_add(*x)),
        );
        if chksum != expected_chksum {
            return Err(ParseError::ChecksumMismatch(chksum, expected_chksum).into());
        }

        // Parse record fields
        let record_length = record_bytes[0] as usize;
        let record_offset = ((record_bytes[1] as u16) << 8) | (record_bytes[2] as u16);
        let record_type = record_bytes[3];
        let record_payload = &record_bytes[4..];

        // Validate payload length
        if record_payload.len() != record_length {
            return Err(ParseError::PayloadLengthMismatch.into());
        }

        // Process record based on type
        match record_type {
            0 => {
                // Data Record
                for i in 0..record_length {
                    let address = match base_address {
                        // Segment addressing mode:
                        // Physical Address = SBA + ([DRLO + DRI] MOD 65536)
                        // where:
                        // - SBA (Segment Base Address) = base
                        // - DRLO (Data Record Load Offset) = record_offset
                        // - DRI (Data Record Index) = i
                        // - MOD 65536 is achieved through u16 wrapping addition
                        AddressMode::SegmentAddress(base) => base
                            .wrapping_add(((record_offset as u16).wrapping_add(i as u16)) as u32),
                        // Linear addressing mode:
                        // Physical Address = Base Address + DRLO + DRI
                        // where:
                        // - Base Address = base (upper 16 bits)
                        // - DRLO (Data Record Load Offset) = record_offset
                        // - DRI (Data Record Index) = i
                        AddressMode::LinearAddress(base) => base
                            .wrapping_add(record_offset as u32)
                            .wrapping_add(i as u32),
                    };
                    if let None = self.memory_data_cells.get(&address) {
                        self.memory_data_cells.insert(address, record_payload[i]);
                    } else {
                        return Err(MemoryError::AddressOverlap.into());
                    }
                }
            }

            1 => {
                // End of File Record
                if record_length != 0 {
                    return Err(ParseError::InvalidLengthForType.into());
                } else if record_offset != 0 {
                    return Err(ParseError::InvalidLoadOffset.into());
                }
                return Ok(true);
            }

            2 => {
                // Extended Segment Address Record
                if record_length != 2 {
                    return Err(ParseError::InvalidLengthForType.into());
                } else if record_offset != 0 {
                    return Err(ParseError::InvalidLoadOffset.into());
                } else {
                    *base_address = AddressMode::SegmentAddress(
                        (((record_payload[0] as u32) << 8) | (record_payload[1] as u32)) << 4,
                    );
                }
            }

            3 => {
                // Start Segment Address Record
                if record_length != 4 {
                    return Err(ParseError::InvalidLengthForType.into());
                } else if record_offset != 0 {
                    return Err(ParseError::InvalidLoadOffset.into());
                } else {
                    let cs: u16 = ((record_payload[0] as u16) << 8) | record_payload[1] as u16;
                    let ip: u16 = ((record_payload[2] as u16) << 8) | record_payload[3] as u16;
                    if let None = self.execution_start_address {
                        self.execution_start_address =
                            Some(ExecutionStartAddress::StartSegmentAddress { cs, ip });
                    } else {
                        return Err(ParseError::MultipleStartAddressRecord.into());
                    }
                }
            }

            4 => {
                // Extended Linear Address Record
                if record_length != 2 {
                    return Err(ParseError::InvalidLengthForType.into());
                } else if record_offset != 0 {
                    return Err(ParseError::InvalidLoadOffset.into());
                } else {
                    *base_address = AddressMode::LinearAddress(
                        (((record_payload[0] as u32) << 8) | (record_payload[1] as u32)) << 16,
                    );
                }
            }

            5 => {
                // Start Linear Address Record
                if record_length != 4 {
                    return Err(ParseError::InvalidLengthForType.into());
                } else if record_offset != 0 {
                    return Err(ParseError::InvalidLoadOffset.into());
                } else {
                    let eip: u32 = ((record_payload[0] as u32) << 24)
                        | ((record_payload[1] as u32) << 16)
                        | ((record_payload[2] as u32) << 8)
                        | record_payload[3] as u32;
                    if let None = self.execution_start_address {
                        self.execution_start_address =
                            Some(ExecutionStartAddress::StartLinearAddress { eip });
                    } else {
                        return Err(ParseError::MultipleStartAddressRecord.into());
                    }
                }
            }

            _ => return Err(ParseError::UnsupportedRecordType(record_type).into()),
        }

        Ok(false)
    }

    /// Writes Intel HEX format data to a writer
    ///
    /// # Arguments
    ///
    /// * `writer` - Any type that implements the `Write` trait
    /// * `data_byte_count` - Number of data bytes per Data Record (1-255).
    ///                       A value of 16 is recommended for general use.
    ///
    /// # Returns
    ///
    /// * `Ok(())` - If the data was successfully written
    /// * `Err(std::io::Error)` - If there was an error writing the data
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use intelhex::IntelHex;
    /// use std::fs::File;
    ///
    /// let intel_hex = IntelHex::new();
    /// let mut file = File::create("output.hex").unwrap();
    /// intel_hex.to_writer(&mut file, 16).unwrap();  // 16 data bytes per data record
    /// ```
    pub fn to_writer<W>(&self, writer: W, data_byte_count: u8) -> Result<(), std::io::Error>
    where
        W: std::io::Write,
    {
        // Since data_byte_count is u8, it's automatically limited to 0-255
        // We only need to check the lower bound (0)
        if data_byte_count == 0 {
            return Err(std::io::Error::new(
                std::io::ErrorKind::InvalidInput,
                "data_byte_count must be between 1 and 255",
            ));
        }

        let mut writer = BufWriter::new(writer);
        let mut is_first = true;
        let mut base_address: u32 = 0;
        let mut continuous_bytes: Vec<u8> = Vec::with_capacity(data_byte_count as usize);
        let mut load_offset = 0;
        let mut last_addr = 0;

        // Write data records
        for (addr, val) in &self.memory_data_cells {
            let mut need_addr_record = false;
            let mut is_addr_continuous = false;

            if is_first {
                base_address = *addr & 0xFFFF0000;
                need_addr_record = true;
                last_addr = *addr;
                is_first = false;
            }

            if *addr - base_address > 0xFFFF {
                need_addr_record = true;
            }

            if *addr == (last_addr + 1) {
                is_addr_continuous = true;
            }

            if (!is_addr_continuous)
                || (continuous_bytes.len() >= data_byte_count as usize)
                || need_addr_record
            {
                if !continuous_bytes.is_empty() {
                    // Data Record
                    let bytes_length = continuous_bytes.len();
                    let mut chksum: u8 = (bytes_length as u8)
                        .wrapping_add((load_offset >> 8) as u8)
                        .wrapping_add(load_offset as u8);

                    write!(writer, ":{:02X}{:04X}00", bytes_length, load_offset)?;

                    for v in &continuous_bytes {
                        chksum = chksum.wrapping_add(*v);
                        write!(writer, "{:02X}", *v)?;
                    }
                    chksum = (0 as u8).wrapping_sub(chksum);

                    #[cfg(windows)]
                    write!(writer, "{:02X}\r\n", chksum)?;
                    #[cfg(not(windows))]
                    write!(writer, "{:02X}\n", chksum)?;

                    continuous_bytes.clear();
                    load_offset = *addr - base_address;
                }
            }

            if need_addr_record {
                base_address = *addr & 0xFFFF0000;
                load_offset = *addr - base_address;

                // Extended Linear Address Record
                let mut chksum: u8 = 2 + 4;
                chksum = chksum.wrapping_add((base_address >> 24) as u8);
                chksum = chksum.wrapping_add((base_address >> 16) as u8);
                chksum = (0 as u8).wrapping_sub(chksum);

                #[cfg(windows)]
                write!(
                    writer,
                    ":02000004{:04X}{:02X}\r\n",
                    base_address >> 16,
                    chksum
                )?;
                #[cfg(not(windows))]
                write!(
                    writer,
                    ":02000004{:04X}{:02X}\n",
                    base_address >> 16,
                    chksum
                )?;
            }

            continuous_bytes.push(*val);
            last_addr = *addr;
        }

        if !continuous_bytes.is_empty() {
            // Data Record
            let bytes_length = continuous_bytes.len();
            let mut chksum: u8 = (bytes_length as u8)
                .wrapping_add((load_offset >> 8) as u8)
                .wrapping_add(load_offset as u8);

            write!(writer, ":{:02X}{:04X}00", bytes_length, load_offset)?;

            for v in &continuous_bytes {
                chksum = chksum.wrapping_add(*v);
                write!(writer, "{:02X}", *v)?;
            }
            chksum = (0 as u8).wrapping_sub(chksum);

            #[cfg(windows)]
            write!(writer, "{:02X}\r\n", chksum)?;
            #[cfg(not(windows))]
            write!(writer, "{:02X}\n", chksum)?;
        }

        // Write execution start address if present
        if let Some(execution_start_address) = &self.execution_start_address {
            match *execution_start_address {
                ExecutionStartAddress::StartSegmentAddress { cs, ip } => {
                    // Start Segment Address Record
                    let mut chksum: u8 = 4 + 3;
                    chksum = chksum.wrapping_add((cs >> 8) as u8);
                    chksum = chksum.wrapping_add(cs as u8);
                    chksum = chksum.wrapping_add((ip >> 8) as u8);
                    chksum = chksum.wrapping_add(ip as u8);
                    chksum = (0 as u8).wrapping_sub(chksum);

                    #[cfg(windows)]
                    write!(writer, ":04000003{:04X}{:04X}{:02X}\r\n", cs, ip, chksum)?;
                    #[cfg(not(windows))]
                    write!(writer, ":04000003{:04X}{:04X}{:02X}\n", cs, ip, chksum)?;
                }

                ExecutionStartAddress::StartLinearAddress { eip } => {
                    // Start Linear Address Record
                    let mut chksum: u8 = 4 + 5;
                    chksum = chksum.wrapping_add((eip >> 24) as u8);
                    chksum = chksum.wrapping_add((eip >> 16) as u8);
                    chksum = chksum.wrapping_add((eip >> 8) as u8);
                    chksum = chksum.wrapping_add(eip as u8);
                    chksum = (0 as u8).wrapping_sub(chksum);

                    #[cfg(windows)]
                    write!(writer, ":04000005{:08X}{:02X}\r\n", eip, chksum)?;
                    #[cfg(not(windows))]
                    write!(writer, ":04000005{:08X}{:02X}\n", eip, chksum)?;
                }
            }
        }

        // End of File Record
        #[cfg(windows)]
        write!(writer, ":00000001FF\r\n")?;
        #[cfg(not(windows))]
        write!(writer, ":00000001FF\n")?;
        writer.flush()?;

        Ok(())
    }

    /// Converts the IntelHex object to Intel HEX format text
    ///
    /// # Returns
    ///
    /// * `Ok(String)` - A string containing the Intel HEX formatted data
    /// * `Err(std::io::Error)` - If there was an error writing the data
    pub fn to_intel_hex_text(&self) -> Result<String, std::io::Error> {
        let mut buf: Vec<u8> = Vec::new();
        self.to_writer(&mut buf, 16)?;
        Ok(String::from_utf8(buf).unwrap())
    }

    /// Converts memory data into a collection of continuous data blocks
    ///
    /// # Returns
    ///
    /// Returns a vector of MemoryDataBlock, each containing:
    /// * address: Starting address of the data block
    /// * data: Vector of continuous data bytes
    pub fn memory_blocks(&self) -> Vec<MemoryDataBlock> {
        let mut blocks = Vec::new();
        if self.memory_data_cells.is_empty() {
            return blocks;
        }

        let mut current_block = MemoryDataBlock {
            address: 0,
            data: Vec::new(),
        };
        let mut last_address: Option<u32> = None;

        for (&address, &value) in &self.memory_data_cells {
            match last_address {
                None => {
                    // First data point
                    current_block.address = address;
                    current_block.data.push(value);
                }
                Some(last_addr) => {
                    if address == last_addr + 1 {
                        // Continuous address
                        current_block.data.push(value);
                    } else {
                        // Discontinuous address, create new block
                        blocks.push(std::mem::replace(
                            &mut current_block,
                            MemoryDataBlock {
                                address,
                                data: vec![value],
                            },
                        ));
                    }
                }
            }
            last_address = Some(address);
        }

        // Add the last block
        if !current_block.data.is_empty() {
            blocks.push(current_block);
        }

        blocks
    }

    /// Adds data from a MemoryDataBlock to the memory cells
    ///
    /// # Arguments
    ///
    /// * `block` - The MemoryDataBlock containing address and data to add
    ///
    /// # Returns
    ///
    /// * `Ok(())` - If the data was successfully added
    /// * `Err(IntelHexError)` - If there was an error adding the data
    ///
    /// # Examples
    ///
    /// ```
    /// use intelhex::{IntelHex, MemoryDataBlock};
    ///
    /// let mut intel_hex = IntelHex::new();
    /// let block = MemoryDataBlock {
    ///     address: 0x1000,
    ///     data: vec![0x12, 0x34, 0x56],
    /// };
    ///
    /// // Add the memory block
    /// intel_hex.add_memory_block(&block).unwrap();
    ///
    /// // Verify the data was added
    /// let memory = intel_hex.memory_cells();
    /// assert_eq!(memory.get(&0x1000), Some(&0x12));
    /// assert_eq!(memory.get(&0x1001), Some(&0x34));
    /// assert_eq!(memory.get(&0x1002), Some(&0x56));
    /// ```
    pub fn add_memory_block(&mut self, block: &MemoryDataBlock) -> Result<(), IntelHexError> {
        // Check for address overlap before adding any data
        for i in 0..block.data.len() {
            let address = block.address.wrapping_add(i as u32);
            if self.memory_data_cells.contains_key(&address) {
                return Err(MemoryError::AddressOverlap.into());
            }
        }

        // Add all data bytes to memory cells
        for (i, &value) in block.data.iter().enumerate() {
            let address = block.address.wrapping_add(i as u32);
            self.memory_data_cells.insert(address, value);
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // Test helper function to create a simple IntelHex instance with test data
    fn create_test_hex() -> IntelHex {
        let hex_text = "\
            :10010000214601360121470136007EFE09D2190140\n\
            :100110002146017EB7C20001FF5F16002148011988\n\
            :00000001FF";
        IntelHex::from_intel_hex_text(hex_text).unwrap()
    }

    #[test]
    fn test_new() {
        // Test creating a new empty IntelHex instance
        let hex = IntelHex::new();
        assert!(hex.memory_cells().is_empty());
        assert!(hex.execution_start_address().is_none());
    }

    #[test]
    fn test_basic_parsing() {
        let hex = create_test_hex();
        let memory = hex.memory_cells();

        // Verify first data record was parsed correctly
        assert_eq!(memory.get(&0x0100), Some(&0x21));
        assert_eq!(memory.get(&0x0101), Some(&0x46));

        // Verify second data record was parsed correctly
        assert_eq!(memory.get(&0x0110), Some(&0x21));
        assert_eq!(memory.get(&0x0111), Some(&0x46));
    }

    #[test]
    fn test_start_segment_address() {
        // Test parsing of Start Segment Address Record
        let hex_text = ":0400000300100020C9\n:00000001FF";
        let hex = IntelHex::from_intel_hex_text(hex_text).unwrap();

        match hex.execution_start_address().unwrap() {
            ExecutionStartAddress::StartSegmentAddress { cs, ip } => {
                assert_eq!(*cs, 0x0010);
                assert_eq!(*ip, 0x0020);
            }
            _ => panic!("Wrong execution start address type"),
        }
    }

    #[test]
    fn test_start_linear_address() {
        // Test parsing of Start Linear Address Record
        let hex_text = ":0400000512345678E3\n:00000001FF";
        let hex = IntelHex::from_intel_hex_text(hex_text).unwrap();

        match hex.execution_start_address().unwrap() {
            ExecutionStartAddress::StartLinearAddress { eip } => {
                assert_eq!(*eip, 0x12345678);
            }
            _ => panic!("Wrong execution start address type"),
        }
    }

    #[test]
    fn test_extended_segment_address() {
        // Test parsing with Extended Segment Address Record
        let hex_text = "\
            :020000021000EC\n\
            :10010000214601360121470136007EFE09D2190140\n\
            :00000001FF";
        let hex = IntelHex::from_intel_hex_text(hex_text).unwrap();
        let memory = hex.memory_cells();

        // Base address should be 0x10000 + offset
        assert_eq!(memory.get(&0x10100), Some(&0x21));
        assert_eq!(memory.get(&0x10101), Some(&0x46));
    }

    #[test]
    fn test_extended_linear_address() {
        // Test parsing with Extended Linear Address Record
        let hex_text = "\
            :02000004FFFFFC\n\
            :10010000214601360121470136007EFE09D2190140\n\
            :00000001FF";
        let hex = IntelHex::from_intel_hex_text(hex_text).unwrap();
        let memory = hex.memory_cells();

        // Base address should be 0xFFFF0000 + offset
        assert_eq!(memory.get(&0xFFFF0100), Some(&0x21));
        assert_eq!(memory.get(&0xFFFF0101), Some(&0x46));
    }

    #[test]
    fn test_memory_blocks() {
        let mut hex = IntelHex::new();

        // Add discontinuous memory blocks
        let block1 = MemoryDataBlock {
            address: 0x1000,
            data: vec![0x11, 0x22, 0x33],
        };
        let block2 = MemoryDataBlock {
            address: 0x2000,
            data: vec![0x44, 0x55],
        };

        hex.add_memory_block(&block1).unwrap();
        hex.add_memory_block(&block2).unwrap();

        let blocks = hex.memory_blocks();
        assert_eq!(blocks.len(), 2);

        // Verify first block
        assert_eq!(blocks[0].address, 0x1000);
        assert_eq!(blocks[0].data, vec![0x11, 0x22, 0x33]);

        // Verify second block
        assert_eq!(blocks[1].address, 0x2000);
        assert_eq!(blocks[1].data, vec![0x44, 0x55]);
    }

    #[test]
    fn test_error_handling() {
        // Test invalid start code
        let result = IntelHex::from_intel_hex_text("10010000214601360121470136007EFE09D2190140");
        assert!(matches!(
            result,
            Err(IntelHexError::Parse(ParseError::MissingStartCode))
        ));

        // Test invalid checksum
        let result = IntelHex::from_intel_hex_text(":10010000214601360121470136007EFE09D2190141");
        assert!(matches!(
            result,
            Err(IntelHexError::Parse(ParseError::ChecksumMismatch(_, _)))
        ));

        // Test address overlap
        let mut hex = IntelHex::new();
        let block1 = MemoryDataBlock {
            address: 0x1000,
            data: vec![0x11, 0x22],
        };
        let block2 = MemoryDataBlock {
            address: 0x1001,
            data: vec![0x33, 0x44],
        };

        hex.add_memory_block(&block1).unwrap();
        assert!(matches!(
            hex.add_memory_block(&block2),
            Err(IntelHexError::Memory(MemoryError::AddressOverlap))
        ));
    }
}
