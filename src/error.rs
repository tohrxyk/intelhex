/// All possible errors that may occur when processing Intel HEX format
#[derive(Debug)]
pub enum IntelHexError {
    /// Errors that occur during parsing
    Parse(ParseError),
    /// Errors that occur during memory operations
    Memory(MemoryError),
    /// I/O errors
    Io(std::io::Error),
}

/// Errors that can occur while parsing Intel HEX format
#[derive(Debug)]
pub enum ParseError {
    /// Record does not begin with ':'
    MissingStartCode,
    /// Record is shorter than the minimum valid length
    RecordTooShort,
    /// Record exceeds maximum length (255 bytes payload)
    RecordTooLong,
    /// Record length is not even
    RecordNotEvenLength,
    /// Record contains non-hexadecimal characters
    InvalidCharacters,
    /// Checksum verification failed
    ChecksumMismatch(u8, u8),
    /// Actual payload length does not match the declared length
    PayloadLengthMismatch,
    /// Record type is not supported
    UnsupportedRecordType(u8),
    /// Payload length is invalid for the record type
    InvalidLengthForType,
    /// Load offset is invalid
    InvalidLoadOffset,
    /// Multiple start segment/linear address records found
    MultipleStartAddressRecord,
}

/// Errors that can occur during memory operations
#[derive(Debug)]
pub enum MemoryError {
    /// Address already contains data (overlapping addresses found)
    AddressOverlap,
}

// Implement standard error trait
impl std::error::Error for IntelHexError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            IntelHexError::Parse(err) => Some(err),
            IntelHexError::Memory(err) => Some(err),
            IntelHexError::Io(err) => Some(err),
        }
    }
}

impl std::error::Error for ParseError {}
impl std::error::Error for MemoryError {}

// Implement display trait
impl std::fmt::Display for IntelHexError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            IntelHexError::Parse(err) => write!(f, "Parse error: {}", err),
            IntelHexError::Memory(err) => write!(f, "Memory error: {}", err),
            IntelHexError::Io(err) => write!(f, "IO error: {}", err),
        }
    }
}

impl std::fmt::Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ParseError::MissingStartCode => write!(f, "missing start code ':'"),
            ParseError::RecordTooShort => write!(f, "record too short"),
            ParseError::RecordTooLong => write!(f, "record too long"),
            ParseError::RecordNotEvenLength => {
                write!(f, "record does not contain a whole number of bytes")
            }
            ParseError::InvalidCharacters => write!(f, "invalid characters encountered in record"),
            ParseError::ChecksumMismatch(found, expected) => {
                write!(
                    f,
                    "checksum mismatch, found {}, expected {}",
                    found, expected
                )
            }
            ParseError::PayloadLengthMismatch => {
                write!(f, "payload length does not match record header")
            }
            ParseError::UnsupportedRecordType(record_type) => {
                write!(f, "unsupported record type '{:02X}'", record_type)
            }
            ParseError::InvalidLengthForType => write!(f, "payload length invalid for record type"),
            ParseError::InvalidLoadOffset => write!(f, "invalid load offset"),
            ParseError::MultipleStartAddressRecord => {
                write!(f, "multiple start segment/linear address records")
            }
        }
    }
}

impl std::fmt::Display for MemoryError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            MemoryError::AddressOverlap => write!(
                f,
                "address already contains data (overlapping addresses found)"
            ),
        }
    }
}

// Implement error conversions
impl From<std::io::Error> for IntelHexError {
    fn from(err: std::io::Error) -> Self {
        IntelHexError::Io(err)
    }
}

impl From<ParseError> for IntelHexError {
    fn from(err: ParseError) -> Self {
        IntelHexError::Parse(err)
    }
}

impl From<MemoryError> for IntelHexError {
    fn from(err: MemoryError) -> Self {
        IntelHexError::Memory(err)
    }
}
