extern crate byteorder;

use std::error;
use std::fmt;
use std::io;
use std::io::{Read, Seek, SeekFrom};
use std::result;

use byteorder::{LittleEndian, ReadBytesExt};

// MARK: Error types

/// Represents an error that occurred while reading a wave file.
#[derive(Debug)]
pub enum ReadError {
    /// The file format is incorrect or unsupported.
    Format(FormatErrorKind),
    /// An IO error occurred.
    Io(io::Error),
}

/// Represents a result when reading a wave file.
pub type ReadResult<T> = result::Result<T, ReadError>;

impl fmt::Display for ReadError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            ReadError::Format(ref err_kind) => write!(f, "Format error: {}", err_kind),
            ReadError::Io(ref err) => write!(f, "IO error: {}", err),
        }
    }
}

/// Represents a file format error, when the wave file is incorrect or unsupported.
#[derive(Debug)]
pub enum FormatErrorKind {
    /// The file does not start with a "RIFF" tag and chunk size.
    NotARiffFile,
    /// The file doesn't continue with "WAVE" after the RIFF chunk header.
    NotAWaveFile,
}

impl FormatErrorKind {
    fn to_string(&self) -> &str {
        match *self {
            FormatErrorKind::NotARiffFile => "not a RIFF file",
            FormatErrorKind::NotAWaveFile => "not a WAVE file",
        }
    }
}

impl fmt::Display for FormatErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.to_string())
    }
}

impl error::Error for ReadError {
    fn description(&self) -> &str {
        match *self {
            ReadError::Format(ref kind) => kind.to_string(),
            ReadError::Io(ref err) => err.description(),
        }
    }

    fn cause(&self) -> Option<&error::Error> {
        match *self {
            ReadError::Format(_) => None,
            ReadError::Io(ref err) => Some(err),
        }
    }
}

impl From<io::Error> for ReadError {
    fn from(err: io::Error) -> ReadError {
        ReadError::Io(err)
    }
}

// MARK: Validation and parsing functions

trait WaveReader: Read + Seek {
    fn validate_is_riff_file(&mut self) -> ReadResult<()> {
        try!(self.validate_tag(b"RIFF", FormatErrorKind::NotARiffFile));
        // The next four bytes represent the chunk size. We're not going to
        // validate it, so that we can still try to read files that might have
        // an incorrect chunk size, so let's skip over it.
        let _ = try!(self.read_chunk_size());
        Ok(())
    }

    fn validate_is_wave_file(&mut self) -> ReadResult<()> {
        try!(self.validate_tag(b"WAVE", FormatErrorKind::NotAWaveFile));
        Ok(())
    }

    fn validate_tag(&mut self,
                    expected_tag: &[u8; 4],
                    err_kind: FormatErrorKind)
                    -> ReadResult<()> {
        let tag = try!(self.read_tag());
        if &tag != expected_tag {
            return Err(ReadError::Format(err_kind));
        }
        Ok(())
    }

    fn skip_until_subchunk(&mut self, matching_tag: &[u8; 4]) -> ReadResult<u32> {
        loop {
            let tag = try!(self.read_tag());
            let subchunk_size = try!(self.read_chunk_size());

            if &tag == matching_tag {
                return Ok(subchunk_size);
            } else {
                try!(self.seek(SeekFrom::Current(subchunk_size.into())));
            }
        }
    }

    fn read_tag(&mut self) -> ReadResult<[u8; 4]> {
        let mut tag: [u8; 4] = [0; 4];
        try!(self.read_exact(&mut tag));
        Ok(tag)
    }

    fn read_chunk_size(&mut self) -> ReadResult<u32> {
        Ok(try!(self.read_u32::<LittleEndian>()))
    }
}

impl<T> WaveReader for T where T: Read + Seek {}

// MARK: Tests

#[cfg(test)]
mod tests {
    use std::io::Cursor;

    use {FormatErrorKind, ReadError, WaveReader};

    // This is a helper macro that helps us validate results in our tests.
    // Thank you bluss and durka42!
    macro_rules! assert_matches {
        ($expected:pat $(if $guard:expr)*, $value:expr) => {
            match $value {
                $expected $(if $guard)* => {},
                ref actual => {
                    panic!("assertion failed: `(left matches right)` (left: `{}`, right: `{:?}`",
                        stringify!($expected), actual);
                },
            }
        };
    }

    // RIFF header tests

    #[test]
    fn test_validate_is_riff_file_ok() {
        let mut data = Cursor::new(b"RIFF    ");
        assert_matches!(Ok(()), data.validate_is_riff_file());
    }

    #[test]
    fn test_validate_is_riff_file_err_incomplete() {
        let mut data = Cursor::new(b"RIF     ");
        assert_matches!(Err(ReadError::Format(FormatErrorKind::NotARiffFile)),
                        data.validate_is_riff_file());
    }

    #[test]
    fn test_validate_is_riff_file_err_something_else() {
        let mut data = Cursor::new(b"JPEG     ");
        assert_matches!(Err(ReadError::Format(FormatErrorKind::NotARiffFile)),
                        data.validate_is_riff_file());
    }

    // Wave tag tests

    #[test]
    fn test_validate_is_wave_file_ok() {
        let mut data = Cursor::new(b"WAVE");
        assert_matches!(Ok(()), data.validate_is_wave_file());
    }

    #[test]
    fn test_validate_is_wave_file_err_incomplete() {
        let mut data = Cursor::new(b"WAV ");
        assert_matches!(Err(ReadError::Format(FormatErrorKind::NotAWaveFile)),
                        data.validate_is_wave_file());
    }

    #[test]
    fn test_validate_is_wave_file_err_something_else() {
        let mut data = Cursor::new(b"JPEG");
        assert_matches!(Err(ReadError::Format(FormatErrorKind::NotAWaveFile)),
                        data.validate_is_wave_file());
    }

    // Skipping to subchunk tests
    // After reading in the file header, we also need to read in the "fmt " subchunk.
    // The file might contain other subchunks that we don't currently support, so
    // we'll need to skip over them.

    #[test]
    fn test_skip_until_subchunk() {
        // A size of 0.
        let mut data = Cursor::new(b"RIFF    WAVEfmt \x00\x00\x00\x00");
        let _ = data.validate_is_riff_file();
        let _ = data.validate_is_wave_file();
        let size = data.skip_until_subchunk(b"fmt ");
        assert_eq!(0, size.unwrap());
    }

    #[test]
    fn test_skip_until_second_subchunk() {
        // A size of 0.
        let mut data = Cursor::new(b"RIFF    WAVEfmt \x00\x00\x00\x00data\x00\x00\x00\x00");
        let _ = data.validate_is_riff_file();
        let _ = data.validate_is_wave_file();
        let _ = data.skip_until_subchunk(b"fmt ");
        let size = data.skip_until_subchunk(b"data");
        assert_eq!(0, size.unwrap());
    }

    #[test]
    #[should_panic]
    fn test_cant_read_first_subchunk_after_second() {
        // A size of 0.
        let mut data = Cursor::new(b"RIFF    WAVEdata\x00\x00\x00\x00fmt \x00\x00\x00\x00");
        let _ = data.validate_is_riff_file();
        let _ = data.validate_is_wave_file();
        let _ = data.skip_until_subchunk(b"fmt ");
        let size = data.skip_until_subchunk(b"data");
        assert_eq!(0, size.unwrap());
    }
}
