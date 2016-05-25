// riff-wave -- Basic support for reading and writing wave PCM files.
// Copyright (c) 2016 Kevin Brothaler and the riff-wave project authors.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// A copy of the License has been included in the root of the repository.
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use std::error;
use std::fmt;
use std::io;
use std::io::{Seek, Write};
use std::result;

use super::{PcmFormat};

// MARK: Error types

#[derive(Debug)]
pub enum WriteError {
    /// The file format is incorrect or unsupported.
    Format(WriteErrorKind),
    /// An IO error occurred.
    Io(io::Error),
}

/// Represents a result when reading a wave file.
pub type WriteResult<T> = result::Result<T, WriteError>;

impl fmt::Display for WriteError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            WriteError::Format(ref err_kind) => write!(f, "Format error: {}", err_kind),
            WriteError::Io(ref err) => write!(f, "IO error: {}", err),
        }
    }
}

/// Represents a file format error, when incorrect parameters have been specified.
#[derive(Debug)]
pub enum WriteErrorKind {    
    /// The number of channels is zero, which is invalid.
    NumChannelsIsZero,
    /// The sample rate is zero, which is invalid.
    SampleRateIsZero,
    /// Only 8-bit, 16-bit, 24-bit and 32-bit PCM files are supported.
    UnsupportedBitsPerSample(u16),    
}

impl WriteErrorKind {
    fn to_string(&self) -> &str {
        match *self {            
            WriteErrorKind::NumChannelsIsZero => "Number of channels is zero",
            WriteErrorKind::SampleRateIsZero => "Sample rate is zero",
            WriteErrorKind::UnsupportedBitsPerSample(_) => "Unsupported bits per sample",            
        }
    }
}

impl fmt::Display for WriteErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.to_string())
    }
}

impl error::Error for WriteError {
    fn description(&self) -> &str {
        match *self {
            WriteError::Format(ref kind) => kind.to_string(),
            WriteError::Io(ref err) => err.description(),
        }
    }

    fn cause(&self) -> Option<&error::Error> {
        match *self {
            WriteError::Format(_) => None,
            WriteError::Io(ref err) => Some(err),
        }
    }
}

impl From<io::Error> for WriteError {
    fn from(err: io::Error) -> WriteError {
        WriteError::Io(err)
    }
}

// MARK: Writing functions

/// Helper struct that takes ownership of a writer and can be used to write data
/// to a PCM wave file.
#[derive(Debug)]
pub struct WaveWriter<T>
    where T: Seek + Write
{
    ///  Represents the PCM format for this wave file.
    pub pcm_format: PcmFormat,

    // The underlying writer that we'll use to read data.
    writer: T,
}

// TODO what should we do if an incorrect write_* method is called? Return the error in the result?
impl<T> WaveWriter<T>
    where T: Seek + Write
{
    /// Returns a new wave writer for the given writer.
    pub fn new(num_channels: u16, sample_rate: u32, bits_per_sample: u16, mut writer: T) -> WriteResult<WaveWriter<T>> {
    	if num_channels == 0 {
    		return Err(WriteError::Format(WriteErrorKind::NumChannelsIsZero));
    	} else if sample_rate == 0 {
    		return Err(WriteError::Format(WriteErrorKind::SampleRateIsZero));
    	} else if bits_per_sample != 8 && bits_per_sample != 16 
        	   && bits_per_sample != 24 && bits_per_sample != 32 {
    	   	return Err(WriteError::Format(WriteErrorKind::UnsupportedBitsPerSample(bits_per_sample)));
	   	}

        let pcm_format = PcmFormat { num_channels: num_channels, sample_rate: sample_rate, bits_per_sample: bits_per_sample};
        
        Ok(WaveWriter {
            pcm_format: pcm_format,
            writer: writer,
        })
    }

/*
    /// Reads a single sample as an unsigned 8-bit value.
    pub fn read_sample_u8(&mut self) -> io::Result<u8> {
        self.read_sample(|reader| reader.read_u8())
    }

    /// Reads a single sample as a signed 16-bit value.
    pub fn read_sample_i16(&mut self) -> io::Result<i16> {
        self.read_sample(|reader| reader.read_i16::<LittleEndian>())
    }

    /// Reads a single sample as a signed 24-bit value. The value will be padded
    /// to fit in a 32-bit buffer.
    pub fn read_sample_i24(&mut self) -> io::Result<i32> {
        self.read_sample(|reader| reader.read_int::<LittleEndian>(3)).map(|x| x as i32)
    }

    /// Reads a single sample as a signed 32-bit value.
    pub fn read_sample_i32(&mut self) -> io::Result<i32> {
        self.read_sample(|reader| reader.read_i32::<LittleEndian>())
    }

    fn read_sample<F, S>(&mut self, read_data: F) -> io::Result<S>
        where F: Fn(&mut T) -> io::Result<S>
    {
        Ok(try!(read_data(&mut self.reader)))
    }*/
}

// MARK: Tests

#[cfg(test)]
mod tests {        
    use std::io::Cursor;    

    use super::{WriteError, WriteErrorKind, WaveWriter};        

    // Validation tests

    #[test]
    fn test_validate_doesnt_accept_zero_channels() {
    	let wave_writer = WaveWriter::new(0, 44100, 16, Cursor::new(Vec::new()));        
        assert_matches!(Err(WriteError::Format(WriteErrorKind::NumChannelsIsZero)), wave_writer);
    }

    #[test]
    fn test_validate_doesnt_accept_zero_sample_rate() {
    	let wave_writer = WaveWriter::new(1, 0, 16, Cursor::new(Vec::new()));        
        assert_matches!(Err(WriteError::Format(WriteErrorKind::SampleRateIsZero)), wave_writer);
    }

    #[test]
    fn test_validate_doesnt_accept_invalid_bitrate() {
    	let wave_writer = WaveWriter::new(1, 44100, 12, Cursor::new(Vec::new()));        
        assert_matches!(Err(WriteError::Format(WriteErrorKind::UnsupportedBitsPerSample(12))), wave_writer);
    }

    #[test]
    fn test_validate_accepts_valid_combination() {
    	let wave_writer = WaveWriter::new(1, 44100, 16, Cursor::new(Vec::new()));        
        assert_matches!(Ok(_), wave_writer);
    }
}