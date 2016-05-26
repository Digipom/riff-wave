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

use std::cmp;
use std::error;
use std::fmt;
use std::io;
use std::io::{Seek, SeekFrom, Write};
use std::result;

use byteorder::{LittleEndian, WriteBytesExt};

use super::PcmFormat;
use super::{FORMAT_UNCOMPRESSED_PCM, MAX_I24_VALUE, MIN_I24_VALUE};

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

trait WriteWaveExt: Write + Seek {
    fn write_standard_wave_header(&mut self, pcm_format: &PcmFormat) -> WriteResult<()> {
        try!(self.write_riff_wave_chunk_header());
        try!(self.write_standard_fmt_subchunk(pcm_format.num_channels,
                                              pcm_format.sample_rate,
                                              pcm_format.bits_per_sample));
        try!(self.write_data_subchunk_header());

        Ok(())
    }

    fn write_riff_wave_chunk_header(&mut self) -> WriteResult<()> {
        try!(self.write_all(b"RIFF"));                      // Identifier
        try!(self.write_u32_l(36));                         // File size (header) minus eight bytes
        try!(self.write_all(b"WAVE"));                      // Identifier

        Ok(())
    }

    fn write_standard_fmt_subchunk(&mut self,
                                   num_channels: u16,
                                   sample_rate: u32,
                                   bits_per_sample: u16)
                                   -> WriteResult<()> {
        if num_channels == 0 {
            return Err(WriteError::Format(WriteErrorKind::NumChannelsIsZero));
        } else if sample_rate == 0 {
            return Err(WriteError::Format(WriteErrorKind::SampleRateIsZero));
        } else if bits_per_sample != 8 && bits_per_sample != 16 && bits_per_sample != 24 &&
           bits_per_sample != 32 {
            return Err(WriteError::Format(WriteErrorKind::UnsupportedBitsPerSample(bits_per_sample)));
        }

        try!(self.write_all(b"fmt "));                      // "fmt " chunk and size
        try!(self.write_u32_l(16));                         // Subchunk size
        try!(self.write_u16_l(FORMAT_UNCOMPRESSED_PCM));    // PCM Format
        try!(self.write_u16_l(num_channels));               // Number of channels
        try!(self.write_u32_l(sample_rate));                // Sample rate

        let bytes_per_sample = bits_per_sample / 8;
        let block_align = num_channels * bytes_per_sample;
        let byte_rate = block_align as u32 * sample_rate;

        try!(self.write_u32_l(byte_rate));                  // Byte rate
        try!(self.write_u16_l(block_align));                // Block align
        try!(self.write_u16_l(bits_per_sample));            // Bits per sample

        Ok(())
    }

    fn write_data_subchunk_header(&mut self) -> WriteResult<()> {
        try!(self.write_all(b"data"));                      // Start of "data" subchunk
        try!(self.write_u32_l(0));                          // Size of data subchunk.

        Ok(())
    }    

    fn write_u16_l(&mut self, n: u16) -> io::Result<()> {
        self.write_u16::<LittleEndian>(n)
    }

    fn write_u32_l(&mut self, n: u32) -> io::Result<()> {
        self.write_u32::<LittleEndian>(n)
    }    
}

impl<T> WriteWaveExt for T where T: Seek + Write {}

fn clamp(n: i32, min: i32, max: i32) -> i32 {
    cmp::min(cmp::max(n, min), max)
}

/// Helper struct that takes ownership of a writer and can be used to write data
/// to a PCM wave file.
#[derive(Debug)]
pub struct WaveWriter<T>
    where T: Seek + Write
{
    ///  Represents the PCM format for this wave file.
    pub pcm_format: PcmFormat,

    // How many samples have been written.
    written_samples: u32,

    // The underlying writer that we'll use to read data.
    writer: T,
}

// TODO what should we do if an incorrect write_* method is called? Return the error in the result?
impl<T> WaveWriter<T>
    where T: Seek + Write
{
    /// Returns a new wave writer for the given writer.
    pub fn new(num_channels: u16,
               sample_rate: u32,
               bits_per_sample: u16,
               mut writer: T)
               -> WriteResult<WaveWriter<T>> {
        let pcm_format = PcmFormat {
            num_channels: num_channels,
            sample_rate: sample_rate,
            bits_per_sample: bits_per_sample,
        };

        try!(writer.write_standard_wave_header(&pcm_format));

        Ok(WaveWriter {
            pcm_format: pcm_format,
            written_samples: 0,
            writer: writer,
        })
    }

    /// Writes a single sample as an unsigned 8-bit value.
    pub fn write_sample_u8(&mut self, sample: u8) -> io::Result<()> {
        self.write_sample(sample, |writer, sample| writer.write_u8(sample))
    }

    /// Writes a single sample as a signed 16-bit value.
    pub fn write_sample_i16(&mut self, sample: i16) -> io::Result<()> {
        self.write_sample(sample, |writer, sample| 
            writer.write_i16::<LittleEndian>(sample))
    }

    /// Writes a single sample as a signed 24-bit value. The value will be truncated
    /// to fit in a 24-bit value.
    pub fn write_sample_i24(&mut self, sample: i32) -> io::Result<()> {
        self.write_sample(sample, |writer, sample| {
            writer.write_int::<LittleEndian>(3, 
                clamp(sample, MIN_I24_VALUE, MAX_I24_VALUE) as usize)
        })
    }

    /// Writes a single sample as a signed 32-bit value.
    pub fn write_sample_i32(&mut self, sample: i32) -> io::Result<()> {
        self.write_sample(sample, |writer, sample| 
            writer.write_i32::<LittleEndian>(sample))
    }

    fn write_sample<F, S>(&mut self, sample: S, write_data: F) -> io::Result<()>
        where F: Fn(&mut T, S) -> io::Result<()>
    {
        try!(write_data(&mut self.writer, sample));
        self.written_samples = self.written_samples + 1;
        Ok(())
    }

    /// Updates the header at the beginning of the file with the new chunk sizes.
    pub fn sync_header(&mut self) -> io::Result<()> {            
        let data_chunk_size = self.written_samples * self.pcm_format.bits_per_sample as u32 / 8;
        let riff_chunk_size = 36 + data_chunk_size;

        // File size minus eight bytes     
        try!(self.writer.seek(SeekFrom::Start(4)));   
        try!(self.writer.write_u32_l(riff_chunk_size));

        // Data size minus eight bytes     
        try!(self.writer.seek(SeekFrom::Start(40)));   
        try!(self.writer.write_u32_l(data_chunk_size));

        // Seek back to the end so we can continue writing
        try!(self.writer.seek(SeekFrom::End(0)));

        Ok(())
    }

    /// Consumes this writer, returning the underlying value.
    pub fn into_inner(self) -> T {
        self.writer
    }
}

// MARK: Tests

#[cfg(test)]
mod tests {
    use std::io::Cursor;

    use super::super::WaveReader;
    use super::{WriteError, WriteErrorKind, WaveWriter};


    // Validation tests

    #[test]
    fn test_validate_doesnt_accept_zero_channels() {
        let wave_writer = WaveWriter::new(0, 44100, 16, Cursor::new(Vec::new()));
        assert_matches!(Err(WriteError::Format(WriteErrorKind::NumChannelsIsZero)),
                        wave_writer);
    }

    #[test]
    fn test_validate_doesnt_accept_zero_sample_rate() {
        let wave_writer = WaveWriter::new(1, 0, 16, Cursor::new(Vec::new()));
        assert_matches!(Err(WriteError::Format(WriteErrorKind::SampleRateIsZero)),
                        wave_writer);
    }

    #[test]
    fn test_validate_doesnt_accept_invalid_bitrate() {
        let wave_writer = WaveWriter::new(1, 44100, 12, Cursor::new(Vec::new()));
        assert_matches!(Err(WriteError::Format(WriteErrorKind::UnsupportedBitsPerSample(12))),
                        wave_writer);
    }

    #[test]
    fn test_validate_accepts_valid_combination() {
        let wave_writer = WaveWriter::new(1, 44100, 16, Cursor::new(Vec::new()));
        assert_matches!(Ok(_), wave_writer);
    }

    // Header validation tests

    #[test]
    fn test_header_is_acceptable() {
        let data = Vec::new();
        let mut cursor = Cursor::new(data);
        let wave_writer = WaveWriter::new(1, 44100, 16, cursor).unwrap();
        let mut cursor = wave_writer.into_inner();

        cursor.set_position(0);

        let wave_reader = WaveReader::new(cursor).unwrap();

        assert_eq!(1, wave_reader.pcm_format.num_channels);
        assert_eq!(44100, wave_reader.pcm_format.sample_rate);
        assert_eq!(16, wave_reader.pcm_format.bits_per_sample);
    }

    // Write validation tests

    #[test]
    fn test_header_sync_when_no_data_written() {
      let data = Vec::new();
        let mut cursor = Cursor::new(data);
        let mut wave_writer = WaveWriter::new(1, 44100, 16, cursor).unwrap();
        wave_writer.sync_header().unwrap();
        let mut cursor = wave_writer.into_inner();

        cursor.set_position(0);

        let wave_reader = WaveReader::new(cursor).unwrap();        
        let cursor = wave_reader.into_inner();
        let data = cursor.into_inner();
        
        assert_eq!(44, data.len());
        // We're not currently surfacing the chunk/subchunk info in the reader
        // so just access the data directly.

        // Should match 36 in little-endian format.
        assert_eq!(b"\x24\x00\x00\x00", &data[4..8]);  

        // Should match 0 in little-endian format.
        assert_eq!(b"\x00\x00\x00\x00", &data[40..44]);  
    }

    #[test]
    fn test_header_sync_when_ten_samples_written() {
        let data = Vec::new();
        let mut cursor = Cursor::new(data);
        let mut wave_writer = WaveWriter::new(1, 44100, 16, cursor).unwrap();

        for i in 0..10 {
            wave_writer.write_sample_i16(i as i16).unwrap();
        }

        wave_writer.sync_header().unwrap();

        let mut cursor = wave_writer.into_inner();

        cursor.set_position(0);

        let wave_reader = WaveReader::new(cursor).unwrap();        
        let cursor = wave_reader.into_inner();
        let data = cursor.into_inner();
        
        assert_eq!(64, data.len());
        // We're not currently surfacing the chunk/subchunk info in the reader
        // so just access the data directly.

        // Should match 56 in little-endian format.
        assert_eq!(b"\x38\x00\x00\x00", &data[4..8]);  

        // Should match 20 in little-endian format.
        assert_eq!(b"\x14\x00\x00\x00", &data[40..44]);  
    }

    // TODO test header
}
