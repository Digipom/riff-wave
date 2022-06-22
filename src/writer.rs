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
    /// Wave files are limited to 4GB in size.
    ExceededMaxSize,
    /// An IO error occurred.
    Io(io::Error),
}

/// Represents a result when reading a wave file.
pub type WriteResult<T> = result::Result<T, WriteError>;

impl fmt::Display for WriteError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            WriteError::ExceededMaxSize => write!(f, "Exceeded max size of 4GiB"),
            WriteError::Io(ref err) => write!(f, "IO error: {}", err),
        }
    }
}

impl error::Error for WriteError {
    fn description(&self) -> &str {
        match *self {
            WriteError::ExceededMaxSize => "exceeded max size",
            WriteError::Io(ref err) => err.description(),
        }
    }

    fn cause(&self) -> Option<&dyn error::Error> {
        match *self {
            WriteError::ExceededMaxSize => None,
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
    fn write_standard_wave_header(&mut self, pcm_format: &PcmFormat) -> io::Result<()> {
        try!(self.write_riff_wave_chunk_header());
        try!(self.write_standard_fmt_subchunk(pcm_format));
        try!(self.write_data_subchunk_header());

        Ok(())
    }

    fn write_riff_wave_chunk_header(&mut self) -> io::Result<()> {
        try!(self.write_all(b"RIFF"));                      // Identifier
        try!(self.write_u32_l(36));                         // File size (header) minus eight bytes
        try!(self.write_all(b"WAVE"));                      // Identifier

        Ok(())
    }

    fn write_standard_fmt_subchunk(&mut self, pcm_format: &PcmFormat) -> io::Result<()> {
        let num_channels = pcm_format.num_channels;
        let sample_rate = pcm_format.sample_rate;
        let bits_per_sample = pcm_format.bits_per_sample;

        if num_channels == 0 {
            panic!("The number of channels should be greater than zero.");
        } else if sample_rate == 0 {
            panic!("The sample rate should be greater than zero.");            
        } else if bits_per_sample != 8 && bits_per_sample != 16 
               && bits_per_sample != 24 && bits_per_sample != 32 {
            panic!("The bits per sample needs to be either 8, 16, 24, or 32.");            
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

    fn write_data_subchunk_header(&mut self) -> io::Result<()> {
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
    /// # Panics
    /// Panics if num_channels or sample_rate is zero, or if bits_per_sample
    /// doesn't match 8, 16, 24, or 32.
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
    pub fn write_sample_u8(&mut self, sample: u8) -> WriteResult<()> {
        self.write_sample(sample, |writer, sample| writer.write_u8(sample))
    }

    /// Writes a single sample as a signed 16-bit value.
    pub fn write_sample_i16(&mut self, sample: i16) -> WriteResult<()> {
        self.write_sample(sample, |writer, sample| writer.write_i16::<LittleEndian>(sample))
    }

    /// Writes a single sample as a signed 24-bit value. The value will be truncated
    /// to fit in a 24-bit value.
    pub fn write_sample_i24(&mut self, sample: i32) -> WriteResult<()> {
        self.write_sample(sample, |writer, sample| {
            writer.write_int::<LittleEndian>(clamp(sample, MIN_I24_VALUE, MAX_I24_VALUE) as i64, 3)
        })
    }

    /// Writes a single sample as a signed 32-bit value.
    pub fn write_sample_i32(&mut self, sample: i32) -> WriteResult<()> {
        self.write_sample(sample, |writer, sample| writer.write_i32::<LittleEndian>(sample))
    }

    fn write_sample<F, S>(&mut self, sample: S, write_data: F) -> WriteResult<()>
        where F: Fn(&mut T, S) -> io::Result<()>
    {
        try!(self.do_overflow_check_for_next_sample());
        try!(write_data(&mut self.writer, sample));
        self.written_samples += 1;
        Ok(())
    }

    fn do_overflow_check_for_next_sample(&self) -> WriteResult<()> {
        let data_chunk_size = self.calculate_current_data_size();
        let riff_chunk_size = 36 + data_chunk_size;
        let file_size = 8 + riff_chunk_size;

        // The file size after we finish writing a new frame should not exceed
        // 4 GiB.

        let num_channels = self.pcm_format.num_channels as u32;
        let sample_size = self.calculate_sample_size_in_bytes();

        // This is slightly conservative, but most wave files we deal with will
        // probably be either 8-bit or 16-bit and mono or stereo, so we keep the
        // more expensive check for the minority of cases, even if there are
        // some combinations that don't need it.
        if num_channels <= 2 && sample_size <= 2 {
            // The remaining 4GiB space will evenly divide mono and stereo
            // frames for 8-bit and 16-bit files, so we don't need to guard
            // against incomplete frames.
            file_size.checked_add(sample_size).map_or(Err(WriteError::ExceededMaxSize), |_| Ok(()))
        } else {
            let remaining_channels = num_channels - self.written_samples % num_channels;
            let remaining_samples_for_frame = sample_size * remaining_channels;

            file_size.checked_add(remaining_samples_for_frame)
                .map_or(Err(WriteError::ExceededMaxSize), |_| Ok(()))
        }
    }

    fn calculate_current_data_size(&self) -> u32 {
        self.written_samples * self.calculate_sample_size_in_bytes()
    }

    fn calculate_sample_size_in_bytes(&self) -> u32 {
        self.pcm_format.bits_per_sample as u32 / 8
    }

    /// Updates the header at the beginning of the file with the new chunk sizes.
    pub fn sync_header(&mut self) -> io::Result<()> {
        let data_chunk_size = self.calculate_current_data_size();
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
}

impl<T> Drop for WaveWriter<T>
    where T: Seek + Write
{
    fn drop(&mut self) {
        // Make sure the header reflects the latest chunk sizes before we go away.
        let _ = self.sync_header();
    }
}

// Mark: Helper functions

fn clamp(n: i32, min: i32, max: i32) -> i32 {
    cmp::min(cmp::max(n, min), max)
}

// MARK: Tests

#[cfg(test)]
mod tests {
    use std::io::{Cursor, Write};

    use byteorder::{LittleEndian, WriteBytesExt};

    use super::super::WaveReader;
    use super::super::{MIN_I24_VALUE, MAX_I24_VALUE};
    use super::{WaveWriter, WriteError, WriteResult};
    use super::clamp;

    // Validation tests

    #[test]
    #[should_panic]
    fn test_validate_doesnt_accept_zero_channels() {
        let _ = WaveWriter::new(0, 44100, 16, Cursor::new(Vec::new()));
    }

    #[test]
    #[should_panic]
    fn test_validate_doesnt_accept_zero_sample_rate() {
        let _ = WaveWriter::new(1, 0, 16, Cursor::new(Vec::new()));
    }

    #[test]
    #[should_panic]
    fn test_validate_doesnt_accept_invalid_bitrate() {
        let _ = WaveWriter::new(1, 44100, 12, Cursor::new(Vec::new()));
    }

    #[test]
    fn test_validate_accepts_valid_combination() {
        let wave_writer = WaveWriter::new(1, 44100, 16, Cursor::new(Vec::new()));
        assert_matches!(Ok(_), wave_writer);
    }

    // Header validation tests

    #[test]
    fn test_header_is_acceptable() {
        let mut cursor = Cursor::new(Vec::new());
        {
            let _ = WaveWriter::new(1, 44100, 16, cursor.by_ref()).unwrap();
        }

        cursor.set_position(0);

        let wave_reader = WaveReader::new(cursor).unwrap();

        assert_eq!(1, wave_reader.pcm_format.num_channels);
        assert_eq!(44100, wave_reader.pcm_format.sample_rate);
        assert_eq!(16, wave_reader.pcm_format.bits_per_sample);
    }

    // Header sync & drop validation tests

    fn test_header_sync(explicit_sync: bool, write_count: u32) {
        let mut cursor = Cursor::new(Vec::new());
        {
            let mut wave_writer = WaveWriter::new(1, 44100, 16, cursor.by_ref()).unwrap();

            for i in 0..write_count {
                wave_writer.write_sample_i16(i as i16).unwrap();
            }

            if explicit_sync {
                wave_writer.sync_header().unwrap();
            }
        }

        cursor.set_position(0);

        let wave_reader = WaveReader::new(cursor).unwrap();
        let cursor = wave_reader.into_inner();
        let data = cursor.into_inner();

        assert_eq!(44 + write_count as usize * 2, data.len());
        // We're not currently surfacing the chunk/subchunk info in the reader
        // so just access the data directly.
        assert_eq!(get_little_endian_bytes(36 + write_count * 2 as u32), &data[4..8]);
        assert_eq!(get_little_endian_bytes(write_count * 2 as u32), &data[40..44]);
    }

    #[test]
    fn test_header_sync_when_no_data_written() {
        test_header_sync(true, 0);
    }

    #[test]
    fn test_header_sync_via_drop_when_no_data_written() {
        test_header_sync(false, 0);
    }

    #[test]
    fn test_header_sync_when_ten_samples_written() {
        test_header_sync(true, 10);
    }

    #[test]
    fn test_header_sync_via_drop_when_ten_samples_written() {
        test_header_sync(false, 10);
    }

    // Overflow tests

    #[test]
    fn test_clamp() {
        assert_eq!(-5, clamp(-10, -5, 5));
        assert_eq!(5, clamp(10, -5, 5));

        assert_eq!(MIN_I24_VALUE, clamp(i32::min_value(), MIN_I24_VALUE, MAX_I24_VALUE));
        assert_eq!(MAX_I24_VALUE, clamp(i32::max_value(), MIN_I24_VALUE, MAX_I24_VALUE));
    }

    #[test]
    fn test_24_bit_doesnt_panic_when_out_of_range() {
        let mut wave_writer = WaveWriter::new(1, 44100, 24, Cursor::new(Vec::new())).unwrap();

        wave_writer.write_sample_i24(i32::min_value()).unwrap();
        wave_writer.write_sample_i24(i32::max_value()).unwrap();
    }

    #[test]
    fn test_24_bit_accepts_range() {
        let mut cursor = Cursor::new(Vec::new());
        {
            let mut wave_writer = WaveWriter::new(1, 44100, 16, cursor.by_ref()).unwrap();

            wave_writer.write_sample_i24(i32::min_value()).unwrap();
            wave_writer.write_sample_i24(MIN_I24_VALUE).unwrap();
            wave_writer.write_sample_i24(MAX_I24_VALUE).unwrap();
            wave_writer.write_sample_i24(i32::max_value()).unwrap();
        }

        cursor.set_position(0);

        let mut wave_reader = WaveReader::new(cursor).unwrap();
        assert_eq!(MIN_I24_VALUE, wave_reader.read_sample_i24().unwrap());
        assert_eq!(MIN_I24_VALUE, wave_reader.read_sample_i24().unwrap());
        assert_eq!(MAX_I24_VALUE, wave_reader.read_sample_i24().unwrap());
        assert_eq!(MAX_I24_VALUE, wave_reader.read_sample_i24().unwrap());
    }

    #[test]
    fn test_overflow_8bit() {
        test_overflow(8, |wave_writer| wave_writer.write_sample_u8(5));
    }

    #[test]
    fn test_overflow_16bit() {
        test_overflow(16, |wave_writer| wave_writer.write_sample_i16(5));
    }

    #[test]
    fn test_overflow_24bit() {
        test_overflow(24, |wave_writer| wave_writer.write_sample_i24(5));
    }

    #[test]
    fn test_overflow_32bit() {
        test_overflow(32, |wave_writer| wave_writer.write_sample_i32(5));
    }

    fn test_overflow<F>(bits_per_sample: u16, write_sample: F)
        where F: Fn(&mut WaveWriter<Cursor<Vec<u8>>>) -> WriteResult<()>
    {
        let mut wave_writer = WaveWriter::new(1, 44100, bits_per_sample, Cursor::new(Vec::new()))
            .unwrap();

        // Make it believe we are close to overflow:
        wave_writer.written_samples = (u32::max_value() - 44) / (bits_per_sample as u32 / 8);

        // The next write should overflow
        assert_matches!(Err(WriteError::ExceededMaxSize), write_sample(&mut wave_writer));
    }

    #[test]
    fn test_overflow_doesnt_let_us_start_an_incomplete_frame_8bit() {
        test_overflow_doesnt_let_us_start_an_incomplete_frame(5, 8, |wave_writer| {
            wave_writer.write_sample_u8(5)
        });
    }

    #[test]
    fn test_overflow_doesnt_let_us_start_an_incomplete_frame_16bit() {
        test_overflow_doesnt_let_us_start_an_incomplete_frame(6, 16, |wave_writer| {
            wave_writer.write_sample_i16(5)
        });
    }

    fn test_overflow_doesnt_let_us_start_an_incomplete_frame<F>(num_channels: u16,
                                                                bits_per_sample: u16,
                                                                write_sample: F)
        where F: Fn(&mut WaveWriter<Cursor<Vec<u8>>>) -> WriteResult<()>
    {
        let mut wave_writer = WaveWriter::new(num_channels,
                                              44100,
                                              bits_per_sample,
                                              Cursor::new(Vec::new()))
            .unwrap();

        // With this value, we should still be able to write one more 5-channel
        // frame, but should hit a failure when we start the second frame.

        wave_writer.written_samples = (u32::max_value() - 44) / (bits_per_sample as u32 / 8);
        // Make sure we have an incomplete frame at the end.
        assert!(wave_writer.written_samples % num_channels as u32 != 0);
        wave_writer.written_samples -= wave_writer.written_samples % num_channels as u32;
        // Make room for one full frame.
        wave_writer.written_samples -= num_channels as u32;

        // First frame should be OK.
        for _ in 0..num_channels {
            write_sample(&mut wave_writer).unwrap();
        }

        // Starting the next frame should overflow, even though we still have
        // room to write one more sample.
        assert_matches!(Err(WriteError::ExceededMaxSize), write_sample(&mut wave_writer));
    }

    // Write validation tests

    #[test]
    fn test_writing_8bit() {
        test_writing(8,
                     |wave_writer, x| wave_writer.write_sample_u8(x as u8),
                     |wave_reader, x| wave_reader.read_sample_u8().unwrap() == x as u8);
    }

    #[test]
    fn test_writing_16bit() {
        test_writing(16,
                     |wave_writer, x| wave_writer.write_sample_i16(x as i16 * 100),
                     |wave_reader, x| wave_reader.read_sample_i16().unwrap() == x as i16 * 100);
    }

    #[test]
    fn test_writing_24bit() {
        test_writing(24,
                     |wave_writer, x| wave_writer.write_sample_i24(x as i32 * 32767),
                     |wave_reader, x| wave_reader.read_sample_i24().unwrap() == x as i32 * 32767);
    }

    #[test]
    fn test_writing_32bit() {
        test_writing(32,
                     |wave_writer, x| wave_writer.write_sample_i32(x as i32 * 8000000),
                     |wave_reader, x| wave_reader.read_sample_i32().unwrap() == x as i32 * 8000000);
    }

    fn test_writing<F, G>(bits_per_sample: u16, write_sample: F, read_and_check_equal: G)
        where F: Fn(&mut WaveWriter<&mut Cursor<Vec<u8>>>, i32) -> WriteResult<()>,
              G: Fn(&mut WaveReader<Cursor<Vec<u8>>>, i32) -> bool
    {
        let data = Vec::new();
        let mut cursor = Cursor::new(data);
        {
            let mut wave_writer = WaveWriter::new(1, 44100, bits_per_sample, cursor.by_ref())
                .unwrap();

            for i in 0..256 {
                write_sample(&mut wave_writer, i).unwrap();
            }
        }

        cursor.set_position(0);

        let mut wave_reader = WaveReader::new(cursor).unwrap();

        for i in 0..256 {
            assert!(read_and_check_equal(&mut wave_reader, i));
        }

        let cursor = wave_reader.into_inner();
        let data = cursor.into_inner();

        let expected_data_size = 256 * bits_per_sample / 8;
        assert_eq!(44 + expected_data_size as usize, data.len());

        // We're not currently surfacing the chunk/subchunk info in the reader
        // so just access the data directly.
        assert_eq!(get_little_endian_bytes(36 + expected_data_size as u32), &data[4..8]);
        assert_eq!(get_little_endian_bytes(expected_data_size as u32), &data[40..44]);
    }

    fn get_little_endian_bytes(n: u32) -> [u8; 4] {
        let mut buf: [u8; 4] = [0; 4];
        {
            let mut cursor = Cursor::new(&mut buf[..]);
            cursor.write_u32::<LittleEndian>(n).unwrap();
        }
        buf
    }
}
