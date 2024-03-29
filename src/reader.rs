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
use std::io::{Read, Seek, SeekFrom};
use std::result;

use byteorder::{LittleEndian, ReadBytesExt};

use super::{Format, PcmFormat};
use super::{FORMAT_EXTENDED, FORMAT_UNCOMPRESSED_PCM};

// MARK: Error types

/// Represents an error that occurred while reading a wave file.
#[derive(Debug)]
pub enum ReadError {
    /// The file format is incorrect or unsupported.
    Format(ReadErrorKind),
    /// An IO error occurred.
    Io(io::Error),
}

/// Represents a result when reading a wave file.
pub type ReadResult<T> = result::Result<T, ReadError>;

/// Represents a file format error, when the wave file is incorrect or unsupported.
#[derive(Debug)]
pub enum ReadErrorKind {
    /// The file does not start with a "RIFF" tag and chunk size.
    NotARiffFile,
    /// The file doesn't continue with "WAVE" after the RIFF chunk header.
    NotAWaveFile,
    /// This file is not an uncompressed PCM wave file. Only uncompressed files are supported.
    NotAnUncompressedPcmWaveFile(u16),
    /// This file is missing header data and can't be parsed.
    FmtChunkTooShort,
    /// The number of channels is zero, which is invalid.
    NumChannelsIsZero,
    /// The sample rate is zero, which is invalid.
    SampleRateIsZero,
    /// Only 8-bit, 16-bit, 24-bit and 32-bit PCM files are supported.
    UnsupportedBitsPerSample(u16),
    /// We don't currently support extended PCM wave files where the actual
    /// bits per sample is less than the container size.
    InvalidBitsPerSample(u16, u16),
}

impl ReadErrorKind {
    fn to_string(&self) -> &str {
        match *self {
            ReadErrorKind::NotARiffFile => "not a RIFF file",
            ReadErrorKind::NotAWaveFile => "not a WAVE file",
            ReadErrorKind::NotAnUncompressedPcmWaveFile(_) => "Not an uncompressed wave file",
            ReadErrorKind::FmtChunkTooShort => "fmt_ chunk is too short",
            ReadErrorKind::NumChannelsIsZero => "Number of channels is zero",
            ReadErrorKind::SampleRateIsZero => "Sample rate is zero",
            ReadErrorKind::UnsupportedBitsPerSample(_) => "Unsupported bits per sample",
            ReadErrorKind::InvalidBitsPerSample(_, _) => {
                "A bits per sample of less than the container size is not currently supported"
            }
        }
    }
}

impl fmt::Display for ReadErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.to_string())
    }
}

impl fmt::Display for ReadError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            ReadError::Format(ref err_kind) => write!(f, "Format error: {}", err_kind),
            ReadError::Io(ref err) => write!(f, "IO error: {}", err),
        }
    }
}

impl error::Error for ReadError {
    fn cause(&self) -> Option<&dyn error::Error> {
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

fn validate_pcm_format(format: u16) -> ReadResult<Format> {
    match format {
        FORMAT_UNCOMPRESSED_PCM => Ok(Format::UncompressedPcm),
        FORMAT_EXTENDED => Ok(Format::Extended),
        _ => Err(ReadError::Format(
            ReadErrorKind::NotAnUncompressedPcmWaveFile(format),
        )),
    }
}

fn validate_pcm_subformat(sub_format: u16) -> ReadResult<()> {
    match sub_format {
        FORMAT_UNCOMPRESSED_PCM => Ok(()),
        _ => Err(ReadError::Format(
            ReadErrorKind::NotAnUncompressedPcmWaveFile(sub_format),
        )),
    }
}

fn validate_fmt_header_is_large_enough(size: u32, min_size: u32) -> ReadResult<()> {
    if size < min_size {
        Err(ReadError::Format(ReadErrorKind::FmtChunkTooShort))
    } else {
        Ok(())
    }
}

trait ReadWaveExt: Read + Seek {
    fn read_wave_header(&mut self) -> ReadResult<PcmFormat> {
        self.validate_is_riff_file()?;
        self.validate_is_wave_file()?;

        // The fmt subchunk should be at least 14 bytes for wave files, and 16 bytes
        // for PCM wave files. The check is done twice so an appropriate error message
        // can be returned depending on the type of file.
        let fmt_subchunk_size = self.skip_until_subchunk(b"fmt ")?;
        validate_fmt_header_is_large_enough(fmt_subchunk_size, 14)?;
        let format = validate_pcm_format(self.read_u16::<LittleEndian>()?)?;
        validate_fmt_header_is_large_enough(fmt_subchunk_size, 16)?;

        let num_channels = self.read_u16::<LittleEndian>()?;
        let sample_rate = self.read_u32::<LittleEndian>()?;
        let _ = self.read_u32::<LittleEndian>()?;                   // Byte rate, ignored.
        let _ = self.read_u16::<LittleEndian>()?;                   // Block align, ignored.
        let bits_per_sample = self.read_u16::<LittleEndian>()?;

        match format {
            Format::UncompressedPcm => self.skip_over_remainder(16, fmt_subchunk_size)?,
            Format::Extended => self.validate_extended_format(bits_per_sample)?,
        }

        if num_channels == 0 {
            return Err(ReadError::Format(ReadErrorKind::NumChannelsIsZero));
        } else if sample_rate == 0 {
            return Err(ReadError::Format(ReadErrorKind::SampleRateIsZero));
        } else if bits_per_sample != 8 && bits_per_sample != 16 
        	   && bits_per_sample != 24 && bits_per_sample != 32 {
            return Err(ReadError::Format(
            	ReadErrorKind::UnsupportedBitsPerSample(bits_per_sample)));
        }

        Ok(PcmFormat {
            num_channels: num_channels,
            sample_rate: sample_rate,
            bits_per_sample: bits_per_sample,
        })
    }

    fn validate_extended_format(&mut self, bits_per_sample: u16) -> ReadResult<()> {
        let extra_info_size = self.read_u16::<LittleEndian>()?;
        validate_fmt_header_is_large_enough(extra_info_size.into(), 22)?;

        let sample_info = self.read_u16::<LittleEndian>()?;
        let _ = self.read_u32::<LittleEndian>()?;                   // Channel mask, ignored.
        validate_pcm_subformat(self.read_u16::<LittleEndian>()?)?;
        self.skip_over_remainder(8, extra_info_size.into())?;       // Ignore the rest of the GUID.

        if sample_info != bits_per_sample {
            // We don't currently support wave files where the bits per sample
            // doesn't entirely fill the allocated bits per sample.
            return Err(ReadError::Format(ReadErrorKind::InvalidBitsPerSample(
                bits_per_sample,
                sample_info,
            )));
        }

        Ok(())
    }

    fn skip_over_remainder(&mut self, read_so_far: u32, size: u32) -> ReadResult<()> {
        if read_so_far < size {
            let remainder = size - read_so_far;
            self.seek(SeekFrom::Current(remainder.into()))?;
        }
        Ok(())
    }

    fn validate_is_riff_file(&mut self) -> ReadResult<()> {
        self.validate_tag(b"RIFF", ReadErrorKind::NotARiffFile)?;
        // The next four bytes represent the chunk size. We're not going to
        // validate it, so that we can still try to read files that might have
        // an incorrect chunk size, so let's skip over it.
        let _ = self.read_chunk_size()?;
        Ok(())
    }

    fn validate_is_wave_file(&mut self) -> ReadResult<()> {
        self.validate_tag(b"WAVE", ReadErrorKind::NotAWaveFile)?;
        Ok(())
    }

    fn validate_tag(&mut self, expected_tag: &[u8; 4], err_kind: ReadErrorKind) -> ReadResult<()> {
        let tag = self.read_tag()?;
        if &tag != expected_tag {
            return Err(ReadError::Format(err_kind));
        }
        Ok(())
    }

    fn skip_until_subchunk(&mut self, matching_tag: &[u8; 4]) -> ReadResult<u32> {
        loop {
            let tag = self.read_tag()?;
            let subchunk_size = self.read_chunk_size()?;

            if &tag == matching_tag {
                return Ok(subchunk_size);
            } else {
                self.seek(SeekFrom::Current(subchunk_size.into()))?;
            }
        }
    }

    fn read_tag(&mut self) -> ReadResult<[u8; 4]> {
        let mut tag: [u8; 4] = [0; 4];
        self.read_exact(&mut tag)?;
        Ok(tag)
    }

    fn read_chunk_size(&mut self) -> ReadResult<u32> {
        Ok(self.read_u32::<LittleEndian>()?)
    }
}

impl<T> ReadWaveExt for T where T: Read + Seek {}

/// Helper struct that takes ownership of a reader and can be used to read data
/// from a PCM wave file.
pub struct WaveReader<T>
where
    T: Read + Seek,
{
    /// Represents the PCM format for this wave file.
    pub pcm_format: PcmFormat,

    // The underlying reader that we'll use to read data.
    reader: T,
}

// TODO what should we do if an incorrect read_* method is called? Return the
// error in the result? Also, the read methods might need to return optionals
// instead so we have a better way of flagging EOF.
impl<T> WaveReader<T>
where
    T: Read + Seek,
{
    /// Returns a new wave reader for the given reader.
    pub fn new(mut reader: T) -> ReadResult<WaveReader<T>> {
        let pcm_format = reader.read_wave_header()?;
        let _ = reader.skip_until_subchunk(b"data")?;

        Ok(WaveReader {
            pcm_format: pcm_format,
            reader: reader,
        })
    }

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
        self.read_sample(|reader| reader.read_int::<LittleEndian>(3))
            .map(|x| x as i32)
    }

    /// Reads a single sample as a signed 32-bit value.
    pub fn read_sample_i32(&mut self) -> io::Result<i32> {
        self.read_sample(|reader| reader.read_i32::<LittleEndian>())
    }

    fn read_sample<F, S>(&mut self, read_data: F) -> io::Result<S>
    where
        F: Fn(&mut T) -> io::Result<S>,
    {
        Ok(read_data(&mut self.reader)?)
    }

    /// Consumes this reader, returning the underlying value.
    pub fn into_inner(self) -> T {
        self.reader
    }
}

// MARK: Tests

#[cfg(test)]
mod tests {
    use std::fmt::Debug;
    use std::io;
    use std::io::{Cursor, Read};

    use byteorder::{ByteOrder, LittleEndian};

    use super::super::{Format, PcmFormat};
    use super::super::{FORMAT_EXTENDED, FORMAT_UNCOMPRESSED_PCM};
    use super::{validate_fmt_header_is_large_enough, validate_pcm_format, validate_pcm_subformat};
    use super::{ReadError, ReadErrorKind, ReadWaveExt, WaveReader};

    // RIFF header tests

    #[test]
    fn test_validate_is_riff_file_ok() {
        let mut data = Cursor::new(b"RIFF    ");
        assert_matches!(Ok(()), data.validate_is_riff_file());
    }

    #[test]
    fn test_validate_is_riff_file_err_incomplete() {
        let mut data = Cursor::new(b"RIF     ");
        assert_matches!(
            Err(ReadError::Format(ReadErrorKind::NotARiffFile)),
            data.validate_is_riff_file()
        );
    }

    #[test]
    fn test_validate_is_riff_file_err_something_else() {
        let mut data = Cursor::new(b"JPEG     ");
        assert_matches!(
            Err(ReadError::Format(ReadErrorKind::NotARiffFile)),
            data.validate_is_riff_file()
        );
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
        assert_matches!(
            Err(ReadError::Format(ReadErrorKind::NotAWaveFile)),
            data.validate_is_wave_file()
        );
    }

    #[test]
    fn test_validate_is_wave_file_err_something_else() {
        let mut data = Cursor::new(b"JPEG");
        assert_matches!(
            Err(ReadError::Format(ReadErrorKind::NotAWaveFile)),
            data.validate_is_wave_file()
        );
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

    // Wave format validation tests. We only support uncompressed PCM files,
    // which can be in the "canonical" format or an "extended" format.

    #[test]
    fn test_validate_pcm_format_ok_uncompressed() {
        assert_matches!(
            Ok(Format::UncompressedPcm),
            validate_pcm_format(FORMAT_UNCOMPRESSED_PCM)
        );
    }

    #[test]
    fn test_validate_pcm_format_ok_extended() {
        assert_matches!(Ok(Format::Extended), validate_pcm_format(FORMAT_EXTENDED));
    }

    #[test]
    fn test_validate_pcm_format_err_not_uncompressed() {
        assert_matches!(
            Err(ReadError::Format(
                ReadErrorKind::NotAnUncompressedPcmWaveFile(_)
            )),
            validate_pcm_format(12345)
        );
    }

    // Wave subformat validation tests. We only support uncompressed PCM files.

    #[test]
    fn test_validate_pcm_subformat_ok_uncompressed() {
        assert_matches!(Ok(()), validate_pcm_subformat(FORMAT_UNCOMPRESSED_PCM));
    }

    #[test]
    fn test_validate_pcm_subformat_err_extended_format_value_not_valid_for_subformat() {
        assert_matches!(
            Err(ReadError::Format(
                ReadErrorKind::NotAnUncompressedPcmWaveFile(_)
            )),
            validate_pcm_subformat(FORMAT_EXTENDED)
        );
    }

    #[test]
    fn test_validate_pcm_subformat_err_not_uncompressed() {
        assert_matches!(
            Err(ReadError::Format(
                ReadErrorKind::NotAnUncompressedPcmWaveFile(_)
            )),
            validate_pcm_subformat(12345)
        );
    }

    // Validation tests for ensuring the header is large enough to read in the data we need.

    #[test]
    fn test_validate_fmt_header_is_large_enough_matches() {
        assert_matches!(Ok(()), validate_fmt_header_is_large_enough(16, 16));
    }

    #[test]
    fn test_validate_fmt_header_is_large_enough_more_than_we_need() {
        assert_matches!(Ok(()), validate_fmt_header_is_large_enough(22, 16));
    }

    #[test]
    fn test_validate_fmt_header_is_large_enough_too_small() {
        assert_matches!(
            Err(ReadError::Format(ReadErrorKind::FmtChunkTooShort)),
            validate_fmt_header_is_large_enough(14, 16)
        );
    }

    // Wave header validation tests.

    #[test]
    fn test_validate_pcm_header_missing_fmt_chunk() {
        let mut data = Cursor::new(b"RIFF    WAVE");
        assert_matches!(Err(ReadError::Io(ref err)) if err.kind() == io::ErrorKind::UnexpectedEof,
            			data.read_wave_header());
    }

    #[test]
    fn test_validate_pcm_header_fmt_chunk_too_small() {
        let mut data = Cursor::new(
            b"RIFF    WAVE\
                                     fmt \x0C\x00\x00\x00",
        );
        assert_matches!(
            Err(ReadError::Format(ReadErrorKind::FmtChunkTooShort)),
            data.read_wave_header()
        );
    }

    #[test]
    fn test_validate_pcm_header_fmt_chunk_too_small_pcm() {
        let mut data = Cursor::new(
            b"RIFF    WAVE\
                                     fmt \x0E\x00\x00\x00\
                                     \x01\x00",
        );
        assert_matches!(
            Err(ReadError::Format(ReadErrorKind::FmtChunkTooShort)),
            data.read_wave_header()
        );
    }

    #[test]
    fn test_validate_pcm_header_not_pcm_format() {
        let mut data = Cursor::new(
            b"RIFF    WAVE\
                                     fmt \x0E\x00\x00\x00\
                                     \x02\x00",
        );
        assert_matches!(
            Err(ReadError::Format(
                ReadErrorKind::NotAnUncompressedPcmWaveFile(_)
            )),
            data.read_wave_header()
        );
    }

    #[test]
    fn test_validate_pcm_header_dont_accept_zero_channels() {
        let mut data = Cursor::new(
            b"RIFF    WAVE\
                                     fmt \x10\x00\x00\x00\
                                     \x01\x00\
                                     \x00\x00\
                                     \x00\x00\x00\x00\
                                     \x00\x00\x00\x00\
                                     \x00\x00\
                                     \x00\x00" as &[u8],
        );
        assert_matches!(
            Err(ReadError::Format(ReadErrorKind::NumChannelsIsZero)),
            data.read_wave_header()
        );
    }

    #[test]
    fn test_validate_pcm_header_dont_accept_zero_sample_rate() {
        let mut data = Cursor::new(
            b"RIFF    WAVE\
                                     fmt \x10\x00\x00\x00\
                                     \x01\x00\
                                     \x01\x00\
                                     \x00\x00\x00\x00\
                                     \x00\x00\x00\x00\
                                     \x00\x00\
                                     \x00\x00" as &[u8],
        );
        assert_matches!(
            Err(ReadError::Format(ReadErrorKind::SampleRateIsZero)),
            data.read_wave_header()
        );
    }

    // Standard wave files

    #[test]
    fn test_validate_pcm_header_validate_bits_per_sample_standard() {
        let mut vec = Vec::new();
        vec.extend_from_slice(
            b"RIFF    WAVE\
	                            fmt \x10\x00\x00\x00\
	                            \x01\x00\
	                            \x01\x00\
	                            \x44\xAC\x00\x00\
	                            \x00\x00\x00\x00\
	                            \x00\x00\
	                            \x08\x00",
        );

        let mut cursor = Cursor::new(vec.clone());
        assert_matches!(Ok(_), cursor.read_wave_header());

        vec[34] = 16;
        let mut cursor = Cursor::new(vec.clone());
        assert_matches!(Ok(_), cursor.read_wave_header());

        vec[34] = 24;
        let mut cursor = Cursor::new(vec.clone());
        assert_matches!(Ok(_), cursor.read_wave_header());

        vec[34] = 32;
        let mut cursor = Cursor::new(vec.clone());
        assert_matches!(Ok(_), cursor.read_wave_header());

        vec[34] = 48;
        let mut cursor = Cursor::new(vec.clone());
        assert_matches!(
            Err(ReadError::Format(ReadErrorKind::UnsupportedBitsPerSample(
                _
            ))),
            cursor.read_wave_header()
        );

        vec[34] = 0;
        let mut cursor = Cursor::new(vec.clone());
        assert_matches!(
            Err(ReadError::Format(ReadErrorKind::UnsupportedBitsPerSample(
                _
            ))),
            cursor.read_wave_header()
        );
    }

    #[test]
    fn test_validate_pcm_header_8bit_mono_example_standard() {
        let mut vec = Vec::new();
        vec.extend_from_slice(
            b"RIFF    WAVE\
	                            fmt \x10\x00\x00\x00\
	                            \x01\x00\
	                            \x01\x00\
	                            \x44\xAC\x00\x00\
	                            \x00\x00\x00\x00\
	                            \x00\x00\
	                            \x08\x00",
        );
        let mut cursor = Cursor::new(vec.clone());

        assert_matches!(
            Ok(PcmFormat {
                num_channels: 1,
                sample_rate: 44100,
                bits_per_sample: 8,
            }),
            cursor.read_wave_header()
        );
    }

    #[test]
    fn test_validate_pcm_header_8bit_mono_example_standard_with_extra_cb_data() {
        let mut vec = Vec::new();
        vec.extend_from_slice(
            b"RIFF    WAVE\
	                            fmt \x10\x00\x00\x00\
	                            \x01\x00\
	                            \x01\x00\
	                            \x44\xAC\x00\x00\
	                            \x00\x00\x00\x00\
	                            \x00\x00\
	                            \x08\x00\
	                            \x00\x00\x00\x00",
        );
        let mut cursor = Cursor::new(vec.clone());

        assert_matches!(
            Ok(PcmFormat {
                num_channels: 1,
                sample_rate: 44100,
                bits_per_sample: 8,
            }),
            cursor.read_wave_header()
        );
    }

    // Extended format

    #[test]
    fn test_validate_pcm_header_extended_format_too_small() {
        let mut vec = Vec::new();
        vec.extend_from_slice(
            b"RIFF    WAVE\
		                        fmt \x10\x00\x00\x00\
		                        \xFE\xFF\
		                        \x01\x00\
		                        \x44\xAC\x00\x00\
		                        \x00\x00\x00\x00\
		                        \x00\x00\
		                        \x08\x00\
		                        \x02\x00\x00\x00",
        );
        let mut cursor = Cursor::new(vec.clone());

        assert_matches!(
            Err(ReadError::Format(ReadErrorKind::FmtChunkTooShort)),
            cursor.read_wave_header()
        );
    }

    #[test]
    fn test_validate_pcm_header_extended_format_not_pcm_format() {
        let mut vec = Vec::new();
        vec.extend_from_slice(
            b"RIFF    WAVE\
		                        fmt \x10\x00\x00\x00\
		                        \xFE\xFF\
		                        \x01\x00\
		                        \x44\xAC\x00\x00\
		                        \x00\x00\x00\x00\
		                        \x00\x00\
		                        \x08\x00\
		                        \x16\x00\
		                        \x08\x00\
		                        \x00\x00\x00\x00\
		                        \x09\x00\x00\x00\x00\x00\x10\x00\x80\x00\x00\xAA\x00\x38\x9B\x71",
        );
        let mut cursor = Cursor::new(vec.clone());

        assert_matches!(
            Err(ReadError::Format(
                ReadErrorKind::NotAnUncompressedPcmWaveFile(_)
            )),
            cursor.read_wave_header()
        );
    }

    #[test]
    fn test_validate_pcm_header_extended_format_sample_rates_dont_match() {
        let mut vec = Vec::new();
        vec.extend_from_slice(
            b"RIFF    WAVE\
		                        fmt \x10\x00\x00\x00\
		                        \xFE\xFF\
		                        \x01\x00\
		                        \x44\xAC\x00\x00\
		                        \x00\x00\x00\x00\
		                        \x00\x00\
		                        \x08\x00\
		                        \x16\x00\
		                        \x10\x00\
		                        \x00\x00\x00\x00\
		                        \x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00",
        );
        let mut cursor = Cursor::new(vec.clone());

        assert_matches!(
            Err(ReadError::Format(ReadErrorKind::InvalidBitsPerSample(_, _))),
            cursor.read_wave_header()
        );
    }

    #[test]
    fn test_validate_pcm_header_extended_format_sample_rates_ok() {
        let mut vec = Vec::new();
        vec.extend_from_slice(
            b"RIFF    WAVE\
	                            fmt \x10\x00\x00\x00\
	                            \xFE\xFF\
	                            \x01\x00\
	                            \x44\xAC\x00\x00\
	                            \x00\x00\x00\x00\
	                            \x00\x00\
	                            \x08\x00\
	                            \x16\x00\
	                            \x08\x00\
	                            \x00\x00\x00\x00\
	                            \x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00",
        );
        let mut cursor = Cursor::new(vec.clone());

        assert_matches!(Ok(_), cursor.read_wave_header());
    }

    #[test]
    fn test_validate_pcm_header_8bit_mono_example_extended() {
        let mut vec = Vec::new();
        vec.extend_from_slice(
            b"RIFF    WAVE\
		                        fmt \x10\x00\x00\x00\
		                        \xFE\xFF\
		                        \x01\x00\
		                        \x44\xAC\x00\x00\
		                        \x00\x00\x00\x00\
		                        \x00\x00\
		                        \x08\x00\
		                        \x16\x00\
		                        \x08\x00\
		                        \x00\x00\x00\x00\
		                        \x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00",
        );
        let mut cursor = Cursor::new(vec.clone());

        assert_matches!(
            Ok(PcmFormat {
                num_channels: 1,
                sample_rate: 44100,
                bits_per_sample: 8,
            }),
            cursor.read_wave_header()
        );
    }

    #[test]
    fn test_validate_extended_format_too_short() {
        // Extended size is less than 22 -- should fail.
        let mut data = Cursor::new(b"\x0F\x00\x00\x00");
        assert_matches!(
            Err(ReadError::Format(ReadErrorKind::FmtChunkTooShort)),
            data.validate_extended_format(16)
        );
    }

    #[test]
    fn test_validate_extended_format_not_pcm() {
        let mut data = Cursor::new(
            b"\x16\x00\
                                     \x10\x00\
                                     \x00\x00\x00\x00\
                                     \xFF\xFF\x00\x00\x00\x00\x00\x00\
                                     \x00\x00\x00\x00\x00\x00\x00\x00",
        );
        assert_matches!(
            Err(ReadError::Format(
                ReadErrorKind::NotAnUncompressedPcmWaveFile(_)
            )),
            data.validate_extended_format(16)
        );
    }

    #[test]
    fn test_validate_extended_format_sample_rate_doesnt_match() {
        let mut data = Cursor::new(
            b"\x16\x00\
                                     \x0F\x00\
                                     \x00\x00\x00\x00\
                                     \x01\x00\x00\x00\x00\x00\x00\x00\
                                     \x00\x00\x00\x00\x00\x00\x00\x00",
        );
        assert_matches!(
            Err(ReadError::Format(ReadErrorKind::InvalidBitsPerSample(_, _))),
            data.validate_extended_format(16)
        );
    }

    #[test]
    fn test_validate_extended_format_sample_rate_ok() {
        let mut data = Cursor::new(
            b"\x16\x00\
                                     \x10\x00\
                                     \x00\x00\x00\x00\
                                     \x01\x00\x00\x00\x00\x00\x00\x00\
                                     \x00\x00\x00\x00\x00\x00\x00\x00",
        );
        assert_matches!(Ok(()), data.validate_extended_format(16));
    }

    // Misc tests

    #[test]
    fn test_skip_over_remainder() {
        let mut data = Cursor::new(b"ABCDEFGHIJKLMNOPQRSTUVWXYZ");
        let mut buf = [0u8; 4];

        let _ = data.skip_over_remainder(0, 0);
        let _ = data.read(&mut buf);
        assert_eq!(b"ABCD", &buf);

        let _ = data.skip_over_remainder(4, 4);
        let _ = data.read(&mut buf);
        assert_eq!(b"EFGH", &buf);

        let _ = data.skip_over_remainder(0, 4);
        let _ = data.read(&mut buf);
        assert_eq!(b"MNOP", &buf);

        let _ = data.skip_over_remainder(4, 8);
        let _ = data.read(&mut buf);
        assert_eq!(b"UVWX", &buf);
    }

    // Wave reader tests

    #[test]
    fn test_reading_data_from_data_chunk_u8() {
        let raw_data = b"\x00\x01\x02\x03\
                         \x04\x05\x06\x07\
                         \x08\x09\x0A\x0B\
                         \x0C\x0D\x0E\x0F";

        let expected_results = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15];

        test_reading_data_from_data_chunk(
            raw_data,
            &expected_results,
            1,
            WaveReader::read_sample_u8,
        );
    }

    #[test]
    fn test_reading_data_from_data_chunk_i16() {
        let raw_data = b"\x00\x01\x01\x01\
                         \x02\x01\x03\x01\
                         \x04\x01\x05\x01\
                         \x06\x01\x07\x01";
        let expected_results = [256, 257, 258, 259, 260, 261, 262, 263];

        test_reading_data_from_data_chunk(
            raw_data,
            &expected_results,
            2,
            WaveReader::read_sample_i16,
        );
    }

    #[test]
    fn test_reading_data_from_data_chunk_i24() {
        let raw_data = b"\x01\x01\x02\
                         \x02\x01\x02\
                         \x03\x01\x02\
                         \x04\x01\x02\
                         \x05\x01\x02";
        let expected_results = [
            65536 * 2 + 256 + 1 + 0,
            65536 * 2 + 256 + 1 + 1,
            65536 * 2 + 256 + 1 + 2,
            65536 * 2 + 256 + 1 + 3,
            65536 * 2 + 256 + 1 + 4,
        ];

        test_reading_data_from_data_chunk(
            raw_data,
            &expected_results,
            3,
            WaveReader::read_sample_i24,
        );
    }

    #[test]
    fn test_reading_data_from_data_chunk_i32() {
        let raw_data = b"\x00\x01\x02\x03\
                         \x04\x05\x06\x07\
                         \x08\x09\x0A\x0B\
                         \x0C\x0D\x0E\x0F";
        let expected_results = [50462976, 117835012, 185207048, 252579084];

        test_reading_data_from_data_chunk(
            raw_data,
            &expected_results,
            4,
            WaveReader::read_sample_i32,
        );
    }

    fn test_reading_data_from_data_chunk<S, F>(
        raw_data: &[u8],
        expected_results: &[S],
        bytes_per_num: u16,
        read_sample: F,
    ) where
        S: PartialEq + Debug,
        F: Fn(&mut WaveReader<Cursor<Vec<u8>>>) -> io::Result<S>,
    {
        let vec = create_standard_in_memory_riff_wave(1, 44100, bytes_per_num * 8, raw_data);
        let cursor = Cursor::new(vec.clone());
        let mut wave_reader = WaveReader::new(cursor).unwrap();

        for expected in expected_results {
            let next_sample = read_sample(&mut wave_reader).unwrap();
            assert_eq!(*expected, next_sample);
        }
    }

    trait VecExt {
        fn extend_with_header_for_standard_wave(&mut self, data_size: usize);

        fn extend_with_standard_fmt_subchunk(
            &mut self,
            num_channels: u16,
            sample_rate: u32,
            bits_per_sample: u16,
        );

        fn extend_with_data_subchunk(&mut self, raw_data: &[u8]);

        fn extend_with_u16(&mut self, val: u16);

        fn extend_with_u32(&mut self, val: u32);
    }

    impl VecExt for Vec<u8> {
        fn extend_with_header_for_standard_wave(&mut self, data_size: usize) {
            self.extend_from_slice(b"RIFF");                    // Identifier
            self.extend_with_u32(36 + data_size as u32);        // File size minus eight bytes
            self.extend_from_slice(b"WAVE");                    // Identifier
        }

        fn extend_with_standard_fmt_subchunk(
            &mut self,
            num_channels: u16,
            sample_rate: u32,
            bits_per_sample: u16,
        ) {
            self.extend_from_slice(b"fmt \x10\x00\x00\x00");    // "fmt " chunk and size
            self.extend_from_slice(b"\x01\x00");                // PCM Format
            self.extend_with_u16(num_channels);                 // Number of channels
            self.extend_with_u32(sample_rate);                  // Sample rate

            let bytes_per_sample = bits_per_sample / 8;
            let block_align = num_channels * bytes_per_sample;
            let byte_rate = block_align as u32 * sample_rate;

            self.extend_with_u32(byte_rate);                    // Byte rate
            self.extend_with_u16(block_align);                  // Block align
            self.extend_with_u16(bits_per_sample);              // Bits per sample
        }

        fn extend_with_data_subchunk(&mut self, raw_data: &[u8]) {
            self.extend_from_slice(b"data");                    // Start of "data" subchunk.
            self.extend_with_u32(raw_data.len() as u32);        // Size of data subchunk.
            self.extend_from_slice(raw_data);                   // The actual data, as bytes.
        }

        fn extend_with_u16(&mut self, val: u16) {
            let mut buf_16: [u8; 2] = [0; 2];
            LittleEndian::write_u16(&mut buf_16, val);
            self.extend_from_slice(&buf_16);
        }

        fn extend_with_u32(&mut self, val: u32) {
            let mut buf_32: [u8; 4] = [0; 4];
            LittleEndian::write_u32(&mut buf_32, val);
            self.extend_from_slice(&buf_32);
        }
    }

    fn create_standard_in_memory_riff_wave(
        num_channels: u16,
        sample_rate: u32,
        bits_per_sample: u16,
        data: &[u8],
    ) -> Vec<u8> {
        let mut vec = Vec::new();

        vec.extend_with_header_for_standard_wave(data.len());
        vec.extend_with_standard_fmt_subchunk(num_channels, sample_rate, bits_per_sample);
        vec.extend_with_data_subchunk(data);

        vec
    }
}
