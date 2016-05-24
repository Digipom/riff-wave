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

//! Basic support for reading and writing wave PCM files.
//!
//! This early version of the library seeks to support the "canonical" wave PCM
//! file format, as well as the basic features of the extended file format.
//! Non-PCM files are not currently supported, nor is metadata. Future versions
//! of the library may add support for some of these features.
//!
//! The wave file format was originally defined by Microsoft, and it stores
//! audio wave data in a container using RIFF chunks to encode the header and
//! data. The RIFF format also supports file metadata via a LIST INFO chunk and
//! an associated data chunk.
//!
//! See also:
//!
//! * [Hound][1] - Another wave encoding and decoding library in Rust.
//! * [Multimedia Programming Interface and Data Specifications 1.0][2] - Further
//! info about the RIFF file format.
//! * [RIFF WAVE (.WAV) file format][3] - Also has more info on the RIFF WAVE format.
//!
//! # The wave file format
//!
//! The wave file format starts with the RIFF file header:
//!
//! Offset | Size | Data       |    Description
//! -----: | ---: | ---------- | ----------------------------------------------
//!      0 |    4 | "RIFF"     | Identifies the main chunk.
//!      4 |    4 | chunk size | The size of the rest of the file. This should be equal to the size of the file minus 8 bytes.
//!      8 |    4 | "WAVE"     | Indicates that this is a wave file.
//!
//! The wave file format requires at least two subchunks which follow the main chunk:
//!
//! * The "fmt " subchunk. This contains additional header information.
//! * The "data" subchunk. This contains the actual audio data.
//!
//! ## The "fmt " subchunk
//!
//! The "fmt " subchunk starts with the following fields:
//!
//! Offset | Size | Data            | Description
//! -----: | ---: | --------------- | -----------------------------------------
//!     12 |    4 | "fmt "          | Identifies this subchunk.
//!     16 |    4 | subchunk size   | The size of the rest of this subchunk.
//!     20 |    2 | format (1)      | The format of the wave data, which will be 1 for uncompressed PCM data.
//!     22 |    2 | num channels    | Indicates if the data is mono, stereo, or something else.
//!     24 |    4 | sample rate     | The sample rate per second.
//!     28 |    4 | byte rate       | The total byte rate per second. For 16-bit stereo at 44,100 samples per second, this would be equal to 176,000 bytes per second.
//!     32 |    2 | block align     | How many bytes are needed for each "frame", where a frame is one sample for each channel.
//!     34 |    2 | bits per sample | The bits per sample; i.e. 16 for 16-bit audio.
//!
//! The `format` can take on various values, including the following codes:
//!
//! Value | Description
//! ----: | -------------------------------------------------------------------
//!     1 | Uncompressed PCM
//!     3 | IEEE floating-point
//!     6 | 8-bit ITU-T G.711 A-law
//!     7 | 8-bit ITU-T G.711 µ-law
//! 65534 | A special marker value, indicating that this is an "extended" wave file.
//!
//! This library currently only supports uncompressed PCM in standard and
//! extended wave formats. These files will usually be either 8-bit unsigned or
//! 16-bit signed, mono or stereo.
//!
//! Wave files may include an additional field, usually reserved for non-PCM formats:
//!
//! Offset | Size | Data            | Description
//! -----: | ---: | --------------- | -----------------------------------------
//!     36 |    2 | extra info size | For non-PCM formats, this stores the size of the additional info that follows the end of the standard header. Otherwise, it is set to 0.
//!
//! ### Extended wave files
//!
//! Some wave files may follow the extended format. In this case, the
//! `extra info size` field will be at least 22 instead of 0.
//!
//! Offset | Size | Data            | Description
//! -----: | ---: | --------------- | -----------------------------------------
//!     38 |    2 | sample info     | For PCM files, this contains the valid bits for sample. For example, if this is set to 20 bits and `bits per sample` is set to 24 bits, then that means that 24 bits are being used to store the sample data, but the actual sample data should not exceed 20 bits of precision.
//!     42 |    4 | channel mask    | This specifies the assignment of channels to speaker positions.
//!     46 |   16 | sub format      | For extended wave files, `format` will be set to 0xFFFE to indicate that it's an extended wave file, with the actual format specified here as a [GUID][4]. The first two bytes are the same as specified in `format code`, and the remainder should match 0x00, 0x00, 0x00, 0x00, 0x10, 0x00, 0x80, 0x00, 0x00, 0xaa, 0x00, 0x38, 0x9b, and 0x71.
//!
//! The MSDN docs recommend this format for files with more than two channels
//! or more than 16 bits per sample, but it's also possible to encounter such
//! wave files that don't include these extra fields. In my testing, Android
//! Marshmallow was able to play back 24-bit PCM wave files using both the
//! standard format and the extensible format, generated using [Audacity][5].
//!
//! ## The "data" subchunk
//!
//! The "data" subchunk contains the actual audio data:
//!
//! Offset | Size | Data            | Description
//! -----: | ---: | --------------- | -----------------------------------------
//! 36+    |    4 | "data"          | Identifies this subchunk
//! 40+    |    4 | subchunk size   | The size of this chunk. For the simple "canonical" wave file format, this will generally be the size of the file minus 44 bytes for the header data, up to and including this field.
//! 44+    |  ... | audio data      | This stores the actual audio data.
//! ...    |  ... | padding byte    | If the length of audio data is an odd number, then an additional padding byte should be inserted.
//!
//! As the subchunk size is a 32-bit value, the length of audio data cannot
//! exceed 4 GiB, and indeed the entire file can't really exceed 4 GiB as the
//! master RIFF chunk size field is also a 32-bit value.
//!
//! ## Additional meta-data
//!
//! Wave files may also contain other metadata, such as the LIST INFO chunks
//! defined by RIFF or other metadata. The LIST INFO chunk is analogous to
//! the ID3 tag in an MP3 file, and if it's present, it can often be found
//! between the "fmt " and "data" subchunks or after the end of the "data"
//! subchunk.
//!
//! See also:
//!
//! * [WAVEFORMATEXTENSIBLE structure][6]
//! * [Audio File Format Specifications][7]
//! * [WAVE PCM soundfile format][8]
//!
//! [1]: https://github.com/ruud-v-a/hound
//! [2]: https://www.aelius.com/njh/wavemetatools/doc/riffmci.pdf
//! [3]: http://www.neurophys.wisc.edu/auditory/riff-format.txt
//! [4]: https://msdn.microsoft.com/en-us/library/windows/desktop/aa373931(v=vs.85).aspx
//! [5]: http://www.audacityteam.org
//! [6]: https://msdn.microsoft.com/en-us/library/windows/desktop/dd757714(v=vs.85).aspx
//! [7]: http://www-mmsp.ece.mcgill.ca/documents/audioformats/wave/wave.html
//! [8]: http://soundfile.sapp.org/doc/WaveFormat/

extern crate byteorder;

use std::error;
use std::fmt;
use std::io;
use std::io::{Read, Seek, SeekFrom};
use std::mem;
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

impl FormatErrorKind {
    fn to_string(&self) -> &str {
        match *self {
            FormatErrorKind::NotARiffFile => "not a RIFF file",
            FormatErrorKind::NotAWaveFile => "not a WAVE file",
            FormatErrorKind::NotAnUncompressedPcmWaveFile(_) => "Not an uncompressed wave file",
            FormatErrorKind::FmtChunkTooShort => "fmt_ chunk is too short",
            FormatErrorKind::NumChannelsIsZero => "Number of channels is zero",
            FormatErrorKind::SampleRateIsZero => "Sample rate is zero",
            FormatErrorKind::UnsupportedBitsPerSample(_) => "Unsupported bits per sample",
            FormatErrorKind::InvalidBitsPerSample(_, _) => {
                "A bits per sample of less than the container size is not currently supported"
            }
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

const FORMAT_UNCOMPRESSED_PCM: u16 = 1;
const FORMAT_EXTENDED: u16 = 65534;

#[derive(Debug)]
enum Format {
    UncompressedPcm,
    Extended,
}

#[derive(Debug)]
pub struct PcmFormat {
    pub num_channels: u16,
    pub sample_rate: u32,
    pub bits_per_sample: u16,
}

fn validate_pcm_format(format: u16) -> ReadResult<Format> {
    match format {
        FORMAT_UNCOMPRESSED_PCM => Ok(Format::UncompressedPcm),
        FORMAT_EXTENDED => Ok(Format::Extended),
        _ => Err(ReadError::Format(FormatErrorKind::NotAnUncompressedPcmWaveFile(format))),
    }
}

fn validate_pcm_subformat(sub_format: u16) -> ReadResult<()> {
    match sub_format {
        FORMAT_UNCOMPRESSED_PCM => Ok(()),
        _ => Err(ReadError::Format(FormatErrorKind::NotAnUncompressedPcmWaveFile(sub_format))),
    }
}

fn validate_fmt_header_is_large_enough(size: u32, min_size: u32) -> ReadResult<()> {
    if size < min_size {
        Err(ReadError::Format(FormatErrorKind::FmtChunkTooShort))
    } else {
        Ok(())
    }
}

trait ReadWaveExt: Read + Seek {
    fn read_wave_header(&mut self) -> ReadResult<PcmFormat> {
        // Validate the beginning of the file
        try!(self.validate_is_riff_file());
        try!(self.validate_is_wave_file());

        // Scan for the "fmt " chunk, and validate the format. Check the header
        // size before and after the format check so we can present the
        // appropriate error types.
        let fmt_subchunk_size = try!(self.skip_until_subchunk(b"fmt "));
        // We need at least 14 bytes for wave files.
        try!(validate_fmt_header_is_large_enough(fmt_subchunk_size, 14));
        let format = try!(validate_pcm_format(try!(self.read_u16::<LittleEndian>())));
        // Now that we've validated the PCM format so that we know this is an
        // uncompressed PCM file, we also need to be able to read the bits per sample.
        try!(validate_fmt_header_is_large_enough(fmt_subchunk_size, 16));

        // We passed the format check; read in the PCM format fields.
        let num_channels = try!(self.read_u16::<LittleEndian>());
        let sample_rate = try!(self.read_u32::<LittleEndian>());
        // Ignore byte rate. We don't need it and we won't validate it for now.
        let _ = try!(self.read_u32::<LittleEndian>());
        // Ignore block align. We don't need it and we won't validate it for now.
        let _ = try!(self.read_u16::<LittleEndian>());
        let bits_per_sample = try!(self.read_u16::<LittleEndian>());

        match format {
            // If a standard file, skip over the rest of the fmt subchunk, if present.
            Format::UncompressedPcm => try!(self.skip_over_remainder(16, fmt_subchunk_size)),
            // If an extended file, we also need to validate the extended fields.
            Format::Extended => try!(self.validate_extended_format(bits_per_sample)),
        }

        if num_channels == 0 {
            return Err(ReadError::Format(FormatErrorKind::NumChannelsIsZero));
        } else if sample_rate == 0 {
            return Err(ReadError::Format(FormatErrorKind::SampleRateIsZero));
        } else if bits_per_sample != 8 && bits_per_sample != 16 
        	   && bits_per_sample != 24 && bits_per_sample != 32 {
            return Err(ReadError::Format(
            	FormatErrorKind::UnsupportedBitsPerSample(bits_per_sample)));
        }

        Ok(PcmFormat {
            num_channels: num_channels,
            sample_rate: sample_rate,
            bits_per_sample: bits_per_sample,
        })
    }

    fn validate_extended_format(&mut self, bits_per_sample: u16) -> ReadResult<()> {
        // Validate the extended information.
        let extra_info_size = try!(self.read_u16::<LittleEndian>());
        try!(validate_fmt_header_is_large_enough(extra_info_size.into(), 22));

        // Read in the extended format fields.
        let sample_info = try!(self.read_u16::<LittleEndian>());
        // Ignore channel mask.
        let _ = try!(self.read_u32::<LittleEndian>());
        // Validate the subformat.
        let _ = try!(validate_pcm_subformat(try!(self.read_u16::<LittleEndian>())));
        // Ignore the rest of the GUID.
        try!(self.skip_over_remainder(8, extra_info_size.into()));

        if sample_info != bits_per_sample {
            // We don't currently support wave files where the bits per sample
            // doesn't entirely fill the allocated bits per sample.
            return Err(ReadError::Format(FormatErrorKind::InvalidBitsPerSample(bits_per_sample,
                                                                               sample_info)));
        }

        Ok(())
    }

    fn skip_over_remainder(&mut self, read_so_far: u32, size: u32) -> ReadResult<()> {
        if read_so_far < size {
            let remainder = size - read_so_far;
            try!(self.seek(SeekFrom::Current(remainder.into())));
        }
        Ok(())
    }

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

impl<T> ReadWaveExt for T where T: Read + Seek {}

/// Helper struct that takes ownership of a reader and can be used to read data
/// from a PCM wave file.
pub struct WaveReader<T>
    where T: Read + Seek
{
    ///  Represents the PCM format for this wave file.
    pub pcm_format: PcmFormat,

    // The byte offset in the file where the actual wave data begins (should be
    // 8 bytes after the beginning of the data subchunk).
    data_begin: u64,

    // The byte offset in the file where the wave data ends. If the subchunk size
    // is invalid, then the reader may run into I/O errors before reaching data_end.
    data_end: u64,

    // The current data position, in bytes.
    current_data_offset: u64,

    // The underlying reader that we'll use to read data.
    reader: T,
}

impl<T> WaveReader<T>
    where T: Read + Seek
{
    /// Returns a new wave reader for the given reader.
    pub fn new(mut reader: T) -> ReadResult<WaveReader<T>> {
        let pcm_format = try!(reader.read_wave_header());
        let data_subchunk_size = try!(reader.skip_until_subchunk(b"data"));

        let data_begin = try!(reader.seek(SeekFrom::Current(0)));
        let data_end = data_begin + data_subchunk_size as u64;

        Ok(WaveReader {
            pcm_format: pcm_format,
            data_begin: data_begin,
            data_end: data_end,
            current_data_offset: data_begin,
            reader: reader,
        })
    }

    /// Reads a single sample as an unsigned 8-bit value. If we've reached the
    /// end of the data chunk, then this will return Ok(None).
    pub fn read_sample_u8(&mut self) -> io::Result<Option<u8>> {
        self.read_sample(|reader| reader.read_u8())
    }

    /// Reads a single sample as a signed 16-bit value. If we've reached the
    /// end of the data chunk, then this will return Ok(None).
    pub fn read_sample_i16(&mut self) -> io::Result<Option<i16>> {
        self.read_sample(|reader| reader.read_i16::<LittleEndian>())
    }

    fn read_sample<F, S>(&mut self, read_data: F) -> io::Result<Option<S>>
        where F: Fn(&mut T) -> io::Result<S>
    {
        let remaining = self.remaining();
        if remaining == 0 {
            Ok(None)
        } else {
            let val = try!(read_data(&mut self.reader));
            self.current_data_offset += mem::size_of::<S>() as u64;
            Ok(Some(val))
        }
    }

    fn remaining(&self) -> u64 {
        self.data_end - self.current_data_offset
    }

    /// Reads several samples as unsigned 8-bit values. Returns the number of
    /// samples read, or an io error if one occurred before data was read.
    pub fn read_samples_as_u8(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        self.read_samples(buf, |wave_reader| WaveReader::read_sample_u8(wave_reader))
    }

    /// Reads several samples as signed 16-bit values. Returns the number of
    /// samples read, or an io error if one occurred before data was read.
    pub fn read_samples_as_i16(&mut self, buf: &mut [i16]) -> io::Result<usize> {
        self.read_samples(buf, |wave_reader| WaveReader::read_sample_i16(wave_reader))
    }

    fn read_samples<F, S>(&mut self, buf: &mut [S], read_sample_impl: F) -> io::Result<usize>
        where F: Fn(&mut Self) -> io::Result<Option<S>>
    {
        let mut successfully_read = 0;

        for out in &mut buf[..] {
            match read_sample_impl(self) {
                Ok(Some(sample)) => {
                    *out = sample;
                    successfully_read = successfully_read + 1;
                }
                Ok(None) => {
                    break;
                }
                Err(err) => {
                    if successfully_read == 0 {
                        return Err(err);
                    } else {
                        break;
                    }
                }                                    
            }
        }

        Ok(successfully_read)
    }
}

// MARK: Tests

#[cfg(test)]
mod tests {
    use std::io;
    use std::io::{Cursor, Read};

    use {FORMAT_UNCOMPRESSED_PCM, FORMAT_EXTENDED};
    use {Format, FormatErrorKind, PcmFormat, ReadError, ReadWaveExt, WaveReader};
    use {validate_fmt_header_is_large_enough, validate_pcm_format, validate_pcm_subformat};

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

    // Wave format validation tests. We only support uncompressed PCM files,
    // which can be in the "canonical" format or an "extended" format.

    #[test]
    fn test_validate_pcm_format_ok_uncompressed() {
        assert_matches!(Ok(Format::UncompressedPcm),
                        validate_pcm_format(FORMAT_UNCOMPRESSED_PCM));
    }

    #[test]
    fn test_validate_pcm_format_ok_extended() {
        assert_matches!(Ok(Format::Extended), validate_pcm_format(FORMAT_EXTENDED));
    }

    #[test]
    fn test_validate_pcm_format_err_not_uncompressed() {
        assert_matches!(Err(ReadError::Format(FormatErrorKind::NotAnUncompressedPcmWaveFile(_))),
        				validate_pcm_format(12345));
    }

    // Wave subformat validation tests. We only support uncompressed PCM files.

    #[test]
    fn test_validate_pcm_subformat_ok_uncompressed() {
        assert_matches!(Ok(()), validate_pcm_subformat(FORMAT_UNCOMPRESSED_PCM));
    }

    #[test]
    fn test_validate_pcm_subformat_err_extended_format_value_not_valid_for_subformat() {
        assert_matches!(Err(ReadError::Format(FormatErrorKind::NotAnUncompressedPcmWaveFile(_))),
            			validate_pcm_subformat(FORMAT_EXTENDED));
    }

    #[test]
    fn test_validate_pcm_subformat_err_not_uncompressed() {
        assert_matches!(Err(ReadError::Format(FormatErrorKind::NotAnUncompressedPcmWaveFile(_))),
						validate_pcm_subformat(12345));
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
        assert_matches!(Err(ReadError::Format(FormatErrorKind::FmtChunkTooShort)),
                        validate_fmt_header_is_large_enough(14, 16));
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
        let mut data = Cursor::new(b"RIFF    WAVE\
                                     fmt \x0C\x00\x00\x00");
        assert_matches!(Err(ReadError::Format(FormatErrorKind::FmtChunkTooShort)),
                        data.read_wave_header());
    }

    #[test]
    fn test_validate_pcm_header_fmt_chunk_too_small_pcm() {
        let mut data = Cursor::new(b"RIFF    WAVE\
                                     fmt \x0E\x00\x00\x00\
                                     \x01\x00");
        assert_matches!(Err(ReadError::Format(FormatErrorKind::FmtChunkTooShort)),
                        data.read_wave_header());
    }

    #[test]
    fn test_validate_pcm_header_not_pcm_format() {
        let mut data = Cursor::new(b"RIFF    WAVE\
                                     fmt \x0E\x00\x00\x00\
                                     \x02\x00");
        assert_matches!(Err(ReadError::Format(FormatErrorKind::NotAnUncompressedPcmWaveFile(_))),
            			data.read_wave_header());
    }

    #[test]
    fn test_validate_pcm_header_dont_accept_zero_channels() {
        let mut data = Cursor::new(b"RIFF    WAVE\
                                     fmt \x10\x00\x00\x00\
                                     \x01\x00\
                                     \x00\x00\
                                     \x00\x00\x00\x00\
                                     \x00\x00\x00\x00\
                                     \x00\x00\
                                     \x00\x00" as &[u8]);
        assert_matches!(Err(ReadError::Format(FormatErrorKind::NumChannelsIsZero)),
                        data.read_wave_header());
    }

    #[test]
    fn test_validate_pcm_header_dont_accept_zero_sample_rate() {
        let mut data = Cursor::new(b"RIFF    WAVE\
                                     fmt \x10\x00\x00\x00\
                                     \x01\x00\
                                     \x01\x00\
                                     \x00\x00\x00\x00\
                                     \x00\x00\x00\x00\
                                     \x00\x00\
                                     \x00\x00" as &[u8]);
        assert_matches!(Err(ReadError::Format(FormatErrorKind::SampleRateIsZero)),
                        data.read_wave_header());
    }

    // Standard wave files

    #[test]
    fn test_validate_pcm_header_validate_bits_per_sample_standard() {
        let mut vec = Vec::new();
        vec.extend_from_slice(b"RIFF    WAVE\
	                            fmt \x10\x00\x00\x00\
	                            \x01\x00\
	                            \x01\x00\
	                            \x44\xAC\x00\x00\
	                            \x00\x00\x00\x00\
	                            \x00\x00\
	                            \x08\x00");

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
        assert_matches!(Err(ReadError::Format(FormatErrorKind::UnsupportedBitsPerSample(_))),
            			cursor.read_wave_header());

        vec[34] = 0;
        let mut cursor = Cursor::new(vec.clone());
        assert_matches!(Err(ReadError::Format(FormatErrorKind::UnsupportedBitsPerSample(_))),
            			cursor.read_wave_header());
    }

    #[test]
    fn test_validate_pcm_header_8bit_mono_example_standard() {
        let mut vec = Vec::new();
        vec.extend_from_slice(b"RIFF    WAVE\
	                            fmt \x10\x00\x00\x00\
	                            \x01\x00\
	                            \x01\x00\
	                            \x44\xAC\x00\x00\
	                            \x00\x00\x00\x00\
	                            \x00\x00\
	                            \x08\x00");
        let mut cursor = Cursor::new(vec.clone());

        assert_matches!(Ok(PcmFormat {
                            num_channels: 1,
                            sample_rate: 44100,
                            bits_per_sample: 8,
                        }),
                        cursor.read_wave_header());
    }

    #[test]
    fn test_validate_pcm_header_8bit_mono_example_standard_with_extra_cb_data() {
        let mut vec = Vec::new();
        vec.extend_from_slice(b"RIFF    WAVE\
	                            fmt \x10\x00\x00\x00\
	                            \x01\x00\
	                            \x01\x00\
	                            \x44\xAC\x00\x00\
	                            \x00\x00\x00\x00\
	                            \x00\x00\
	                            \x08\x00\
	                            \x00\x00\x00\x00");
        let mut cursor = Cursor::new(vec.clone());

        assert_matches!(Ok(PcmFormat {
                            num_channels: 1,
                            sample_rate: 44100,
                            bits_per_sample: 8,
                        }),
                        cursor.read_wave_header());
    }

    // Extended format

    #[test]
    fn test_validate_pcm_header_extended_format_too_small() {
        let mut vec = Vec::new();
        vec.extend_from_slice(b"RIFF    WAVE\
		                        fmt \x10\x00\x00\x00\
		                        \xFE\xFF\
		                        \x01\x00\
		                        \x44\xAC\x00\x00\
		                        \x00\x00\x00\x00\
		                        \x00\x00\
		                        \x08\x00\
		                        \x02\x00\x00\x00");
        let mut cursor = Cursor::new(vec.clone());

        assert_matches!(Err(ReadError::Format(FormatErrorKind::FmtChunkTooShort)),
                        cursor.read_wave_header());
    }

    #[test]
    fn test_validate_pcm_header_extended_format_not_pcm_format() {
        let mut vec = Vec::new();
        vec.extend_from_slice(b"RIFF    WAVE\
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
		                        \x09\x00\x00\x00\x00\x00\x10\x00\x80\x00\x00\xAA\x00\x38\x9B\x71");
        let mut cursor = Cursor::new(vec.clone());

        assert_matches!(Err(ReadError::Format(FormatErrorKind::NotAnUncompressedPcmWaveFile(_))),
            			cursor.read_wave_header());
    }

    #[test]
    fn test_validate_pcm_header_extended_format_sample_rates_dont_match() {
        let mut vec = Vec::new();
        vec.extend_from_slice(b"RIFF    WAVE\
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
		                        \x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00");
        let mut cursor = Cursor::new(vec.clone());

        assert_matches!(Err(ReadError::Format(FormatErrorKind::InvalidBitsPerSample(_, _))),
                        cursor.read_wave_header());
    }

    #[test]
    fn test_validate_pcm_header_extended_format_sample_rates_ok() {
        let mut vec = Vec::new();
        vec.extend_from_slice(b"RIFF    WAVE\
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
	                            \x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00");
        let mut cursor = Cursor::new(vec.clone());

        assert_matches!(Ok(_), cursor.read_wave_header());
    }

    #[test]
    fn test_validate_pcm_header_8bit_mono_example_extended() {
        let mut vec = Vec::new();
        vec.extend_from_slice(b"RIFF    WAVE\
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
		                        \x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00");
        let mut cursor = Cursor::new(vec.clone());

        assert_matches!(Ok(PcmFormat {
                            num_channels: 1,
                            sample_rate: 44100,
                            bits_per_sample: 8,
                        }),
                        cursor.read_wave_header());
    }

    #[test]
    fn test_validate_extended_format_too_short() {
        // Extended size is less than 22 -- should fail.
        let mut data = Cursor::new(b"\x0F\x00\x00\x00");
        assert_matches!(Err(ReadError::Format(FormatErrorKind::FmtChunkTooShort)),
                        data.validate_extended_format(16));
    }

    #[test]
    fn test_validate_extended_format_not_pcm() {
        let mut data = Cursor::new(b"\x16\x00\
                                     \x10\x00\
                                     \x00\x00\x00\x00\
                                     \xFF\xFF\x00\x00\x00\x00\x00\x00\
                                     \x00\x00\x00\x00\x00\x00\x00\x00");
        assert_matches!(Err(ReadError::Format(FormatErrorKind::NotAnUncompressedPcmWaveFile(_))),
            			data.validate_extended_format(16));
    }

    #[test]
    fn test_validate_extended_format_sample_rate_doesnt_match() {
        let mut data = Cursor::new(b"\x16\x00\
                                     \x0F\x00\
                                     \x00\x00\x00\x00\
                                     \x01\x00\x00\x00\x00\x00\x00\x00\
                                     \x00\x00\x00\x00\x00\x00\x00\x00");
        assert_matches!(Err(ReadError::Format(FormatErrorKind::InvalidBitsPerSample(_, _))),
            			data.validate_extended_format(16));
    }

    #[test]
    fn test_validate_extended_format_sample_rate_ok() {
        let mut data = Cursor::new(b"\x16\x00\
                                     \x10\x00\
                                     \x00\x00\x00\x00\
                                     \x01\x00\x00\x00\x00\x00\x00\x00\
                                     \x00\x00\x00\x00\x00\x00\x00\x00");
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
    fn test_data_begin_and_data_end_with_empty_data_chunk() {
        let mut vec = Vec::new();
        vec.extend_from_slice(b"RIFF    WAVE\
	                            fmt \x10\x00\x00\x00\
	                            \x01\x00\
	                            \x01\x00\
	                            \x44\xAC\x00\x00\
	                            \x00\x00\x00\x00\
	                            \x00\x00\
	                            \x08\x00\
	                            data\x00\x00\x00\x00");
        let cursor = Cursor::new(vec.clone());
        let wave_reader = WaveReader::new(cursor).unwrap();

        // No data
        assert_eq!(44, wave_reader.data_begin);
        assert_eq!(44, wave_reader.data_end);
    }

    #[test]
    fn test_data_begin_and_data_end_with_some_data_chunk() {
        let mut vec = Vec::new();
        vec.extend_from_slice(b"RIFF    WAVE\
	                            fmt \x10\x00\x00\x00\
	                            \x01\x00\
	                            \x01\x00\
	                            \x44\xAC\x00\x00\
	                            \x00\x00\x00\x00\
	                            \x00\x00\
	                            \x08\x00\
	                            data\x10\x00\x00\x00\
	                            \x00\x00\x00\x00\
	                            \x00\x00\x00\x00\
	                            \x00\x00\x00\x00\
	                            \x00\x00\x00\x00");
        let cursor = Cursor::new(vec.clone());
        let wave_reader = WaveReader::new(cursor).unwrap();

        // 16 bytes of data
        assert_eq!(44, wave_reader.data_begin);
        assert_eq!(60, wave_reader.data_end);
    }

    #[test]
    fn test_reading_data_from_data_chunk_u8() {
        let mut vec = Vec::new();
        vec.extend_from_slice(b"RIFF    WAVE\
	                            fmt \x10\x00\x00\x00\
	                            \x01\x00\
	                            \x01\x00\
	                            \x44\xAC\x00\x00\
	                            \x00\x00\x00\x00\
	                            \x00\x00\
	                            \x08\x00\
	                            data\x10\x00\x00\x00\
	                            \x00\x01\x02\x03\
	                            \x04\x05\x06\x07\
	                            \x08\x09\x0A\x0B\
	                            \x0C\x0D\x0E\x0F");

        let cursor = Cursor::new(vec.clone());
        let mut wave_reader = WaveReader::new(cursor).unwrap();

        // Buf size 0
        let mut empty_buf: [u8; 0] = [0; 0];
        let empty_read_result = wave_reader.read_samples_as_u8(&mut empty_buf).unwrap();
        assert_eq!(0, empty_read_result);

        // Buf size less than remaining:
        let mut small_buf: [u8; 4] = [0; 4];
        let small_read_result = wave_reader.read_samples_as_u8(&mut small_buf).unwrap();
        assert_eq!(4, small_read_result);

        assert_eq!(0, small_buf[0]);
        assert_eq!(1, small_buf[1]);
        assert_eq!(2, small_buf[2]);
        assert_eq!(3, small_buf[3]);

        // Buf size greater than remaining
        let mut large_buf: [u8; 64] = [0; 64];
        let large_read_result = wave_reader.read_samples_as_u8(&mut large_buf).unwrap();
        assert_eq!(12, large_read_result);

        for i in 0..12 {
            assert_eq!(i + 4 as u8, large_buf[i as usize]);
        }

        // Initialize a new wave reader so we can test one more scenario
        let cursor = Cursor::new(vec.clone());
        let mut wave_reader = WaveReader::new(cursor).unwrap();

        // First, a small read:
        let mut small_buf: [u8; 2] = [0; 2];
        let _ = wave_reader.read_samples_as_u8(&mut small_buf).unwrap();

        // Buf size equal to remaining
        let mut matching_buf: [u8; 14] = [0; 14];
        let matching_read_result = wave_reader.read_samples_as_u8(&mut matching_buf).unwrap();
        assert_eq!(14, matching_read_result);

        for i in 0..14 {
            assert_eq!(i + 2 as u8, matching_buf[i as usize]);
        }
    }

    #[test]
    fn test_reading_data_from_data_chunk_i16() {
        let mut vec = Vec::new();
        vec.extend_from_slice(b"RIFF    WAVE\
                                fmt \x10\x00\x00\x00\
                                \x01\x00\
                                \x01\x00\
                                \x88\x58\x01\x00\
                                \x00\x00\x00\x00\
                                \x00\x00\
                                \x10\x00\
                                data\x10\x00\x00\x00\
                                \x00\x01\x01\x01\
                                \x02\x01\x03\x01\
                                \x04\x01\x05\x01\
                                \x06\x01\x07\x01");

        let cursor = Cursor::new(vec.clone());
        let mut wave_reader = WaveReader::new(cursor).unwrap();

        // Buf size 0
        let mut empty_buf: [i16; 0] = [0; 0];
        let empty_read_result = wave_reader.read_samples_as_i16(&mut empty_buf).unwrap();
        assert_eq!(0, empty_read_result);

        // Buf size less than remaining:
        let mut small_buf: [i16; 3] = [0; 3];
        let small_read_result = wave_reader.read_samples_as_i16(&mut small_buf).unwrap();
        assert_eq!(3, small_read_result);

        assert_eq!(256, small_buf[0]);
        assert_eq!(257, small_buf[1]);
        assert_eq!(258, small_buf[2]);

        // Buf size greater than remaining
        let mut large_buf: [i16; 64] = [0; 64];
        let large_read_result = wave_reader.read_samples_as_i16(&mut large_buf).unwrap();
        assert_eq!(5, large_read_result);

        for i in 0..5 {
            assert_eq!(i + 3 + 256 as i16, large_buf[i as usize]);
        }

        // Initialize a new wave reader so we can test one more scenario
        let cursor = Cursor::new(vec.clone());
        let mut wave_reader = WaveReader::new(cursor).unwrap();

        // First, a small read:
        let mut small_buf: [i16; 2] = [0; 2];
        let _ = wave_reader.read_samples_as_i16(&mut small_buf).unwrap();

        // Buf size equal to remaining
        let mut matching_buf: [i16; 6] = [0; 6];
        let matching_read_result = wave_reader.read_samples_as_i16(&mut matching_buf).unwrap();
        assert_eq!(6, matching_read_result);

        for i in 0..6 {
            assert_eq!(i + 2 + 256 as i16, matching_buf[i as usize]);
        }
    }
}
