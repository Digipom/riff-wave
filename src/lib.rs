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

// This is a helper macro that helps us validate results in our tests. It has
// to be defined before the mod definitions below so that it's visible in those
// mods.
// Thank you bluss and durka42!
#[cfg(test)]
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

mod reader;
mod writer;

pub use self::reader::{ReadError, ReadErrorKind, ReadResult, WaveReader};
pub use self::writer::{WaveWriter, WriteError, WriteErrorKind, WriteResult};

pub const FORMAT_UNCOMPRESSED_PCM: u16 = 1;
pub const FORMAT_EXTENDED: u16 = 65534;

pub const MIN_I24_VALUE: i32 = -8388608;
pub const MAX_I24_VALUE: i32 = 8388607;

#[derive(Debug)]
pub enum Format {
    UncompressedPcm,
    Extended,
}

#[derive(Debug)]
pub struct PcmFormat {
    pub num_channels: u16,
    pub sample_rate: u32,
    pub bits_per_sample: u16,
}
