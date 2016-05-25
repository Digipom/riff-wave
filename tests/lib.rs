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

extern crate riff_wave;

use std::fs::File;

use riff_wave::WaveReader;

// MARK: "Standard" PCM wave formats.

#[test]
fn test_header_for_standard_file_8bit_mono_16000() {
	let file = File::open("tests/pcm_8bit_mono_16000_standard.wav").unwrap();
	let wave_reader = WaveReader::new(file).unwrap();
	assert_eq!(1, wave_reader.pcm_format.num_channels);
	assert_eq!(16000, wave_reader.pcm_format.sample_rate);
	assert_eq!(8, wave_reader.pcm_format.bits_per_sample);
}

#[test]
fn test_header_for_standard_file_16bit_mono_44100() {
	let file = File::open("tests/pcm_16bit_mono_44100_standard.wav").unwrap();
	let wave_reader = WaveReader::new(file).unwrap();
	assert_eq!(1, wave_reader.pcm_format.num_channels);
	assert_eq!(44100, wave_reader.pcm_format.sample_rate);
	assert_eq!(16, wave_reader.pcm_format.bits_per_sample);
}

#[test]
fn test_header_for_standard_file_16bit_stereo_44100() {
	let file = File::open("tests/pcm_16bit_stereo_44100_standard.wav").unwrap();
	let wave_reader = WaveReader::new(file).unwrap();
	assert_eq!(2, wave_reader.pcm_format.num_channels);
	assert_eq!(44100, wave_reader.pcm_format.sample_rate);
	assert_eq!(16, wave_reader.pcm_format.bits_per_sample);
}

#[test]
fn test_header_for_standard_file_16bit_stereo_44100_with_cb() {
	let file = File::open("tests/pcm_16bit_stereo_44100_standard_with_cb.wav").unwrap();
	let wave_reader = WaveReader::new(file).unwrap();
	assert_eq!(2, wave_reader.pcm_format.num_channels);
	assert_eq!(44100, wave_reader.pcm_format.sample_rate);
	assert_eq!(16, wave_reader.pcm_format.bits_per_sample);
}

// MARK: "Extended" PCM wave formats.

#[test]
fn test_header_for_extended_file_32bit_stereo_44100() {
	let file = File::open("tests/pcm_32bit_stereo_44100_extended.wav").unwrap();
	let wave_reader = WaveReader::new(file).unwrap();
	assert_eq!(2, wave_reader.pcm_format.num_channels);
	assert_eq!(44100, wave_reader.pcm_format.sample_rate);
	assert_eq!(32, wave_reader.pcm_format.bits_per_sample);
}

// MARK: Data tests

#[test]
fn test_header_for_standard_file_8bit_mono_16000_with_data() {
	let file = File::open("tests/pcm_8bit_mono_16000_standard_with_data.wav").unwrap();
	let mut wave_reader = WaveReader::new(file).unwrap();
	assert_eq!(1, wave_reader.pcm_format.num_channels);
	assert_eq!(16000, wave_reader.pcm_format.sample_rate);
	assert_eq!(8, wave_reader.pcm_format.bits_per_sample);

	for i in 0..16 {
		let next_sample = wave_reader.read_sample_u8().unwrap();
		assert_eq!(i as u8, next_sample);
	}
}