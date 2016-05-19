extern crate riff_wave;

use std::fs::File;

use riff_wave::WaveReader;

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