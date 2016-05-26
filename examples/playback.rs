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

extern crate decibel;
extern crate riff_wave;

#[cfg(target_os = "macos")]
extern crate coreaudio;

use std::env;
use std::f32;
use std::fs::File;
use std::io;
use std::io::{BufReader, BufWriter, Read, Seek, Write};
use std::path::{Path, PathBuf};

use decibel::{AmplitudeRatio, DecibelRatio};

use riff_wave::{WaveReader, WaveWriter};

#[cfg(target_os = "macos")]
use coreaudio::audio_unit::{AudioUnit, IOType, SampleFormat};
#[cfg(target_os = "macos")]
use coreaudio::audio_unit::render_callback::{self, data};

fn main() {
	do_playback();
}

#[cfg(target_os = "macos")]
fn do_playback() {
	do_playback_with_core_audio().unwrap();
}

#[cfg(not(target_os = "macos"))]
fn do_playback() {
	panic!("Not implemented");
}

#[cfg(target_os = "macos")]
fn do_playback_with_core_audio() -> Result<(),  coreaudio::Error> {	
	// Based this off the coreaudio example from the coreaudio crate.
	// There's probably a better way of doing this, but I had issues getting
	// the other crates to compile. This works at least as a basic example.
	let mut audio_unit = try!(AudioUnit::new(IOType::DefaultOutput));
	let stream_format = try!(audio_unit.stream_format());
	assert!(SampleFormat::F32 == stream_format.sample_format);

	let path = get_temporary_file_path("sine_wave_44100.wav");
	let buf_writer = get_buffered_writer_for_path(&path).unwrap();
	let decibel_ratio = DecibelRatio(-3f32);
	write_test_sine_wave(buf_writer, 250, decibel_ratio);
		
	let buf_reader = get_buffered_reader_for_path(&path).unwrap();
	let mut wave_reader = WaveReader::new(buf_reader).unwrap();	

	assert_eq!(1, wave_reader.pcm_format.num_channels);
	assert_eq!(44100, wave_reader.pcm_format.sample_rate);
	assert_eq!(16, wave_reader.pcm_format.bits_per_sample);

	std::thread::sleep(std::time::Duration::from_millis(50));

	try!(audio_unit.set_render_callback(move |args| callback(args, &mut wave_reader)));
    try!(audio_unit.start());
    
    std::thread::sleep(std::time::Duration::from_millis(3000));

	Ok(())
}

fn get_temporary_file_path(name: &str) -> PathBuf {
	let mut path = env::temp_dir();
	path.push(name);
	path
}

fn get_buffered_reader_for_path(path: &Path) -> io::Result<BufReader<File>> {
	let file = try!(File::open(path));
	let output_reader = BufReader::new(file);	
	Ok(output_reader)
}

fn get_buffered_writer_for_path(path: &Path) -> io::Result<BufWriter<File>> {	
	let file = try!(File::create(path));
	let output_writer = BufWriter::new(file);	
	Ok(output_writer)
}

fn write_test_sine_wave<T>(writer: T, hz: u32, scale: DecibelRatio<f32>) where T: Write + Seek {	
	let mut wave_writer = WaveWriter::new(1, 44100, 16, writer).unwrap();

	for n in 0..44100 * 3 {
		let x = sine_wave(n, hz, scale, 44100);
		let x = (x * 32767.0) as i16;
		wave_writer.write_sample_i16(x).unwrap();
	}	
}

fn sine_wave(n: u32, hz: u32, scale: DecibelRatio<f32>, sample_rate: u32) -> f32 {
	// 2 PI = one cycle
	let ratio_per_second = 2.0 * f32::consts::PI * hz as f32;
	let ratio = n as f32 / sample_rate as f32;
	let x = ratio * ratio_per_second;
	let amplitude_ratio: AmplitudeRatio<_> = scale.into();
	x.sin() * amplitude_ratio.amplitude_value()
}

#[cfg(target_os = "macos")]
type Args<'a> = render_callback::Args<'a, data::NonInterleaved<'a, f32>>;

#[cfg(target_os = "macos")]
fn callback<'a, T: Read + Seek>(args: Args<'a>, wave_reader: &mut WaveReader<T>) -> Result<(), ()> {
    let Args { num_frames, mut data, .. } = args;
    
    for i in 0..num_frames {
    	match wave_reader.read_sample_i16() {
    		Ok(sample) => {
    			for channel in data.channels_mut() {
		            channel[i] = sample as f32 / 32768f32;
		        }
    		},
    		Err(_) => {
    			for channel in data.channels_mut() {
		            channel[i] = 0f32;
		        }	
    		},
    	}    	
    }
    Ok(())
}