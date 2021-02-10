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
use std::io::{BufReader, BufWriter};
use std::f32::consts::PI;

use riff_wave::{ReadResult, WaveReader, WaveWriter, WriteResult};

fn main() {
	write_wave().unwrap();
	let _ = read_wave();
}

fn write_wave() -> WriteResult<()> {		
	const SAMPLE_RATE: u32 = 44100;
	const FREQUENCY: f32 = 2.0 * PI * 440.0; // radian per second

	let file = File::create("examples/hello.wav")?;
	let writer = BufWriter::new(file);

	let mut wave_writer = WaveWriter::new(1, SAMPLE_RATE, 16, writer)?;

	for n in 0..SAMPLE_RATE {
		let phase = FREQUENCY * n as f32 / SAMPLE_RATE as f32;
		let sample = (phase.sin() * 0.8 * i16::MAX as f32) as i16;

		wave_writer.write_sample_i16(sample)?;
	}

	Ok(())
}

fn read_wave() -> ReadResult<()> {
	let file = File::open("examples/hello.wav")?;
	let reader = BufReader::new(file);
	let mut wave_reader = WaveReader::new(reader)?;

	loop {
		wave_reader.read_sample_i16()?;
	}
}