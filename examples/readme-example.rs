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

use riff_wave::{ReadResult, WaveReader, WaveWriter, WriteResult};

fn main() {
	write_wave().unwrap();
	let _ = read_wave();
}

fn write_wave() -> WriteResult<()> {		
	let file = try!(File::create("examples/hello.wav"));
	let writer = BufWriter::new(file);
	let mut wave_writer = try!(WaveWriter::new(1, 44100, 16, writer));

	for n in 0..10000 {		
		try!(wave_writer.write_sample_i16(n));
	}	

	Ok(())
}

fn read_wave() -> ReadResult<()> {
	let file = try!(File::open("examples/hello.wav"));
	let reader = BufReader::new(file);
	let mut wave_reader = try!(WaveReader::new(reader));

	loop {
		try!(wave_reader.read_sample_i16());
	}	
}	