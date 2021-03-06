# riff-wave
Simple methods for reading and writing PCM wave files.

## Examples

### Reading a wave file

```rust
extern crate riff_wave;

use std::fs::File;
use std::io::BufReader;

use riff_wave::{ReadResult, WaveReader};

fn read_wave() -> ReadResult<()> {
	let file = File::open("examples/hello.wav")?;
	let reader = BufReader::new(file);
	let mut wave_reader = WaveReader::new(reader)?;

	loop {
		wave_reader.read_sample_i16()?;
	}	
}
```

### Writing a wave file

```rust
extern crate riff_wave;

use std::f32::consts::PI;
use std::fs::File;
use std::io::BufWriter;

use riff_wave::{WaveWriter, WriteResult};

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
```

## Documentation

Documentation is available via `cargo doc` or [via this link](https://digipom.github.io/riff-wave/doc/riff_wave/index.html).
