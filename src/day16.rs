// Copyright (c) 2022 Bastiaan Marinus van de Weerd


fn nonzero_ranges(offset: usize, end: usize) -> impl Iterator<Item = (std::ops::Range<usize>, bool)> {
	use std::{iter::from_fn, mem::replace};
	let len = offset + 1;
	let mut start = len - 1;
	let mut positive = true;
	from_fn(move || {
		if start >= end { return None }
		let end = (start + len).min(end);
		let range = replace(&mut start, end + len)..end;
		let next_positive = !positive;
		Some((range, replace(&mut positive, next_positive)))
	})
}


struct DisplaySequence([u8; 8]);

impl std::fmt::Display for DisplaySequence {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		use std::fmt::Write;
		for d in self.0 { f.write_char((b'0' + d) as char)? }
		Ok(())
	}
}


fn part1and2_impl<const N: usize>(input_offset: usize, mut input_sequence: impl AsMut<[u8]>) -> impl std::fmt::Display {
	let sequence = input_sequence.as_mut();
	assert!(sequence.len() >= 8);

	#[allow(clippy::uninit_vec)]
	let mut working_sequence = {
		let mut v = Vec::with_capacity(sequence.len());
		// SAFETY: Bunch of `u8` garbage that’s never read before it’s written to
		unsafe { v.set_len(sequence.len()) }
		v
	};

	for _ in 0..N {
		for (i, elt) in working_sequence.iter_mut().enumerate() {
			*elt = (nonzero_ranges(input_offset + i, input_offset + sequence.len())
				.map(|(r, p)| (r.start - input_offset..r.end - input_offset, p))
				.fold(0, |acc, (range, positive)|
					acc + sequence[range].iter().map(|&v| v as i64).sum::<i64>()
							* if positive { 1 } else {-1 })
				.abs() % 10) as u8;
		}
		sequence.copy_from_slice(&working_sequence[..]);
	}

	let mut output = [0u8; 8];
	output.copy_from_slice(&sequence[..8]);
	DisplaySequence(output)
}


fn input_sequence_from_str(s: &str) -> impl AsMut<[u8]> {
	parsing::try_sequence_from_str(s).unwrap()
}

fn part1_impl<const N: usize>(input_sequence: impl AsMut<[u8]>) -> impl std::fmt::Display {
	part1and2_impl::<N>(0, input_sequence)
}

pub(crate) fn part1() -> impl std::fmt::Display {
	part1_impl::<100>(input_sequence_from_str(include_str!("day16.txt")))
}


const REPS: usize = 10_000;

fn input_offset_and_sequence_from_str(s: &str) -> (usize, impl AsMut<[u8]>) {
	parsing::try_offset_and_sequence_from_str(s).unwrap()
}

fn part2_impl((input_offset, mut input_sequence): (usize, impl AsMut<[u8]>)) -> impl std::fmt::Display {
	let input_sequence = input_sequence.as_mut();
	let total_sequence_len = input_sequence.len() * REPS;

	// Only deal with the leading range of exclusively ones in the base patterns
	assert!((input_offset + 1) * 2 >= total_sequence_len);

	// TODO(bm-w): Constant space?
	let sequence_suffix_len = total_sequence_len - input_offset;
	let mut sequence_suffix = Vec::with_capacity(sequence_suffix_len);
	let part_sequence_offset = input_offset % input_sequence.len();
	for (i, elt) in sequence_suffix.spare_capacity_mut().iter_mut().enumerate() {
		elt.write(input_sequence[(part_sequence_offset + i) % input_sequence.len()]);
	}
	unsafe { sequence_suffix.set_len(sequence_suffix_len); }

	for _ in 0..100 {
		// Work backwards; the last element in `sequence_suffix` never changes
		for i in (0..total_sequence_len - input_offset - 1).rev() {
			sequence_suffix[i] = (sequence_suffix[i] + sequence_suffix[i + 1]) % 10;
		}
	}

	let mut output = [0u8; 8];
	output.copy_from_slice(&sequence_suffix[..8]);
	DisplaySequence(output)
}

pub(crate) fn part2() -> impl std::fmt::Display {
	part2_impl(input_offset_and_sequence_from_str(include_str!("day16.txt")))
}


mod parsing {
	use std::num::ParseIntError;

	#[allow(dead_code)]
	#[derive(Debug)]
	pub(super) enum SequenceError {
		Len(usize),
		Char { column: usize, found: char }
	}

	pub(super) fn try_sequence_from_str(s: &str) -> Result<impl AsMut<[u8]>, SequenceError> {
		if s.len() < 8 { return Err(SequenceError::Len(s.len())) }
		s.chars()
			.enumerate()
			.map(|(c, chr)| chr.to_digit(10)
				.map(|d| d as u8)
				.ok_or(SequenceError::Char { column: c + 1, found: chr }))
			.collect::<Result<Vec<_>, _>>()
	}

	#[allow(dead_code)]
	#[derive(Debug)]
	pub(super) enum OffsetError {
		Len(usize),
		Int(ParseIntError)
	}

	fn try_offset_from_str(s: &str) -> Result<usize, OffsetError> {
		if s.len() < 7 { return Err(OffsetError::Len(s.len())) }
		s[..7].parse().map_err(OffsetError::Int)
	}

	#[derive(Debug)]
	pub(super) enum Error {
		Offset(OffsetError),
		Sequence(SequenceError),
	}

	pub(super) fn try_offset_and_sequence_from_str(s: &str) -> Result<(usize, impl AsMut<[u8]>), Error> {
		let offset = try_offset_from_str(s).map_err(Error::Offset)?;
		let sequence = try_sequence_from_str(s).map_err(Error::Sequence)?;
		Ok((offset, sequence))
	}
}


#[test]
fn tests() {
	assert_eq!(part1_impl::<4>(input_sequence_from_str("12345678")).to_string(), "01029498");
	assert_eq!(part1_impl::<100>(input_sequence_from_str("80871224585914546619083218645595")).to_string(), "24176176");
	assert_eq!(part1_impl::<100>(input_sequence_from_str("19617804207202209144916044189917")).to_string(), "73745418");
	assert_eq!(part1_impl::<100>(input_sequence_from_str("69317163492948606335995924319873")).to_string(), "52432133");
	assert_eq!(part1().to_string(), "82435530");
	assert_eq!(part2_impl(input_offset_and_sequence_from_str("03036732577212944063491565474664")).to_string(), "84462026");
	assert_eq!(part2_impl(input_offset_and_sequence_from_str("02935109699940807407585447034323")).to_string(), "78725270");
	assert_eq!(part2_impl(input_offset_and_sequence_from_str("03081770884921959731165446850517")).to_string(), "53553731");
	assert_eq!(part2().to_string(), "83036156");
}
