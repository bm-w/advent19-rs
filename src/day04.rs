// Copyright (c) 2022 Bastiaan Marinus van de Weerd


const INPUT: &str = "178416-676461";


struct Range {
	from: u64,
	through: u64,
}


trait MaybePassword: AsRef<[u8]> {
	fn contains_double(&self) -> bool {
		use itertools::Itertools;
		self.as_ref().iter().tuple_windows().any(|(l, r)| l == r)
	}

	fn contains_strict_double(&self) -> bool {
		use itertools::Itertools;
		let bytes = self.as_ref();
		let l = bytes.len();
		if l <= 2 { return self.contains_double() }

		bytes[0] == bytes[1] && bytes[1] != bytes[2]
			|| self.as_ref().iter().tuple_windows().any(|(p, l, r, n)|
				p != l && l == r && r != n)
			|| bytes[l - 3] != bytes[l - 2] && bytes[l - 2] == bytes[l - 1]
	}

	fn contains_decreasing_digits(&self) -> bool {
		use itertools::Itertools;
		self.as_ref().iter().tuple_windows().any(|(l, r)| l > r)
	}

	fn is_valid(&self) -> bool {
		self.contains_double() && !self.contains_decreasing_digits()
	}

	fn is_strictly_valid(&self) -> bool {
		self.contains_strict_double() && !self.contains_decreasing_digits()
	}
}

impl MaybePassword for String {}


fn input_range() -> Range {
	INPUT.parse().unwrap()
}


pub(crate) fn part1() -> usize {
	let Range { from, through } = input_range();
	(from..=through)
		.filter(|value| value.to_string().is_valid())
		.count()
}


pub(crate) fn part2() -> usize {
	let Range { from, through } = input_range();
	(from..=through)
		.filter(|value| value.to_string().is_strictly_valid())
		.count()
}


mod parsing {
	use std::{num::ParseIntError, str::FromStr};
	use super::Range;

	#[derive(Debug)]
	pub(super) enum RangeError {
		Format,
		Min(ParseIntError),
		Max(ParseIntError),
	}

	impl FromStr for Range {
		type Err = RangeError;
		fn from_str(s: &str) -> Result<Self, Self::Err> {
			let (from, through) = s.split_once('-')
				.ok_or(RangeError::Format)?;
			let from = from.parse()
				.map_err(RangeError::Min)?;
			let through = through.parse()
				.map_err(RangeError::Max)?;
			Ok(Range { from, through })
		}
	}
}


#[test]
fn tests() {
	assert_eq!(part1(), 1650);
	assert_eq!(part2(), 1129);
}
