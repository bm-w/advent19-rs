// Copyright (c) 2022 Bastiaan Marinus van de Weerd

// TODO(bm-w): Find solution programmatically (found by reasoning now)?

use crate::day05::{parsing::from_str as input_program_from_str, self};


#[cfg(test)]
#[cfg_attr(test, derive(Debug))]
struct Render {
	hull: Vec<bool>,
	jumped: Option<usize>,
	fell: usize,
}

#[derive(Debug)]
enum ProgramExecutionError {
	Internal(String),
	InvalidOutput,
	UnconsumedInput,
	UnexpectedEnd,
	#[cfg(test)]
	DidntMakeIt(Render),
	#[cfg(not(test))]
	DidntMakeIt(String),
}

trait Program: day05::Program<'static, i64> {
	fn execute(&mut self, input: impl AsRef<str>) -> Result<usize, ProgramExecutionError> {
		use std::iter::{empty, from_fn};

		let walking = input.as_ref().ends_with("WALK\n");
		let mut state = day05::ProgramState::new(true);

		#[cfg(test)]
		let mut dbg_output = Vec::new();

		macro_rules! safe_output {
			( $input:expr ) => { match self.safe_output(&mut state, $input) {
				Ok(Some(num)) => { #[cfg(test)] dbg_output.push(num); num },
				Ok(None) => return Err(ProgramExecutionError::UnexpectedEnd),
				Err(err) => return Err(ProgramExecutionError::Internal(err)),
			} };
			() => { safe_output!(empty()) }
		}

		macro_rules! invalid_output { ( $label:literal ) => { {
			#[cfg(test)]
			{
				let dbg_output_string = unsafe { String::from_utf8_unchecked(dbg_output.iter()
					.map_while(|&num| u8::try_from(num).ok())
					.collect::<Vec<_>>()) };
				println!("Invalid output ({}): {:?}{}",
					$label,
					dbg_output_string,
					if dbg_output_string.len() < dbg_output.len() {
						format!(" + {:?}", &dbg_output[dbg_output_string.len()..])
					} else { "".to_owned() });
			};
			return Err(ProgramExecutionError::InvalidOutput)
		} } }


		for b in "Input instructions:\n".bytes() {
			if safe_output!() != b as i64 { invalid_output!('A') }
		}

		let mut input = input.as_ref().bytes().map(|b| b as i64);
		if safe_output!(&mut input) != b'\n' as i64 {
			invalid_output!('B')
		} else if input.next().is_some() {
			return Err(ProgramExecutionError::UnconsumedInput)
		}

		for b in if walking { "Walking...\n\n" } else { "Running...\n\n" }.bytes() {
			if safe_output!() != b as i64 { invalid_output!('C') }
		}

		match safe_output!() {
			num if num > u8::MAX as i64 => return Ok(num as usize),
			num if num != b'\n' as i64 => invalid_output!('D'),
			_ => (),
		};

		for b in "Didn't make it across:\n\n".bytes() {
			if safe_output!() != b as i64 { invalid_output!('E') }
		}

		let render = from_fn(|| self.safe_output(&mut state, empty()).transpose())
			.map(|n| n.map(|n| (n as u8) as char))
			.collect::<Result<String, _>>()
			.map_err(ProgramExecutionError::Internal)?;

		#[cfg(test)]
		let render = match render.parse::<Render>() {
			Ok(render) => render,
			Err(err) => { println!("Render parsing error:\n{err:?}"); invalid_output!('F') }
		};

		Err(ProgramExecutionError::DidntMakeIt(render))
	}
}

impl<T> Program for T where T: day05::Program<'static, i64> {}



fn input_program() -> impl Program {
	input_program_from_str(include_str!("day21.txt"))
}


macro_rules! unwrap_or_render { ( $result:expr ) => { match $result {
	Ok(damage) => damage,
	Err(ProgramExecutionError::DidntMakeIt(render)) =>
		panic!("Didn’t make it; render:\n{render}"),
	Err(err) => { panic!("Execution error: {err:?}") },
} }}


pub(crate) fn part1() -> usize {
	// Not much to compute here; only jump if:
	//  -  there is a hole at A, B, or C;
	//  -  there is hull to jump to at D.
	unwrap_or_render!(input_program().execute(indoc::indoc! { "
		NOT A J
		NOT B T
		OR T J
		NOT C T
		OR T J
		AND D J
		WALK
	" }))
}


pub(crate) fn part2() -> usize {
	// Again, not much to compute here; only jump if:
	//  -  there is a hole at A, B, or C;
	//  -  there is hull to jump to at D;
	//  -  either of:
	//      *  there is hull to run to at E (using double `NOT`);
	//      *  there is hull to jump to at H.
	unwrap_or_render!(input_program().execute(indoc::indoc! { "
		NOT A J
		NOT B T
		OR T J
		NOT C T
		OR T J
		AND D J
		NOT E T
		NOT T T
		OR H T
		AND T J
		RUN
	" }))
}


#[cfg(test)]
mod parsing {
	use std::str::FromStr;
	use super::Render;

	#[allow(dead_code)]
	#[derive(Debug)]
	pub(super) enum RenderError {
		Empty,
		LineLen { line: usize, width: Option<usize>, len: usize },
		Char { line: usize, column: usize, found: char },
		UnexpectedJump { line: usize, column: usize, jumped: usize },
		UnexpectedFall { line: usize, column: usize, fell: usize },
		DuplicateDroid { line: usize, column: usize, prev_line: usize, prev_column: usize },
		FrameMismatch { line: usize, column: usize, hull: bool },
		MissingFall
	}

	impl FromStr for Render {
		type Err = RenderError;
		fn from_str(s: &str) -> Result<Self, Self::Err> {
			use RenderError::*;

			if s.is_empty() { return Err(Empty) }

			let mut hull = Vec::new();
			let mut jumped = None;
			let mut fell = None;
			let mut l = 0;
			for frame in s.split("\n\n") {
				let mut droid = Option::<[usize; 2]>::None;
				for line in frame.lines() {
					for (c, b) in line.bytes().enumerate() {
						match b {
							_ if l > 0 && c == hull.len() => break,
							b'@' => {
								if let Some([prev_l, prev_c]) = droid {
									return Err(DuplicateDroid {
										line: l + 1, column: c + 1,
										prev_line: prev_l + 1, prev_column: prev_c + 1,
									})
								} else {
									droid = Some([l, c])
								}

								if l % 5 == 1 {
									if let Some(jumped) = jumped {
										if jumped != c - 3 {
											dbg!(jumped, c);
											println!("{s}");
											return Err(UnexpectedJump {
												line: l + 1, column: c + 1, jumped })
										}
									} else {
										jumped = Some(c - 1)
									}
								} else if l % 5 == 3 {
									if let Some(fell) = fell {
										return Err(UnexpectedFall {
											line: l + 1, column: c + 1, fell })
									} else {
										fell = Some(c)
									}
								}
							}
							b'#' | b'.' if l == 3 => hull[c] = b == b'#',
							b'#' | b'.' if l % 5 == 3 => if (b == b'#') ^ hull[c] {
								return Err(FrameMismatch {
									line: l + 1, column: c + 1, hull: hull[c] })
							}
							b'.' => (),
							found => return Err(Char {
								line: l + 1, column: c + 1, found: found as char }),
						}
					}

					if l == 0 && !line.is_empty() { hull = vec![false; line.len()] }

					if line.is_empty() || line.len() != hull.len() {
						let width = match hull.len() { 0 => None, len => Some(len) };
						return Err(LineLen { line: l + 1, width, len: line.len() })
					}

					l += 1;
				}
				l += 1;
			}

			Ok(Render { hull, fell: fell.ok_or(MissingFall)?, jumped })
		}
	}
}


#[cfg(test)]
impl std::fmt::Display for Render {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		use std::fmt::Write;
		let w = self.hull.len();
		for y in 0..4 {
			for x in 0..w {
				f.write_char(match [x, y] {
					[j, 2] if Some(j) == self.jumped => '^',
					[j, 1] if j > 1 && Some(j - 1) == self.jumped => '^',
					[j, 0] if j > 2 && Some(j - 2) == self.jumped => '>',
					[j, 1] if j > 3 && Some(j - 3) == self.jumped => 'v',
					[j, 2] if j > 4 && Some(j - 4) == self.jumped => 'v',
					[f, 3] if f == self.fell => '@',
					[h, 3] if self.hull[h] => '#',
					_ => '.'
				})?;
			}
			f.write_char('\n')?;
		}
		Ok(())
	}
}


#[test]
fn tests() {
	assert_eq!(part1(), 19357290);
	assert_eq!(part2(), 1136394042);
}
