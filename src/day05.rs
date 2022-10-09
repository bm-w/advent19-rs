// Copyright (c) 2022 Bastiaan Marinus van de Weerd

//! NOTE: The “Intcode computer” of this module is also used in `day07`; for that reason:
//! - various items are `pub(crate)`;
//! - various items implement `Clone`;
//! - `Program` was refactored into to expose the `safe_output` method.


#[derive(Clone, Copy)]
#[cfg_attr(test, derive(Debug))]
pub(crate) enum ParMode { Pos, Imm }

#[derive(Debug)]
pub(crate) enum ArgPos { First, Second }

impl<T> std::ops::Index<ArgPos> for [T] {
	type Output = T;
	fn index(&self, index: ArgPos) -> &Self::Output {
		match index { ArgPos::First => &self[0], ArgPos::Second => &self[1], }
	}
}

#[derive(Clone, Copy)]
#[cfg_attr(test, derive(Debug))]
pub(crate) enum Op {
	Add([ParMode; 2]),
	Mul([ParMode; 2]),
	In,
	Out(ParMode),
	JumpIf(bool, [ParMode; 2]),
	Lt([ParMode; 2]),
	Eq([ParMode; 2]),
	Halt,
}

#[derive(Clone)]
#[cfg_attr(test, derive(Debug))]
pub(crate) enum Int<'a> {
	Op(Op),
	Num(i64),
	Raw { _column: usize, str: &'a str }
}

const PAR_MODE_COEFFS: [i64; 2] = [100, 1000];

impl ParMode {
	fn num(&self) -> i64 {
		use ParMode::*;
		match self { Pos => 0, Imm => 1 }
	}

	fn arg0_num(par_mode: &Self) -> i64 {
		PAR_MODE_COEFFS[ArgPos::First] * par_mode.num()
	}

	fn args_num(par_modes: &[Self; 2]) -> i64 {
		Self::arg0_num(&par_modes[ArgPos::First])
			+ PAR_MODE_COEFFS[ArgPos::Second] * par_modes[ArgPos::Second].num()
	}
}

impl Op {
	fn num(&self) -> i64 {
		match self {
			Op::Add(par_modes) => 1 + ParMode::args_num(par_modes),
			Op::Mul(par_modes) => 2 + ParMode::args_num(par_modes),
			Op::In => 3,
			Op::Out(par_mode) => 4 + ParMode::arg0_num(par_mode),
			Op::JumpIf(true, par_modes) => 5 + ParMode::args_num(par_modes),
			Op::JumpIf(false, par_modes) => 6 + ParMode::args_num(par_modes),
			Op::Lt(par_modes) => 7 + ParMode::args_num(par_modes),
			Op::Eq(par_modes) => 8 + ParMode::args_num(par_modes),
			Op::Halt => 99,
		}
	}
}

impl Int<'_> {
	fn parse_into_op(&mut self) -> Result<Op, parsing::OpError> {
		macro_rules! parse_into_self {
			( $s:expr ) => { {
				use std::str::FromStr;
				match Op::from_str($s) {
					Ok(op) => {
						*self = Int::Op(op);
						let Int::Op(op) = self else { unreachable!() };
						Ok(*op)
					}
					err => err,
				}
			} }
		}
		match self {
			Int::Op(op) => Ok(*op),
			Int::Num(num) => parse_into_self!(&num.to_string()),
			Int::Raw { str, .. } => parse_into_self!(str),
		}
	}

	fn as_num(&self) -> Result<i64, std::num::ParseIntError> {
		use std::str::FromStr;
		match self {
			Int::Op(op) => Ok(op.num()),
			Int::Num(num) => Ok(*num),
			Int::Raw { str, .. } => i64::from_str(str)
		}
	}

	fn parse_into_num(&mut self) -> Result<i64, std::num::ParseIntError> {
		let num = self.as_num()?;
		*self = Int::Num(num);
		Ok(num)
	}

	fn parse_into_pos(&mut self) -> Result<usize, std::num::ParseIntError> {
		self.as_num().map(|num| num as usize)
	}
}

pub(crate) trait Program<'a>: AsMut<[Int<'a>]> + Clone {

	fn safe_output<'b, In>(&'b mut self, offset: &mut usize, mut input: In) -> Result<Option<i64>, String>
	where 'a: 'b, In: Iterator<Item = i64> + 'b {
		loop {
			use {ArgPos::*, Op::*};

			let memory = self.as_mut();
			let eop_err = || Err("Unexpected end of program".to_string());
			if *offset >= memory.len() { return eop_err() }

			macro_rules! parse_pos {
				( $pos:expr ) => {
					memory[$pos].parse_into_pos().map_err(|e|
						format!("Invalid position argument at position {}; source: {e:?}", $pos))?
				}
			}
			macro_rules! parse_memory {
				( $pos:expr, $par_mode:expr, $parse:ident) => { {
					use ParMode::*;
					let pos = match $par_mode { Pos => parse_pos!($pos), Imm => $pos };
					memory[pos].$parse().map_err(|e|
						format!("Invalid immediate argument at position {}: {e:?}", $pos))?
				} }
			}
			macro_rules! parse_memory_num { ( $pos:expr, $par_mode:expr) => { parse_memory!($pos, $par_mode, parse_into_num) } }

			match memory[*offset].parse_into_op().map_err(|e|
					format!("Unexpected non-op instruction at position {offset}: {e:?}"))? {
				Halt => return Ok(None),
				op @ (Add(_) | Mul(_) | Lt(_) | Eq(_)) => {
					if *offset + 3 >= memory.len() { return eop_err() }
					let args = {
						let (Add(pm) | Mul(pm) | Lt(pm) | Eq(pm)) = op else { unreachable!() };
						[parse_memory_num!(*offset + 1, pm[First]), parse_memory_num!(*offset + 2, pm[Second])]
					};
					memory[parse_pos!(*offset + 3)] = Int::Num(match op {
						Add(_) => args[First] + args[Second],
						Mul(_) => args[First] * args[Second],
						Lt(_) => i64::from(args[First] < args[Second]),
						Eq(_) => i64::from(args[First] == args[Second]),
						_ => unreachable!(),
					});
					*offset += 4;
				}
				In => {
					if *offset + 1 >= memory.len() { return eop_err() }
					let dest = parse_pos!(*offset + 1);
					memory[dest] = Int::Num(input.next().ok_or_else(|| "Unexpected end of input".to_string())?);
					*offset += 2;
				}
				Out(par_mode) => {
					if *offset + 1 >= memory.len() { return eop_err() }
					let output = parse_memory_num!(*offset + 1, par_mode);
					*offset += 2;
					return Ok(Some(output))
				}
				JumpIf(flag, par_mode) => {
					if *offset + 2 >= memory.len() { return eop_err() }
					if (parse_memory_num!(*offset + 1, par_mode[First]) != 0) == flag {
						*offset = parse_memory!(*offset + 2, par_mode[Second], parse_into_pos);
					} else {
						*offset += 3;
					}
				}
			}
		}
	}

	// TODO(bm-w): Return `impl Iterator<…>` once Rust allows it from trait methods
	fn execute<'b, In>(&'b mut self, mut input: In) -> Box<dyn Iterator<Item = i64> + 'b>
	where 'a: 'b, In: Iterator<Item = i64> + 'b {
		let mut offset = 0usize;
		Box::new(std::iter::from_fn(move || {
			self.safe_output(&mut offset, &mut input).unwrap()
		}))
	}
}


fn input_program() -> impl Program<'static> {
	parsing::from_str(include_str!("day05.txt"))
}


pub(crate) fn part1() -> i64 {
	input_program()
		.execute(std::iter::once(1))
		.fold(0, |prev, output| {
			if prev != 0 { panic!("Unexpected non-zero output") }
			output
		})
}


pub(crate) fn part2() -> i64 {
	use itertools::Itertools as _;
	input_program()
		.execute(std::iter::once(5))
		.exactly_one()
		.ok().unwrap()
}


pub(crate) mod parsing {
	use super::{ParMode, ArgPos, Op, Int, Program};
	use std::{mem, str::FromStr};

	#[derive(Debug)]
	pub(crate) struct ParModeError(u8);

	impl TryFrom<u8> for ParMode {
		type Error = ParModeError;
		fn try_from(value: u8) -> Result<Self, Self::Error> {
			use ParMode::*;
			match value {
				b'0' => Ok(Pos),
				b'1' => Ok(Imm),
				b => Err(ParModeError(b))
			}
		}
	}

	#[derive(Debug)]
	pub(crate) enum OpError {
		Format,
		Op(u8, Option<u8>),
		ParMode(Option<ParModeError>, ArgPos),
	}

	impl FromStr for Op {
		type Err = OpError;
		fn from_str(s: &str) -> Result<Self, Self::Err> {
			if s.is_empty() || s.len() > 4 { return Err(OpError::Format) }
			let mut bytes_rev = s.bytes().rev().fuse();
			match (bytes_rev.next().unwrap(), bytes_rev.next()) {
				(b'9', Some(b'9')) if bytes_rev.next().is_none() =>
					Ok(Op::Halt),
				(b0, b1 @ (None | Some(b'0'))) => {
					fn par_mode<I>(bytes: &mut I, pos: ArgPos) -> Result<ParMode, OpError>
					where I: Iterator<Item = u8> {
						bytes.next()
							.map(|b| b.try_into()
								.map_err(|e| OpError::ParMode(Some(e), pos)))
							.unwrap_or(Ok(ParMode::Pos))
					}

					let par_modes = [
						par_mode(&mut bytes_rev, ArgPos::First)?,
						par_mode(&mut bytes_rev, ArgPos::Second)?
					];

					match b0 {
						b'1' => Ok(Op::Add(par_modes)),
						b'2' => Ok(Op::Mul(par_modes)),
						b'3' => match par_modes {
							[ParMode::Pos, ParMode::Pos] => Ok(Op::In),
							[ParMode::Imm, _] => Err(OpError::ParMode(None, ArgPos::First)),
							_ => Err(OpError::ParMode(None, ArgPos::Second)),
						}
						b'4' => match par_modes {
							[par_mode, ParMode::Pos] => Ok(Op::Out(par_mode)),
							_ => Err(OpError::ParMode(None, ArgPos::Second)),
						}
						b'5' => Ok(Op::JumpIf(true, par_modes)),
						b'6' => Ok(Op::JumpIf(false, par_modes)),
						b'7' => Ok(Op::Lt(par_modes)),
						b'8' => Ok(Op::Eq(par_modes)),
						_ => Err(OpError::Op(b0, b1)),
					}
				}
				(b0, b1) => Err(OpError::Op(b0, b1)),
			}
		}
	}

	impl<'a> Program<'a> for Vec<Int<'a>> {}

	pub(crate) fn from_str<'a>(s: &'a str) -> impl Program<'a> {
		use itertools::Itertools;
		s.lines()
			.enumerate()
			.flat_map(|(l, line)|
				if line.ends_with(',') { line.chars().dropping_back(1).as_str() }
				else { line }
					.split(',')
					.map(move |int| (l, int)))
			.scan(0, |c, (l, int)|
				Some((l, mem::replace(c, *c + int.len() + 1), int)))
			.map(|(_, c, str)| Int::Raw { _column: c + 1, str })
			.collect::<Vec<Int<'a>>>()
	}
}


#[cfg(test)]
mod tests {
	use super::*;

	pub(super) const INPUTS: [&str; 8] = [
		"1002,4,3,4,33",
		"3,9,8,9,10,9,4,9,99,-1,8",
		"3,9,7,9,10,9,4,9,99,-1,8",
		"3,3,1108,-1,8,3,4,3,99",
		"3,3,1107,-1,8,3,4,3,99",
		"3,12,6,12,15,1,13,14,13,4,13,99,-1,0,1,9",
		"3,3,1105,-1,9,1101,0,0,12,4,12,99,1",
		indoc::indoc! { "
			3,21,1008,21,8,20,1005,20,22,107,8,21,20,1006,20,31,
			1106,0,36,98,0,0,1002,21,125,20,4,20,1105,1,46,104,
			999,1105,1,46,1101,1000,1,20,4,20,1105,1,46,98,99
		" },
	];

	#[test]
	fn tests() {
		use itertools::Itertools as _;
		let mut tiny_program = parsing::from_str(INPUTS[0]);
		assert_eq!(tiny_program.execute(&mut std::iter::from_fn(|| panic!())).count(), 0);
		assert_eq!(tiny_program.as_mut().iter().map(|i| i.as_num().unwrap()).collect::<Vec<_>>(), [1002, 4, 3, 4, 99]);
		assert_eq!(part1(), 7566643);
		assert_eq!(parsing::from_str(INPUTS[1]).execute(std::iter::once(8)).exactly_one().ok(), Some(1));
		assert_eq!(parsing::from_str(INPUTS[1]).execute(std::iter::once(13)).exactly_one().ok(), Some(0));
		assert_eq!(parsing::from_str(INPUTS[2]).execute(std::iter::once(7)).exactly_one().ok(), Some(1));
		assert_eq!(parsing::from_str(INPUTS[2]).execute(std::iter::once(8)).exactly_one().ok(), Some(0));
		assert_eq!(parsing::from_str(INPUTS[3]).execute(std::iter::once(8)).exactly_one().ok(), Some(1));
		assert_eq!(parsing::from_str(INPUTS[3]).execute(std::iter::once(13)).exactly_one().ok(), Some(0));
		assert_eq!(parsing::from_str(INPUTS[4]).execute(std::iter::once(7)).exactly_one().ok(), Some(1));
		assert_eq!(parsing::from_str(INPUTS[4]).execute(std::iter::once(8)).exactly_one().ok(), Some(0));
		assert_eq!(parsing::from_str(INPUTS[5]).execute(std::iter::once(0)).exactly_one().ok(), Some(0));
		assert_eq!(parsing::from_str(INPUTS[5]).execute(std::iter::once(1337)).exactly_one().ok(), Some(1));
		assert_eq!(parsing::from_str(INPUTS[6]).execute(std::iter::once(0)).exactly_one().ok(), Some(0));
		assert_eq!(parsing::from_str(INPUTS[6]).execute(std::iter::once(1337)).exactly_one().ok(), Some(1));
		assert_eq!(parsing::from_str(INPUTS[7]).execute(std::iter::once(7)).exactly_one().ok(), Some(999));
		assert_eq!(parsing::from_str(INPUTS[7]).execute(std::iter::once(8)).exactly_one().ok(), Some(1000));
		assert_eq!(parsing::from_str(INPUTS[7]).execute(std::iter::once(13)).exactly_one().ok(), Some(1001));
		assert_eq!(part2(), 9265694);
	}
}
