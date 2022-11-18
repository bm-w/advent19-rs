// Copyright (c) 2022 Bastiaan Marinus van de Weerd

//! NOTE: The “Intcode computer” of this module is also used in `day07`,
//! `day09`, `day11`, `day13`, `day15`, `day17`, `day19`, `day21`, and
//! `day23`; for that reason:
//! - various items are `pub(crate)`;
//! - various items implement `Clone`;
//! - `Program` was refactored into to expose the `safe_output` method;
//! - relative (`Rel`) parameter mode;
//! - extended memory beyond the base program;
//! - generic `Num` support.

use std::fmt::Debug;


#[derive(Clone, Copy)]
#[cfg_attr(test, derive(Debug))]
pub(crate) enum ParMode { Pos, Imm, Rel }

#[derive(Debug, Clone, Copy)]
pub(crate) enum ArgPos { First, Second, Third }

impl<T> std::ops::Index<ArgPos> for [T] {
	type Output = T;
	fn index(&self, index: ArgPos) -> &Self::Output {
		match index {
			ArgPos::First => &self[0],
			ArgPos::Second => &self[1],
			ArgPos::Third => &self[2],
		}
	}
}

type IsRelParMode = bool;

#[derive(Clone, Copy)]
#[cfg_attr(test, derive(Debug))]
pub(crate) enum Op {
	Add([ParMode; 2], IsRelParMode),
	Mul([ParMode; 2], IsRelParMode),
	In(IsRelParMode),
	Out(ParMode),
	JumpIf(bool, [ParMode; 2]),
	Lt([ParMode; 2], IsRelParMode),
	Eq([ParMode; 2], IsRelParMode),
	RelAdj(ParMode),
	Halt,
}


#[derive(Clone)]
#[cfg_attr(test, derive(Debug))]
pub(crate) enum Int<'a,  Num = i64> {
	Op(Op),
	Num(Num),
	Raw { str: &'a str, _column: usize }
}

const PAR_MODE_COEFFS: [u16; 3] = [100, 1000, 10000];

impl ParMode {
	fn num(&self) -> u16 {
		use ParMode::*;
		match self { Pos => 0, Imm => 1, Rel => 2 }
	}

	fn arg0_num(par_mode: &Self) -> u16 {
		PAR_MODE_COEFFS[ArgPos::First] * par_mode.num()
	}

	fn args_num(par_modes: &[Self; 2]) -> u16 {
		Self::arg0_num(&par_modes[ArgPos::First])
			+ PAR_MODE_COEFFS[ArgPos::Second] * par_modes[ArgPos::Second].num()
	}

	fn is_rel_par_mode_num(is_rel_par_mode: &bool, arg_pos: ArgPos) -> u16 {
		if *is_rel_par_mode { PAR_MODE_COEFFS[arg_pos] * 2 } else { 0 }
	}
}

impl From<&Op> for u16 {
	fn from(op: &Op) -> Self {
		match op {
			Op::Add(par_modes, is_rel_par_mode) => 1
				+ ParMode::args_num(par_modes)
				+ ParMode::is_rel_par_mode_num(is_rel_par_mode, ArgPos::Third),
			Op::Mul(par_modes, is_rel_par_mode) => 2
				+ ParMode::args_num(par_modes)
				+ ParMode::is_rel_par_mode_num(is_rel_par_mode, ArgPos::Third),
			Op::In(is_rel_par_mode) => 3
				+ ParMode::is_rel_par_mode_num(is_rel_par_mode, ArgPos::Second),
			Op::Out(par_mode) => 4 + ParMode::arg0_num(par_mode),
			Op::JumpIf(true, par_modes) => 5 + ParMode::args_num(par_modes),
			Op::JumpIf(false, par_modes) => 6 + ParMode::args_num(par_modes),
			Op::Lt(par_modes, is_rel_par_mode) => 7
				+ ParMode::args_num(par_modes)
				+ ParMode::is_rel_par_mode_num(is_rel_par_mode, ArgPos::Third),
			Op::Eq(par_modes, is_rel_par_mode) => 8
				+ ParMode::args_num(par_modes)
				+ ParMode::is_rel_par_mode_num(is_rel_par_mode, ArgPos::Third),
			Op::RelAdj(par_mode) => 9 + ParMode::arg0_num(par_mode),
			Op::Halt => 99,
		}
	}
}

use std::{ops::{Add, Mul}, str::FromStr};

pub(crate) trait IntNum: Clone + Default + FromStr + From<bool>
	+ PartialEq<Self> + PartialOrd<Self>
	+ Add<Self, Output = Self> + Mul<Self, Output = Self> {
	type TryAsIsizeError;
	fn from_op(_: Op) -> Self;
	fn from_isize(_: isize) -> Self;
	fn try_as_op(&self) -> Result<Op, parsing::OpError>;
	fn try_as_isize(&self) -> Result<isize, Self::TryAsIsizeError>;
}

#[derive(Debug)]
enum TryIntIntoIsizeError<FromNum> {
	FromNum(FromNum),
	FromRaw(<isize as FromStr>::Err),
}

impl<'n, Num> Int<'_, Num> where Num: IntNum + 'n {
	fn try_into_op(&mut self) -> Result<Op, parsing::OpError> {
		macro_rules! try_into_self { ( $res:expr ) => { {
			let num = $res;
			if let Ok(op) = num { *self = Int::Op(op); }
			num
		} } }
		match self {
			Int::Op(op) => Ok(*op),
			Int::Num(num) => try_into_self!(num.try_as_op()),
			Int::Raw { str, .. } => try_into_self!(Op::from_str(str)),
		}
	}

	fn try_into_num(&mut self) -> Result<Num, <Num as FromStr>::Err> {
		match &self {
			Int::Op(op) => Ok(Num::from_op(*op)),
			Int::Num(num) => Ok(num.clone()),
			Int::Raw { str, .. } => {
				let num = Num::from_str(str)?;
				*self = Int::Num(num.clone());
				Ok(num)
			}
		}
	}

	fn try_into_isize(&mut self) -> Result<isize, TryIntIntoIsizeError<Num::TryAsIsizeError>> {
		match &self {
			Int::Op(op) => Ok(u16::from(op) as isize),
			Int::Num(num) => num.try_as_isize().map_err(TryIntIntoIsizeError::FromNum),
			Int::Raw { str, .. } => {
				let isize_ = isize::from_str(str).map_err(TryIntIntoIsizeError::FromRaw)?;
				*self = Int::Num(Num::from_isize(isize_));
				Ok(isize_)
			},
		}
	}
}

impl<Num> Default for Int<'_, Num> where Num: Default {
	fn default() -> Self {
		Int::Num(Num::default())
	}
}

impl IntNum for i64 {
	type TryAsIsizeError = <isize as TryFrom<Self>>::Error;

	fn from_op(op: Op) -> Self {
		u16::from(&op) as Self
	}

	fn from_isize(isize_: isize) -> Self {
		isize_ as Self
	}

	fn try_as_op(&self) -> Result<Op, parsing::OpError> {
		Op::try_from(u16::try_from(*self).map_err(|_| parsing::OpError::Format)?)
	}

	fn try_as_isize(&self) -> Result<isize, Self::TryAsIsizeError> {
		isize::try_from(*self)
	}
}

use std::collections::HashMap;

pub(crate) struct ProgramState<'a, Num> {
	pub(crate) offset: usize,
	pub(crate) rel_base: usize,
	pub(crate) ext_memory: Option<HashMap<usize, Int<'a, Num>>>,
}

impl<'a, Num> ProgramState<'a, Num> {
	pub(crate) fn new(ext_memory: bool) -> Self {
		Self { offset: 0, rel_base: 0, ext_memory: ext_memory.then(HashMap::new) }
	}
}

pub(crate) trait Program<'a, Num = i64>: AsRef<[Int<'a, Num>]> + AsMut<[Int<'a, Num>]> + Clone
where Num: Debug + IntNum + 'a, <Num as FromStr>::Err: Debug, Num::TryAsIsizeError: Debug {

	fn try_step<'b, FIn>(
		&'b mut self,
		ProgramState { offset, rel_base, ext_memory }: &mut ProgramState<'a, Num>,
		input: FIn
	) -> Result<Option<Num>, String>
	where 'a: 'b, FIn: FnOnce() -> Option<Num> {
		use {ArgPos::*, Op::*};

		let memory = self.as_mut();
		let mut ext_memory = ext_memory.as_mut();

		macro_rules! check_offset {
			( + $delta:literal ) => {
				if *offset + $delta >= memory.len() { return Err("Unexpected end of program".to_string()) }
			}
		}
		check_offset!(+0);

		macro_rules! parse_int {
			( $int:expr, $try_into:ident, $err_pos:expr ) => {
				$int.$try_into().map_err(|e|
					format!("Invalid int at position {}; source: {e:?}", $err_pos))
			}
		}
		macro_rules! parse_memory {
			( $pos:expr, $try_into:ident ) => {
				if $pos < memory.len() {
					parse_int!(&mut memory[$pos], $try_into, $pos)?
				} else if let Some(ext_memory) = ext_memory.as_mut() {
					ext_memory.get_mut(&$pos)
						.map(|i| parse_int!(i, $try_into, $pos))
						.unwrap_or(Ok(Default::default()))?
				} else {
					return Err(format!("Reading outside unextended memory at position {}", $pos));
				}
			}
		}
		macro_rules! non_neg_pos { ( $pos:expr ) => { {
			let pos = $pos;
			usize::try_from(pos).map_err(|e| format!("Using invalid position {pos} as memory addres; source: {e:?}"))?
		} } }
		macro_rules! parse_memory_pos {
			( $pos:expr ) => { {
				let pos = non_neg_pos!($pos);
				let mem_pos = parse_memory!(pos, try_into_isize);
				non_neg_pos!(mem_pos)
			} }
		}
		macro_rules! parse_rel_memory_pos {
			( $delta_pos:expr ) => { {
				let pos = *rel_base as isize + parse_memory!($delta_pos, try_into_isize);
				non_neg_pos!(pos)
			} }
		}
		macro_rules! parse_memory_with_mode {
			( $pos:expr, $par_mode:expr, $try_into:ident) => { {
				use ParMode::*;
				let pos = match $par_mode {
					Pos => parse_memory_pos!($pos),
					Imm => $pos,
					Rel => parse_rel_memory_pos!($pos),
				};
				parse_memory!(pos, $try_into)
			} }
		}
		macro_rules! parse_memory_num_with_mode { ( $pos:expr, $par_mode:expr) =>
			{ parse_memory_with_mode!($pos, $par_mode, try_into_num) } }
		macro_rules! write_memory { ( $pos:expr, $val:expr ) => {
			*if $pos < memory.len() {
				&mut memory[$pos]
			} else if let Some(ext_memory) = ext_memory.as_mut() {
				ext_memory.entry($pos).or_default()
			} else {
				return Err(format!("Writing outside unextended memory at position {}", $pos));
			} = Int::Num($val)
		} }

		match memory[*offset].try_into_op()
				.map_err(|e|
					format!("Unexpected non-op instruction at position {offset}: {e:?}"))? {
			op @ (Add(par_modes, is_rel_par_mode)
					| Mul(par_modes, is_rel_par_mode)
					| Lt(par_modes, is_rel_par_mode)
					| Eq(par_modes, is_rel_par_mode)) => {
				check_offset!(+3);
				let arg0 = parse_memory_num_with_mode!(*offset + 1, par_modes[First]);
				let arg1 = parse_memory_num_with_mode!(*offset + 2, par_modes[Second]);
				let dest = if is_rel_par_mode { parse_rel_memory_pos!(*offset + 3) }
					else { parse_memory_pos!(*offset + 3) };
				let num = match op {
					Add(_, _) => arg0 + arg1,
					Mul(_, _) => arg0 * arg1,
					Lt(_, _) => Num::from(arg0 < arg1),
					Eq(_, _) => Num::from(arg0 == arg1),
					_ => unreachable!(),
				};
				write_memory!(dest, num);
				*offset += 4;
			}
			In(is_rel_par_mode) => {
				check_offset!(+1);
				let dest = if is_rel_par_mode { parse_rel_memory_pos!(*offset + 1) }
					else { parse_memory_pos!(*offset + 1) };
				write_memory!(dest, input().ok_or_else(|| "Unexpected end of input".to_string())?);
				*offset += 2;
			}
			Out(par_mode) => {
				check_offset!(+1);
				let output = parse_memory_num_with_mode!(*offset + 1, par_mode);
				*offset += 2;
				return Ok(Some(output))
			}
			JumpIf(flag, par_mode) => {
				check_offset!(+2);
				if (parse_memory_num_with_mode!(*offset + 1, par_mode[First]) != Num::default()) == flag {
					let dest = parse_memory_with_mode!(*offset + 2, par_mode[Second], try_into_isize);
					*offset = non_neg_pos!(dest);
				} else {
					*offset += 3;
				}
			}
			RelAdj(par_mode) => {
				check_offset!(+1);
				let delta = parse_memory_with_mode!(*offset + 1, par_mode, try_into_isize);
				*rel_base = non_neg_pos!(*rel_base as isize + delta);
				*offset += 2;
			}
			Halt => (),
		}

		Ok(None)
	}

	fn is_halted(&self, state: &ProgramState<'a, Num>) -> bool {
		matches!(self.as_ref()[state.offset], Int::Op(Op::Halt))
	}

	fn try_output<'b, In>(
		&'b mut self,
		state: &mut ProgramState<'a, Num>,
		mut input: In
	) -> Result<Option<Num>, String>
	where 'a: 'b, In: Iterator<Item = Num> + 'b {
		loop {
			if let Some(output) = self.try_step(state, || input.next())? {
				return Ok(Some(output))
			} else if self.is_halted(state) {
				return Ok(None)
			}
		}
	}

	// TODO(bm-w): Return `impl Iterator<…>` once Rust allows it from trait methods
	fn execute_ext<'b, In>(&'b mut self, ext_memory: bool, mut input: In) -> Box<dyn Iterator<Item = Num> + 'b>
	where 'a: 'b, In: Iterator<Item = Num> + 'b {
		let mut state = ProgramState::new(ext_memory);
		Box::new(std::iter::from_fn(move || {
			self.try_output(&mut state, &mut input).unwrap()
		}))
	}

	// TODO(bm-w): Return `impl Iterator<…>` once Rust allows it from trait methods
	fn execute<'b, In>(&'b mut self, input: In) -> Box<dyn Iterator<Item = Num> + 'b>
	where 'a: 'b, In: Iterator<Item = Num> + 'b {
		self.execute_ext(false, input)
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
	use super::{ParMode, ArgPos, PAR_MODE_COEFFS, Op, Int, IntNum, Program};
	use std::{mem, fmt::Debug, str::FromStr};

	#[derive(Debug)]
	pub(crate) struct ParModeError(u8);

	impl TryFrom<u8> for ParMode {
		type Error = ParModeError;
		fn try_from(value: u8) -> Result<Self, Self::Error> {
			use ParMode::*;
			match value {
				0 => Ok(Pos),
				1 => Ok(Imm),
				2 => Ok(Rel),
				b => Err(ParModeError(b))
			}
		}
	}

	#[derive(Debug)]
	pub(crate) enum OpError {
		Format,
		Op(u8),
		ParMode(Option<ParModeError>, ArgPos),
	}

	impl TryFrom<u16> for Op {
		type Error = OpError;
		fn try_from(value: u16) -> Result<Self, Self::Error> {
			if value == 99 { return Ok(Op::Halt) }

			fn par_mode(mut value: u16, pos: ArgPos) -> Result<ParMode, OpError> {
				let coeff = PAR_MODE_COEFFS[pos];
				if coeff < u16::MAX / 10 { value %= coeff * 10; }
				value /= coeff;
				ParMode::try_from(value as u8)
					.map_err(|e| OpError::ParMode(Some(e), pos))
			}

			let par_modes = [
				par_mode(value, ArgPos::First)?,
				par_mode(value, ArgPos::Second)?,
			];
			let third_par_mode = par_mode(value, ArgPos::Third)?;

			fn one_par_mode(par_modes: [ParMode; 2]) -> Result<ParMode, OpError> {
				match par_modes {
					[par_mode, ParMode::Pos] => Ok(par_mode),
					_ => Err(OpError::ParMode(None, ArgPos::Second)),
				}
			}

			macro_rules! is_rel_par_mode { ( $pm:expr ) => { matches!($pm, ParMode::Rel) } }

			match value % 100 {
				1 => Ok(Op::Add(par_modes, is_rel_par_mode!(third_par_mode))),
				2 => Ok(Op::Mul(par_modes, is_rel_par_mode!(third_par_mode))),
				3 => match one_par_mode(par_modes)? {
					ParMode::Imm => Err(OpError::ParMode(None, ArgPos::First)),
					par_mode => Ok(Op::In(is_rel_par_mode!(par_mode))),
				}
				4 => Ok(Op::Out(one_par_mode(par_modes)?)),
				5 => Ok(Op::JumpIf(true, par_modes)),
				6 => Ok(Op::JumpIf(false, par_modes)),
				7 => Ok(Op::Lt(par_modes, is_rel_par_mode!(third_par_mode))),
				8 => Ok(Op::Eq(par_modes, is_rel_par_mode!(third_par_mode))),
				9 => Ok(Op::RelAdj(one_par_mode(par_modes)?)),
				err => Err(OpError::Op(err as u8)),
			}
		}
	}

	impl FromStr for Op {
		type Err = OpError;
		fn from_str(s: &str) -> Result<Self, Self::Err> {
			if s.is_empty() || s.len() > 5 { return Err(OpError::Format) }
			s.parse::<u16>().map_err(|_| OpError::Format).and_then(Op::try_from)
		}
	}

	impl<'a, Num> Program<'a, Num> for Vec<Int<'a, Num>>
	where Num: Debug + IntNum + 'a, <Num as FromStr>::Err: Debug, Num::TryAsIsizeError: Debug {}

	pub(crate) fn from_str<'a, Num>(s: &'a str) -> impl Program<'a, Num>
	where Num: Debug + IntNum + 'a, <Num as FromStr>::Err: Debug, Num::TryAsIsizeError: Debug {
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
			.map(|(_, c, str)| Int::Raw { str, _column: c + 1 })
			.collect::<Vec<Int<'a, Num>>>()
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
		let mut tiny_program = parsing::from_str::<i64>(INPUTS[0]);
		assert_eq!(tiny_program.execute(&mut std::iter::empty()).count(), 0);
		assert_eq!(tiny_program.as_mut().iter_mut().map(|i| i.try_into_num().unwrap()).collect::<Vec<_>>(), [1002, 4, 3, 4, 99]);
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
