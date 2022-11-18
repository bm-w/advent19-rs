// Copyright (c) 2022 Bastiaan Marinus van de Weerd


enum Opcode { Add, Mul, Halt, }
enum Int { Op(Opcode), Num(u64) }

impl Int {
	fn num(&self) -> u64 {
		match self {
			Int::Op(Opcode::Add) => 1,
			Int::Op(Opcode::Mul) => 2,
			Int::Op(Opcode::Halt) => 99,
			&Int::Num(num) => num,
		}
	}

	fn pos(&self) -> usize {
		self.num() as usize
	}
}

trait Program: AsMut<[Int]> {
	fn run(&mut self) {
		let memory = self.as_mut();
		let mut offset = 0;
		loop {
			if offset >= memory.len() { panic!("TODO") }
			let int = &memory[offset];
			if matches!(int, &Int::Op(Opcode::Halt)) { break }

			if offset + 3 >= memory.len() { panic!("TODO") }
			let arg_poss = (memory[offset + 1].pos(), memory[offset + 2].pos());
			let out_pos = memory[offset + 3].pos();

			if arg_poss.0.max(arg_poss.1).max(out_pos) >= memory.len() { panic!("TODO") }
			let args = (memory[arg_poss.0].num(), memory[arg_poss.1].num());

			memory[out_pos] = match int {
				Int::Op(Opcode::Add) => args.0 + args.1,
				Int::Op(Opcode::Mul) => args.0 * args.1,
				_ => panic!(),
			}.into();

			offset += 4;
		}
	}
}

impl Program for Vec<Int> {}


fn input_program_from_str(s: &str) -> impl Program {
	parsing::try_from_str(s).unwrap()
}

fn input_program() -> impl Program {
	input_program_from_str(include_str!("day02.txt"))
}


#[cfg(test)]
fn part1_state(mut input_program: impl Program) -> Vec<u64> {
	input_program.run();
	input_program.as_mut().iter().map(|int| int.num()).collect()
}

fn part1and2_impl(input1: u64, input2: u64) -> u64 {
	let mut input_program = input_program();
	input_program.as_mut()[1] = Int::Num(input1);
	input_program.as_mut()[2] = Int::Num(input2);
	input_program.run();
	input_program.as_mut()[0].num()
}


pub(crate) fn part1() -> u64 {
	part1and2_impl(12, 2)
}


pub(crate) fn part2() -> u64 {
	itertools::iproduct!(0..=99, 0..=99)
		.find_map(|(verb, noun)| {
			let output = part1and2_impl(verb, noun);
			(output == 19690720).then_some(verb * 100 + noun)
		})
		.unwrap()
}


mod parsing {
	use super::{Opcode, Int, Program};
	use std::{mem, num::ParseIntError, str::FromStr};

	impl From<u64> for Int {
		fn from(int: u64) -> Self {
			match int {
				1 => Int::Op(Opcode::Add),
				2 => Int::Op(Opcode::Mul),
				99 => Int::Op(Opcode::Halt),
				num => Int::Num(num)
			}
		}
	}

	#[allow(dead_code)]
	#[derive(Debug)]
	pub(super) struct ProgramError { column: usize, source: ParseIntError }

	pub(super) fn try_from_str(s: &str) -> Result<impl Program, ProgramError> {
		let vec = s.lines()
			.next().into_iter().flat_map(|l| l.split(','))
			.scan(0, |c, int| {
				let c = mem::replace(c, *c + int.len() + 1);
				Some((c, int))
			})
			.map(|(c, int)| int.parse()
				.map_err(|e| ProgramError { column: c + 1, source: e })
				.map(|int: u64| int.into()))
			.collect::<Result<Vec<Int>, _>>()?;
		if vec.is_empty() { return Err(ProgramError { column: 1, source: u64::from_str("").unwrap_err() }) }
		Ok(vec)
	}
}


#[test]
fn tests() {
	assert_eq!(part1_state(input_program_from_str("1,0,0,0,99")), [2, 0, 0, 0, 99]);
	assert_eq!(part1_state(input_program_from_str("2,3,0,3,99")), [2, 3, 0, 6, 99]);
	assert_eq!(part1_state(input_program_from_str("2,4,4,5,99,0")), [2, 4, 4, 5, 99, 9801]);
	assert_eq!(part1_state(input_program_from_str("1,1,1,4,99,5,6,0,99")), [30, 1, 1, 4, 2, 5, 6, 0, 99]);
	assert_eq!(part1(), 3716250);
	assert_eq!(part2(), 6472);
}
