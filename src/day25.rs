// Copyright (c) 2022 Bastiaan Marinus van de Weerd

use crate::day05::{parsing::from_str as input_program_from_str, ProgramState, Program};


fn part1_impl<'a>(input_program: impl Program<'a, i64>, interactive: bool) -> String {
	use std::{
		collections::VecDeque,
		fmt::Write,
		io::{BufRead, stdin},
		iter::from_fn,
	};

	let mut program = input_program;
	let mut program_state = ProgramState::new(true);
	let mut l = 0;
	let mut output = String::new();

	let mut input = VecDeque::new();
	if !interactive {
		// Not much to compute here (other than writing an AI);
		// these commands move the droid throught the entire ship,
		// taking all items that don’t don’t cause the “game” to end
		// (or get stuck in an infinite loop).
		input.extend(indoc::indoc! { "
			west
			take mutex
			south
			south
			south
			take polygon
			north
			east
			take weather machine
			west
			north
			north
			east
			south
			take hologram
			west
			east
			north
			north
			north
			north
			take semiconductor
			west
			take monolith
			south
			north
			east
			east
			take prime number
			west
			south
			west
			north
			take jam
			west
			inv
		" }.bytes());
	}

	// This is the right combination that allows passage to Santa.
	// If set to 0, it will be found automatically below.
	let mut items_combination = 0b11100100;

	#[cfg(LOGGING)]
	fn print_input_commands(input: impl Iterator<Item = u8>, l: usize) -> impl Iterator<Item = i64> {
		input
			.scan(String::new(), move |acc, b| {
				if b == b'\n' {
					println!("{} {acc}", ">".repeat(l.to_string().len() + 1));
					acc.clear()
				} else {
					acc.push(if b.is_ascii() { b as char } else { '\u{FFFD}' })
				}
				Some(b)
			})
			.map(|b| b as i64)
	}
	#[cfg(not(LOGGING))]
	fn print_input_commands(input: impl Iterator<Item = u8>, _: usize) -> impl Iterator<Item = i64> {
		input.map(|b| b as i64)
	}

	while !program.is_halted(&program_state) {
		match program.try_output(&mut program_state,
			print_input_commands(from_fn(|| input.pop_front()), l)) {
			Ok(None) => (),
			Ok(Some(num)) => match u8::try_from(num) {
				Ok(b'\n') => {
					l += 1;
					#[cfg(LOGGING)]
					println!("{l}: {output}");
					if output.starts_with("\"Oh, hello!") {
						return output.chars()
							.filter(|c| c.is_ascii() && c.is_numeric())
							.collect();
					}
					output.clear();
				}
				Ok(b) if b.is_ascii() => {
					output.write_char(b as char).unwrap();
				},
				res => panic!("Invalid output ({res:?}); prev. output:\n{output}")
			}
			_ if program.needs_input(&program_state) => {
				let commands = if !interactive && items_combination < u8::MAX {
					// TODO(bm-w): Check inventory & items in the room
					const ITEMS: [&str; 8] = [
						"mutex",
						"hologram",
						"polygon",
						"jam",
						"semiconductor",
						"prime number",
						"monolith",
						"weather machine"
					];

					let mut dropped_items = Vec::new();
					for (i, item) in ITEMS.into_iter().enumerate() {
						if items_combination & (1 << i) != 0 {
							dropped_items.push(item);
						}
					}

					let mut commands = String::new();
					for &item in &dropped_items {
						commands.push_str("drop ");
						commands.push_str(item);
						commands.push('\n');
					}
					commands.push_str("north\n");
					items_combination += 1;
					if items_combination < u8::MAX {
						for &item in &dropped_items {
							commands.push_str("take ");
							commands.push_str(item);
							commands.push('\n');
						}
					}

					commands
				} else if interactive { match stdin().lock().lines().next() {
					Some(Ok(mut command)) if command.is_ascii() => {
						command.push('\n');
						command
					}
					Some(Ok(invalid)) => panic!("Invalid non-ASCII command: {invalid:?}"),
					Some(err) => { _ = err.unwrap(); unreachable!() },
					none => { _ = none.unwrap(); unreachable!() },
				} } else {
					panic!("Could not find the right combination of items!")
				};

				input.extend(commands.bytes())
			}
			err => { println!("Output:\n{output}"); _ = err.unwrap() }
		}
	}

	panic!("Game over!")
}

pub(crate) fn part1() -> String {
	let program = input_program_from_str::<i64>(include_str!("day25.txt"));
	part1_impl(program, std::env::var("INTERACTIVE").is_ok())
}


pub(crate) fn part2() -> &'static str {
	"Merry Christmas!"
}


#[test]
fn tests() {
	assert_eq!(part1(), "35717128");
}
