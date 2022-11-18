// Copyright (c) 2022 Bastiaan Marinus van de Weerd

use std::collections::HashMap;
use crate::day05::{parsing::from_str as input_program_from_str, ProgramState, Program as _};


type PaintedWhite = HashMap<[isize; 2], bool>;

pub(crate) fn part1and2_impl(starting_white: bool) -> PaintedWhite {
	use std::iter::{from_fn, once};

	#[derive(Debug, Clone, Copy)]
	enum Dir { Up, Down, Left, Right }

	impl Dir {
		fn turn(&mut self, left: bool) {
			use Dir::*;
			match (&self, left) {
				(Up, true) | (Down, false) => *self = Left,
				(Down, true) | (Up, false) => *self = Right,
				(Left, true) | (Right, false) => *self = Down,
				(Right, true) | (Left, false) => *self = Up,
			}
		}

		fn r#move(&self, pos: &mut [isize; 2]) {
			use Dir::*;
			match &self {
				Up => pos[1] -= 1,
				Down => pos[1] += 1,
				Left => pos[0] -= 1,
				Right => pos[0] += 1,
			}
		}
	}

	let mut painted_white = HashMap::<[isize; 2], bool>::new();
	if starting_white { painted_white.insert([0, 0], true); }
	let mut robot_pos = [0isize, 0];
	let mut robot_dir = Dir::Up;

	let mut program = input_program_from_str::<i64>(include_str!("day11.txt"));
	let mut program_state = ProgramState::new(true);

	loop {
		let mut input = once(i64::from(*painted_white.get(&robot_pos).unwrap_or(&false)));
		let program = &mut program;
		let mut outputs = from_fn(||
			program.try_output(&mut program_state, &mut input)
				.map(|o| o.map(Ok))
				.unwrap_or_else(|e| Some(Err(e))))
			.take(2);
		
		let outputs = match (outputs.next(), outputs.next()) {
			(Some(Ok(o0)), Some(Ok(o1))) => [o0, o1],
			(Some(Err(e)), _) | (_, Some(Err(e))) => panic!("{}", e),
			(Some(_), None) => panic!("Unexpected end of output!"),
			(None, None) => break,
			(o0, o1) => panic!("o0: {o0:?}, o1: {o1:?}"),
		};

		fn valid_output(outputs: &[i64; 2], idx: usize, kind: &'static str) -> i64 {
			match outputs[idx] {
				o @ 0..=1 => o,
				e => panic!("Unexpected {kind} output {e}"),
			}
		}

		let paint_black = valid_output(&outputs, 0, "paint_color") == 0;
		let turn_left = valid_output(&outputs, 1, "turn direction") == 0;

		painted_white.insert(robot_pos, !paint_black);
		robot_dir.turn(turn_left);
		robot_dir.r#move(&mut robot_pos);
	}

	
	painted_white
}

pub(crate) fn part1() -> usize {
	part1and2_impl(false).len()
}

pub(crate) fn part2() -> String {
	use itertools::Itertools;

	let painted_white = part1and2_impl(true);

	let extents = [
		painted_white.keys().map(|&[x, _]| x).minmax().into_option().unwrap(),
		painted_white.keys().map(|&[_, y]| y).minmax().into_option().unwrap()
	];

	let mut buf = vec![];
	for y in extents[1].0..=extents[1].1 {
		for x in extents[0].0..=extents[0].1 {
			buf.push(match painted_white.get(&[x, y]) {
				None => b' ',
				Some(&false) => b'.',
				Some(&true) => b'#',
			});
		}
		if y < extents[1].1 { buf.push(b'\n'); }
	}
	// SAFETY: Only pushed ASCII characters.
	unsafe { String::from_utf8_unchecked(buf) }
}


#[test]
fn tests() {
	assert_eq!(part1(), 1785);
	assert_eq!(part2(), indoc::indoc!{ "
		.#..#...##..##..#......##.####.####.#..#.. 
		 #..#....#.#..#.#.......#....#.#....#..#...
		 ####....#.#..#.#.......#...#..###..####...
		.#..#....#.####.#.......#..#...#....#..#.. 
		.#..#.#..#.#..#.#....#..#.#....#....#..#.  
		 #..#..##..#..#.####..##..####.#....#..#.  
	" }.trim_end_matches('\n'));
}
