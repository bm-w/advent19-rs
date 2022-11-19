// Copyright (c) 2022 Bastiaan Marinus van de Weerd


const W: usize = 5;

#[derive(Clone)]
enum Grid {
	Plain { bugs: [bool; 25] },
	Recursive { bugs: std::collections::VecDeque<[bool; 25]>, center: usize, }
}

#[derive(Clone, Copy)]
struct RecursiveGridPos {
	level: isize,
	pos: usize,
}

impl Grid {

	fn adjacent_positions(from: usize) -> [Option<usize>; 4] {
		let t = if from >= W { Some(from - W) } else { None };
		let l = if from % W > 0 { Some(from - 1) } else { None };
		let r = if from % W < W - 1 { Some(from + 1) } else { None };
		let b = if from < W * W - W { Some(from + W) } else { None };
		[t, l, r, b]
	}

	fn recursive_adjacent_positions(from: usize, level: isize) -> impl Iterator<Item = RecursiveGridPos> {
		assert_ne!(from, 12);
		assert_eq!(W, 5);

		let mut adj_poss = Self::adjacent_positions(from);

		macro_rules! let_outer { ( $name:ident, $adj_pos:literal, $outer_pos: literal ) => {
			let $name = adj_poss[$adj_pos].is_none()
				.then_some(RecursiveGridPos { level: level - 1, pos: $outer_pos })
				.into_iter();
		}}
		let_outer!(ot, 0, 7);
		let_outer!(ol, 1, 11);
		let_outer!(or, 2, 13);
		let_outer!(ob, 3, 17);

		macro_rules! let_inner {
			( $name:ident, $adj_pos:literal, [ $( $inner_poss: literal ),+ ] ) => {
				let $name = if adj_poss[$adj_pos] == Some(12) {
					adj_poss[$adj_pos] = None;
					const POSS: [usize; 5] = [$( $inner_poss ),+];
					Some(std::array::from_fn::<_, 5, _>(|i| RecursiveGridPos {
						level: level + 1, pos: POSS[i] }))
				} else {
					None
				}.into_iter().flatten();
			}
		}
		let_inner!(it, 0, [20, 21, 22, 23, 24]);
		let_inner!(il, 1, [4, 9, 14, 19, 24]);
		let_inner!(ir, 2, [0, 5, 10, 15, 20]);
		let_inner!(ib, 3, [0, 1, 2, 3, 4]);

		macro_rules! let_chain {
			( $name:ident, $adj_pos:literal, $outer_name:ident, $inner_name:ident ) => {
				let $name = adj_poss[$adj_pos].map(|pos| RecursiveGridPos { level, pos })
					.into_iter().chain($outer_name).chain($inner_name);
			}
		}
		let_chain!(t, 0, ot, it);
		let_chain!(l, 1, ol, il);
		let_chain!(r, 2, or, ir);
		let_chain!(b, 3, ob, ib);

		t.chain(l).chain(r).chain(b)
	}

	fn bugs(&self, level: isize) -> Option<&[bool; 25]> {
		match self {
			Grid::Plain { bugs } => Some(bugs),
			Grid::Recursive { bugs, center } => {
				if !(0..bugs.len() as isize).contains(&(*center as isize + level)) { None }
				else { Some(&bugs[(*center as isize + level).unsigned_abs()]) }
			}
		}
	}

	fn bugs_mut(&mut self, level: isize) -> Option<&mut [bool; 25]> {
		match self {
			Grid::Plain { bugs } => Some(bugs),
			Grid::Recursive { bugs, center } => {
				if !(0..bugs.len() as isize).contains(&(*center as isize + level)) { None }
				else { Some(&mut bugs[(*center as isize + level).unsigned_abs()]) }
			}
		}
	}

	fn levels(&self) -> std::ops::RangeInclusive<isize> {
		match self {
			Grid::Recursive { bugs, center } => {
				let c = *center as isize;
				-c..=bugs.len() as isize - c - 1
			}
			_ => 0..=0
		}
	}

	fn make_recursive(&mut self) -> std::ops::RangeInclusive<isize> {
		match *self {
			Grid::Plain { bugs } => {
				*self = Grid::Recursive {
					bugs: std::collections::VecDeque::from_iter([bugs]),
					center: 0,
				};
				0..=0
			}
			_ => self.levels(),
		}
	}

	fn tick(&mut self, recursive: bool) {
		let levels = if recursive {
			let range = self.make_recursive();
			range.start() - 1..=range.end() + 1
		} else {
			0..=0
		};

		let clone = self.clone();
		let mut new = [false; W * W];

		for level in levels {
			let next = self.bugs_mut(level).unwrap_or(&mut new);

			for (pos, bugs) in next.iter_mut().enumerate() {
				let adj_count = if recursive {
					if pos == 12 { continue }
					Self::recursive_adjacent_positions(pos, level)
						.filter(|rp|
							clone.bugs(rp.level).map(|b| b[rp.pos])
								.unwrap_or(false))
						.count()
				} else {
					Self::adjacent_positions(pos).into_iter()
						.filter(|p| p.and_then(|p|
							clone.bugs(0).map(|b| b[p]))
								.unwrap_or(false))
						.count()
				};

				match (bugs, adj_count) {
					(bugs @ false, 1 | 2) => *bugs = true,
					(true, 1) => (),
					(bugs @ true, _) => *bugs = false,
					_ => (),
				}
			}

			if self.bugs(level).is_none() && new.iter().any(|&i| i) {
				let Grid::Recursive { bugs, center } = self else { unreachable!() };
				if level < 0 {
					bugs.push_front(new);
					*center += 1;
				} else {
					bugs.push_back(new);
				}
			}
		}
	}

	fn biodiversity(&self, level: isize) -> u64 {
		let mut result = 0;
		for (i, &bugs) in self.bugs(level).into_iter().flatten().enumerate() {
			if bugs { result += 1 << i }
		}
		result
	}

	fn count_bugs(&self) -> usize {
		fn count_level_bugs(bugs: &[bool; W * W]) -> usize {
			bugs.iter().filter(|b| **b).count()
		}
		match self {
			Grid::Plain { bugs } => count_level_bugs(bugs),
			Grid::Recursive { bugs, .. } => bugs.iter().map(count_level_bugs).sum(),
		}
	}
}


fn input_grid_from_str(s: &str) -> Grid {
	s.parse().unwrap()
}

fn input_grid() -> Grid {
	input_grid_from_str(include_str!("day24.txt"))
}


fn part1_impl(mut input_grid: Grid) -> u64 {
	let mut seen = std::collections::HashSet::new();
	loop {
		let biodiversity = input_grid.biodiversity(0);
		if !seen.insert(biodiversity) { return biodiversity }
		input_grid.tick(false);
	}
}

pub(crate) fn part1() -> u64 {
	part1_impl(input_grid())
}


fn part2_impl<const N: usize>(mut input_grid: Grid) -> usize {
	for _ in 0..N { input_grid.tick(true); }
	input_grid.count_bugs()
}

pub(crate) fn part2() -> usize {
	part2_impl::<200>(input_grid())
}


mod parsing {
	use std::str::FromStr;
	use super::{W, Grid};

	#[allow(dead_code)]
	#[derive(Debug)]
	pub(super) enum GridError {
		Len { line: usize, len: usize },
		Invalid { line: usize, column: usize, found: u8 },
	}

	impl FromStr for Grid {
		type Err = GridError;
		fn from_str(s: &str) -> Result<Self, Self::Err> {

			let mut bugs = [false; W * W];

			macro_rules! len_err { ( $l:expr, $len:expr ) => {
				GridError::Len { line: $l + 1, len: $len }
			} }
			macro_rules! ret_len_err { ( $l:expr, $len:expr ) => {
				return Err(len_err!($l, $len))
			} }

			let mut bugs_mut = bugs.iter_mut();

			for (l, line) in s.lines().enumerate() {
				for (c, b) in line.bytes().enumerate() {
					if c == W { ret_len_err!(l, W + 1) }
					*bugs_mut.next()
							.ok_or_else(|| len_err!(l, c + 1))? = match b {
						b'.' => false,
						b'#' => true,
						found => return Err(GridError::Invalid {
							line: l + 1, column: c + 1, found })
					};
				}

				match bugs_mut.len() % W { 0 => (), len => ret_len_err!(l, W - len) }
			}

			match bugs_mut.len() { 0 => (), len => ret_len_err!(W - len / W, 0) }

			Ok(Grid::Plain { bugs })
		}
	}
}

#[cfg(LOGGING)]
impl std::fmt::Display for Grid {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		use std::fmt::Write;

		let levels = self.levels();
		let recursive = levels.start() < levels.end();

		let mut first = true;
		for level in levels {
			if !first { f.write_str("\n\n")? }

			if recursive { writeln!(f, "Depth {level}:")?; }

			let bugs = self.bugs(level).unwrap();
			for y in 0..W {
				for x in 0..W {
					f.write_char(
						if recursive && y == 2 && x == 2 { '?' }
						else if bugs[W * y + x] { '#' }
						else { '.' })?;
				}
				if y < W - 1 { f.write_char('\n')?; }
			}

			first = false;
		}
		Ok(())
	}
}


#[test]
fn tests() {
	const INPUT: &str = indoc::indoc! { "
		....#
		#..#.
		#..##
		..#..
		#....
	" };
	assert_eq!(part1_impl(input_grid_from_str(INPUT)), 2129920);
	assert_eq!(part1(), 30442557);
	assert_eq!(part2_impl::<10>(input_grid_from_str(INPUT)), 99);
	assert_eq!(part2(), 1987);

	#[cfg(LOGGING)]
	for i in 0..25 {
		use itertools::Itertools;
		if i == 12 { continue }
		println!("{i}: {}", Grid::recursive_adjacent_positions(i, 0)
			.map(|RecursiveGridPos { level, pos }| format!("{}{pos}", match level {
				0 => "".to_owned(),
				1.. => format!("+{level}."),
				_ => format!("{level}."),
			}))
			.join(", "));
	}
}
