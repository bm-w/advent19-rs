// Copyright (c) 2022 Bastiaan Marinus van de Weerd


#[derive(Clone, Copy)]
#[cfg_attr(test, derive(Debug, PartialEq, Eq))]
enum Dir { Up, Down, Left, Right }

impl std::ops::AddAssign<Dir> for (i32, i32) {
	fn add_assign(&mut self, rhs: Dir) {
		use Dir::*;
		match rhs {
			Up => self.1 += 1,
			Down => self.1 -= 1 ,
			Left => self.0 -= 1,
			Right => self.0 += 1,
		}
	}
}

#[cfg_attr(test, derive(Debug, PartialEq, Eq))]
struct WirePathSeg(Dir, usize);

trait Wire: AsRef<[WirePathSeg]> {
	/// **Note**: Implicitly walks from the origin `(0, 0)`, but
	/// does not contain the origin in its first position.
	// TODO(bm-w): Return `impl Iterator<…>` once Rust allows it from trait methods
	fn path_positions<'a>(&'a self) -> Box<dyn Iterator<Item = (i32, i32)> + 'a> {
		use std::iter;
		Box::new(self.as_ref().iter()
			.flat_map(|&WirePathSeg(dir, amount)|
				iter::repeat(dir).take(amount))
			.scan((0, 0), |pos, dir| {
				*pos += dir;
				Some(*pos) }))
	}
}


fn input_wires_from_str(s: &str) -> (impl Wire, impl Wire) {
	parsing::try_wires_from_str(s).unwrap()
}

fn input_wires() -> (impl Wire, impl Wire) {
	input_wires_from_str(include_str!("day03.txt"))
}


fn part1_impl(input_wires: (impl Wire, impl Wire)) -> i32 {
	use std::collections::HashSet;
	let poss = (
		input_wires.0.path_positions().collect::<HashSet<_>>(),
		input_wires.1.path_positions().collect::<HashSet<_>>());
	let (x, y) = poss.0.intersection(&poss.1)
		.min_by_key(|&&p| p.0.abs() + p.1.abs())
		.copied()
		.unwrap();
	x.abs() + y.abs()
}

pub(crate) fn part1() -> i32 {
	part1_impl(input_wires())
}


fn part2_impl(input_wires: (impl Wire, impl Wire)) -> usize {
	use std::collections::HashMap;

	// TODO(bm-w): Use something like `from_iter` but keeping old values upon conflicts
	let mut wire0_poss = HashMap::new();
	for (steps, pos) in input_wires.0.path_positions().enumerate() {
		_ = wire0_poss.entry(pos).or_insert(steps);
	}

	let mut intsect_steps: Option<usize> = None;
	for (wire1_steps, pos) in input_wires.1.path_positions().enumerate() {
		if let Some(&wire0_steps) = wire0_poss.get(&pos) {
			if let Some(intsect_steps) = intsect_steps.as_mut() {
				*intsect_steps = (*intsect_steps).min(wire0_steps + wire1_steps);
			} else {
				intsect_steps = Some(wire0_steps + wire1_steps);
			}
		}
	}

	// Adding 2 because the first steps from the origin were not counted
	intsect_steps.unwrap() + 2
}


pub(crate) fn part2() -> usize {
	part2_impl(input_wires())
}


mod parsing {
	use std::{mem, num::ParseIntError, str::FromStr};
	use super::{Dir, WirePathSeg, Wire};

	#[derive(Debug)]
	pub(super) struct DirError(char);

	impl TryFrom<char> for Dir {
		type Error = DirError;
		fn try_from(value: char) -> Result<Self, Self::Error> {
			match value {
				'U' => Ok(Dir::Up),
				'D' => Ok(Dir::Down),
				'L' => Ok(Dir::Left),
				'R' => Ok(Dir::Right),
				invalid => Err(DirError(invalid)),
			}
		}
	}

	#[derive(Debug)]
	pub(super) enum WirePathSegError {
		Format,
		Dir(DirError),
		Amount(ParseIntError),
	}

	impl FromStr for WirePathSeg {
		type Err = WirePathSegError;
		fn from_str(s: &str) -> Result<Self, Self::Err> {
			let mut chars = s.chars();
			let dir = chars.next()
				.ok_or(WirePathSegError::Format)
				.and_then(|d| d.try_into()
					.map_err(WirePathSegError::Dir))?;
			let amount = chars.as_str().parse()
				.map_err(WirePathSegError::Amount)?;
			Ok(WirePathSeg(dir, amount))
		}
	}

	#[allow(dead_code)]
	#[derive(Debug)]
	pub(super) struct WireError {
		column: usize,
		source: WirePathSegError,
	}

	fn try_wire_from_str(s: &str) -> Result<Vec<WirePathSeg>, WireError> {
		s
			.split(',')
			.scan(0, |c, seg| {
				let c = mem::replace(c, *c + seg.len() + 1);
				Some((c, seg))
			})
			.map(|(c, seg)| seg.parse()
				.map_err(|e| WireError { column: c + 1, source: e }))
			.collect::<Result<Vec<_>, _>>()
	}

	#[allow(dead_code)]
	#[derive(Debug)]
	pub(super) struct WiresError {
		line: usize,
		source: Option<WireError>,
	}

	fn try_wire_vecs_from_str(s: &str) -> Result<(Vec<WirePathSeg>, Vec<WirePathSeg>), WiresError> {
		let mut iter = s.lines()
			.enumerate()
			.map(|(l, line)| try_wire_from_str(line)
				.map_err(|e| WiresError { line: l + 1, source: Some(e) }))
			.fuse();
		let w0 = iter.next().ok_or(WiresError { line: 1, source: None })??;
		let w1 = iter.next().ok_or(WiresError { line: 2, source: None })??;
		if iter.next().is_some() { return Err(WiresError { line: 3, source: None }) }
		Ok((w0, w1))
	}

	impl Wire for Vec<WirePathSeg> {}

	#[allow(dead_code)]
	pub(super) fn try_wires_from_str(s: &str) -> Result<(impl Wire, impl Wire), WiresError> {
		try_wire_vecs_from_str(s)
	}

	#[test]
	fn tests() -> Result<(), WiresError> {
		use {WirePathSeg as Seg, Dir::*};
		let ww0 = try_wire_vecs_from_str(super::tests::INPUT.0)?;
		assert_eq!(ww0.0, [Seg(Right, 8), Seg(Up, 5), Seg(Left, 5), Seg(Down, 3)]);
		assert_eq!(ww0.1, [Seg(Up, 7), Seg(Right, 6), Seg(Down, 4), Seg(Left, 4)]);
		try_wires_from_str(super::tests::INPUT.1)?;
		try_wires_from_str(super::tests::INPUT.2)?;
		Ok(())
	}
}


#[cfg(test)]
mod tests {
	use indoc::indoc;
	use super::*;


	pub(super) const INPUT: (&str, &str, &str) = (
		indoc! { "
			R8,U5,L5,D3
			U7,R6,D4,L4
		" },
		indoc! { "
			R75,D30,R83,U83,L12,D49,R71,U7,L72
			U62,R66,U55,R34,D71,R55,D58,R83
		" },
		indoc! { "
			R98,U47,R26,D63,R33,U87,L62,D20,R33,U53,R51
			U98,R91,D20,R16,D67,R40,U7,R15,U6,R7
		" },
	);

	#[test]
	fn tests() {
		assert_eq!(part1_impl(input_wires_from_str(INPUT.0)), 6);
		assert_eq!(part1_impl(input_wires_from_str(INPUT.1)), 159);
		assert_eq!(part1_impl(input_wires_from_str(INPUT.2)), 135);
		assert_eq!(part1(), 1017);
		assert_eq!(part2_impl(input_wires_from_str(INPUT.0)), 30);
		assert_eq!(part2_impl(input_wires_from_str(INPUT.1)), 610);
		assert_eq!(part2_impl(input_wires_from_str(INPUT.2)), 410);
		assert_eq!(part2(), 11432);
	}
}