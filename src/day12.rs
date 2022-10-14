// Copyright (c) 2022 Bastiaan Marinus van de Weerd


#[derive(PartialEq, Eq, Clone)]
#[cfg_attr(test, derive(Debug))]
struct _Moon<const A: usize> {
	pos: [isize; A],
	vel: [isize; A],
}

type Moon = _Moon<3>;
type MoonAxis = _Moon<1>;

impl Moon {
	fn energy(&self) -> usize {
		use Axis::*;
		((self.pos[X].abs() + self.pos[Y].abs() + self.pos[Z].abs())
			* (self.vel[X].abs() + self.vel[Y].abs() + self.vel[Z].abs()))
				as usize
	}
}


#[derive(Clone, Copy)]
enum Axis { X, Y, Z }
const AXES: [Axis; 3] = [Axis::X, Axis::Y, Axis::Z];

impl Axis {
	fn as_usize(&self) -> usize {
		use Axis::*;
		match self { X => 0, Y => 1, Z => 2 }
	}
}

impl<T> std::ops::Index<Axis> for [T] {
	type Output = T;
	fn index(&self, axis: Axis) -> &Self::Output {
		&self[axis.as_usize() as usize]
	}
}

impl<T> std::ops::IndexMut<Axis> for [T] {
	fn index_mut(&mut self, axis: Axis) -> &mut Self::Output {
		&mut self[axis.as_usize() as usize]
	}
}


trait System: AsRef<[Moon]> + AsMut<[Moon]> {
	fn tick_with<G, V>(&mut self, apply_gravity: G, apply_velocity: V)
	where G: Fn(&mut Moon, &mut Moon), V: Fn(&mut Moon) {
		use itertools::Itertools as _;

		let moons = self.as_mut();
		for (idx0, idx1) in (0..moons.len()).tuple_combinations() {
			let (moon0, moon1) = {
				let (head, tail) = moons.split_at_mut(idx1);
				(&mut head[idx0], &mut tail[0])
			};
			apply_gravity(moon0, moon1)
		}

		for moon in moons {
			apply_velocity(moon)
		}
	}

	#[inline]
	fn apply_gravity_axis(moon0: &mut Moon, moon1: &mut Moon, axis: Axis) {
		match (moon0.pos[axis], moon1.pos[axis]) {
			(hi, lo) if hi > lo => { moon0.vel[axis] -= 1; moon1.vel[axis] += 1; }
			(lo, hi) if hi > lo => { moon0.vel[axis] += 1; moon1.vel[axis] -= 1; }
			_ => (),
		}
	}

	#[inline]
	fn apply_velocity_axis(moon: &mut Moon, axis: Axis) {
		moon.pos[axis] += moon.vel[axis]
	}

	fn tick(&mut self) {
		self.tick_with(
			|moon0, moon1| for a in AXES { Self::apply_gravity_axis(moon0, moon1, a) },
			|moon| for a in AXES { Self::apply_velocity_axis(moon, a) }
		)
	}

	fn tick_axis(&mut self, axis: Axis) {
		self.tick_with(
			|moon0, moon1| Self::apply_gravity_axis(moon0, moon1, axis),
			|moon| Self::apply_velocity_axis(moon, axis),
		)
	}

	// TODO: Return `impl Iterator<…>` once Rust allows it from trait methods
	fn axis_moons(&self, axis: Axis) -> Box<dyn Iterator<Item = MoonAxis> + '_>  {
		Box::new(self.as_ref().iter().map(move |m| MoonAxis { pos: [m.pos[axis]], vel: [m.vel[axis]] }))
	}

	fn energy(&self) -> usize {
		self.as_ref().iter().map(|m| m.energy()).sum()
	}
}

impl System for Vec<Moon> {}


fn input_system_from_str(s: &str) -> impl System {
	parsing::try_moons_from_str(s).unwrap()
}

fn input_system() -> impl System {
	input_system_from_str(include_str!("day12.txt"))
}


fn part1_impl<const N: usize>(mut input_system: impl System) -> usize {
	for _ in 0..N { input_system.tick() }
	input_system.energy()
}

pub(crate) fn part1() -> usize {
	part1_impl::<1000>(input_system())
}


fn part2_impl(mut input_system: impl System) -> usize {
	use {itertools::Itertools as _, num_integer::lcm};

	let periods: (_, _, _) = AXES.into_iter()
		.map(|axis| {
			let initial_moons = input_system.axis_moons(axis).collect::<Vec<_>>();
			for i in 1.. {
				input_system.tick_axis(axis);
				if input_system.axis_moons(axis).eq(initial_moons.iter().cloned()) {
					return i
				}
			}
			unreachable!()
		})
		.collect_tuple()
		.unwrap();
	lcm(lcm(periods.0, periods.1), periods.2)
}

pub(crate) fn part2() -> usize {
	part2_impl(input_system())
}


mod parsing {
	use super::Moon;
	use std::{num::ParseIntError, str::FromStr};

	#[derive(Debug)]
	pub(super) enum MoonErrorKind {
		Format,
		X(ParseIntError),
		Y(ParseIntError),
		Z(ParseIntError),
	}

	#[allow(dead_code)]
	#[derive(Debug)]
	pub(super) struct MoonError { column: usize, kind: MoonErrorKind }

	impl FromStr for Moon {
		type Err = MoonError;
		fn from_str(s: &str) -> Result<Self, Self::Err> {
			use MoonErrorKind::*;
			let s = s.strip_prefix("<x=").ok_or(MoonError { column: 1, kind: Format })?;
			let (x, s) = s.split_once(", y=").ok_or(MoonError { column: 4, kind: Format })?;
			let (x, column) = (x.parse().map_err(|e| MoonError { column: 4, kind: X(e) })?, 8 + x.len());
			let (y, s) = s.split_once(", z=").ok_or(MoonError { column, kind: Format })?;
			let (y, column) = (y.parse().map_err(|e| MoonError { column, kind: Y(e) })?, column + y.len() + 4);
			let z = s.strip_suffix('>').ok_or(MoonError { column: column + s.len() - 1, kind: Format })?;
			let z = z.parse().map_err(|e| MoonError { column, kind: Z(e) })?;
			Ok(Moon { pos: [x, y, z], vel: [0; 3] })
		}
	}

	#[allow(dead_code)]
	#[derive(Debug)]
	pub(super) struct MoonsError { line: usize, source: MoonError }

	pub(super) fn try_moons_from_str(s: &str) -> Result<Vec<Moon>, MoonsError> {
		s.lines()
			.enumerate()
			.map(|(l, line)| line.parse()
				.map_err(|e| MoonsError { line: l + 1, source: e }))
			.collect()
	}
}


#[test]
fn tests() {
	const INPUTS: [&str; 2] = [
		indoc::indoc! { "
			<x=-1, y=0, z=2>
			<x=2, y=-10, z=-7>
			<x=4, y=-8, z=8>
			<x=3, y=5, z=-1>
		" },
		indoc::indoc! { "
			<x=-8, y=-10, z=0>
			<x=5, y=5, z=10>
			<x=2, y=-7, z=3>
			<x=9, y=-8, z=-3>
		" },
	];
	assert_eq!(part1_impl::<10>(input_system_from_str(INPUTS[0])), 179);
	assert_eq!(part1_impl::<100>(input_system_from_str(INPUTS[1])), 1940);
	assert_eq!(part1(), 9876);
	assert_eq!(part2_impl(input_system_from_str(INPUTS[0])), 2772);
	assert_eq!(part2_impl(input_system_from_str(INPUTS[1])), 4_686_774_924);
	assert_eq!(part2(), 307_043_147_758_488);
}
