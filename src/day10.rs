// Copyright (c) 2022 Bastiaan Marinus van de Weerd


type ContainsAsteroid = bool;

struct Map {
	asteroids: Vec<ContainsAsteroid>,
	width: usize,
}

fn pseudonormalized_dir(dir: [isize; 2]) -> [isize; 2] {
	let div = match dir {
		[d0, 0] => d0.abs(),
		[0, d1] => d1.abs(),
		[d0, d1] => num_integer::gcd(d0.abs(), d1.abs()),
	};
	[dir[0] / div, dir[1] / div]
}

impl Map {
	fn pos_from_idx(&self, idx: usize) -> [usize; 2] {
		[idx % self.width, idx / self.width]
	}

	/// Returns index, position, & score (i.e. how many asteroids detectable).
	fn best(&self) -> Option<(usize, [usize; 2], usize)> {
		self.asteroids.iter()
			.enumerate()
			.filter_map(|(idx0, &contains_asteroid)| {
				use std::collections::HashSet;
				if !contains_asteroid { return None }
				let origin = self.pos_from_idx(idx0);
				let score: usize = self.asteroids.iter()
					.enumerate()
					.filter(|(_, &ca)| ca)
					.filter_map(|(idx, _)| {
						let pos = self.pos_from_idx(idx);
						if pos == origin { return None }
						Some(pseudonormalized_dir([
							pos[0] as isize - origin[0] as isize,
							pos[1] as isize - origin[1] as isize
						]))
					})
					.collect::<HashSet<[isize; 2]>>()
					.len();
				Some((idx0, origin, score))
			})
			.max_by_key(|&(_, _, score)| score)
	}
}


fn input_map_from_str(s: &str) -> Map {
	s.parse().unwrap()
}

fn input_map() -> Map {
	input_map_from_str(include_str!("day10.txt"))
}


fn part1_impl(input_map: Map) -> usize {
	input_map.best().unwrap().2
}

pub(crate) fn part1() -> usize {
	part1_impl(input_map())
}


fn part2_impl<const N: usize>(input_map: Map) -> usize {
	use std::{collections::HashSet, f32::consts::PI, ops::{Add, Mul}};

	assert!(input_map.asteroids.iter().filter(|&&ca| ca).nth(N).is_some());

	let (idx, origin, _) = input_map.best().unwrap();
	let mut discarded = HashSet::with_capacity(N);
	discarded.insert(idx);

	fn dot<T: Add<Output = T> + Mul<Output = T> + Copy>(lhs: [T; 2], rhs: [T; 2]) -> T {
		lhs[0] * rhs[0] + lhs[1] * rhs[1]
	}

	// Starting slightly “behind” so that any asteroid directly
	// “above” the station (in the XY plane) will be hit first.
	let mut laser_dir = [-1, -(input_map.asteroids.len() as isize)];

	let nth_hit_pos = loop {
		let laser_norm = {
			let v = [laser_dir[0] as f32, laser_dir[1] as f32];
			let mag = dot(v, v).sqrt();
			[v[0] / mag, v[1] / mag]
		};
		let laser_ortho = [-laser_norm[1], laser_norm[0]];
		let (next_hit, pos, _, _) = input_map.asteroids.iter()
			.enumerate()
			.filter_map(|(i, &contains_asteroid)| {
				if !contains_asteroid || discarded.contains(&i) { return None }
				let pos = input_map.pos_from_idx(i);
				let delta = [
					pos[0] as isize - origin[0] as isize,
					pos[1] as isize - origin[1] as isize
				];
				let dist = (dot(delta, delta) as f32).sqrt();
				let delta = pseudonormalized_dir(delta);
				let angle = if delta == laser_dir { f32::INFINITY } else {
					let delta = [delta[0] as f32, delta[1] as f32];
					let laser_delta = [dot(delta, laser_norm), dot(delta, laser_ortho)];
					(-laser_delta[1]).atan2(-laser_delta[0]) + PI
				};
				Some((i, pos, angle, dist))
			})
			.min_by(|l, r| {
				l.2.total_cmp(&r.2).then(l.3.total_cmp(&r.3))
			})
			.unwrap();
		if discarded.len() == N { break pos }
		discarded.insert(next_hit);
		laser_dir = pseudonormalized_dir([
			pos[0] as isize - origin[0] as isize,
			pos[1] as isize - origin[1] as isize
		]);
	};

	nth_hit_pos[0] * 100 + nth_hit_pos[1]
}

pub(crate) fn part2() -> usize {
	part2_impl::<200>(input_map())
}


mod parsing {
	use std::str::FromStr;
	use super::Map;

	#[derive(Debug)]
	pub(super) enum MapErrorKind {
		Format,
		Asteroid(char)
	}

	#[derive(Debug)]
	#[allow(dead_code)]
	pub(super) struct MapError {
		line: usize,
		column: usize,
		kind: MapErrorKind,
	}

	impl FromStr for Map {
		type Err = MapError;
		fn from_str(s: &str) -> Result<Self, Self::Err> {
			use {std::iter::once, itertools::Either, MapErrorKind::*};
			if s.is_empty() { return Err(MapError { line: 1, column: 1, kind: Format }) }
			let mut lines = s.lines().peekable();
			// SAFETY: Already checked `s.is_empty()` above.
			let width = unsafe { lines.peek().unwrap_unchecked().len() };
			let asteroids = s.lines()
				.enumerate()
				.flat_map(|(l, line)| if line.len() != width {
					Either::Left(once(Err(MapError { line: l + 1, column: line.len() + 1, kind: Format })))
				} else {
					Either::Right(line.chars()
						.enumerate()
						.map(move |(c, chr)| match chr {
							'#' => Ok(true),
							'.' => Ok(false),
							chr => Err(MapError { line: l + 1, column: c + 1, kind: Asteroid(chr) })
						}))
				})
				.collect::<Result<_, _>>()?;
			Ok(Map { asteroids, width })
		}
	}
}


#[test]
fn tests() {
	const INPUTS: [&str; 5] = [
		indoc::indoc! { "
			.#..#
			.....
			#####
			....#
			...##
		" },
		indoc::indoc! { "
			......#.#.
			#..#.#....
			..#######.
			.#.#.###..
			.#..#.....
			..#....#.#
			#..#....#.
			.##.#..###
			##...#..#.
			.#....####
		" },
		indoc::indoc! { "
			#.#...#.#.
			.###....#.
			.#....#...
			##.#.#.#.#
			....#.#.#.
			.##..###.#
			..#...##..
			..##....##
			......#...
			.####.###.
		" },
		indoc::indoc! { "
			.#..#..###
			####.###.#
			....###.#.
			..###.##.#
			##.##.#.#.
			....###..#
			..#.#..#.#
			#..#.#.###
			.##...##.#
			.....#.#..
		" },
		indoc::indoc! { "
			.#..##.###...#######
			##.############..##.
			.#.######.########.#
			.###.#######.####.#.
			#####.##.#.##.###.##
			..#####..#.#########
			####################
			#.####....###.#.#.##
			##.#################
			#####.##.###..####..
			..######..##.#######
			####.##.####...##..#
			.#####..#.######.###
			##...#.##########...
			#.##########.#######
			.####.#.###.###.#.##
			....##.##.###..#####
			.#.#.###########.###
			#.#.#.#####.####.###
			###.##.####.##.#..##
		" },
	];
	assert_eq!(part1_impl(input_map_from_str(INPUTS[0])), 8);
	assert_eq!(part1_impl(input_map_from_str(INPUTS[1])), 33);
	assert_eq!(part1_impl(input_map_from_str(INPUTS[2])), 35);
	assert_eq!(part1_impl(input_map_from_str(INPUTS[3])), 41);
	assert_eq!(part1_impl(input_map_from_str(INPUTS[4])), 210);
	assert_eq!(part1(), 253);
	assert_eq!(part2_impl::<9>(input_map_from_str(INPUTS[0])), 100);
	assert_eq!(part2_impl::<200>(input_map_from_str(INPUTS[4])), 802);
	assert_eq!(part2(), 815);
}
