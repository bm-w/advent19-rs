// Copyright (c) 2022 Bastiaan Marinus van de Weerd

use crate::day05::{parsing::from_str as input_program_from_str, Program, ProgramState};


#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Move { North, South, West, East, }

impl Move {
	fn next(&self) -> Self {
		use Move::*;
		match self { North => East, South => West, West => North, East => South }
	}

	fn inv(&self) -> Self {
		use Move::*;
		match self { North => South, South => North, West => East, East => West }
	}

	fn prev(&self) -> Self {
		self.next().inv()
	}

	fn pos_from(&self, pos: &[isize; 2]) -> [isize; 2] {
		use Move::*;
		match self {
			North => [pos[0], pos[1] - 1],
			South => [pos[0], pos[1] + 1],
			West => [pos[0] - 1, pos[1]],
			East => [pos[0] + 1, pos[1]],
		}
	}

	fn next_iter(&self) -> impl Iterator<Item = Self> {
		(0..4).scan(*self, move |l, _| { *l = l.next(); Some(*l) })
	}

	fn next_pos_iter_from(&self, pos: [isize; 2]) -> impl Iterator<Item = ([isize; 2], Self)> {
		self.next_iter().map(move |m| (m.pos_from(&pos), m))
	}

	fn to_origin(from: [isize; 2]) -> Self {
		use Move::*;
		if from == [0; 2] { return North } // Whatever…
		if from[0] > 0 && (if from[1] > 0 { from[1] <= from[0] } else { -from[1] < from[0] }) { West }
		else if from[1] > 0 && -from[0] <= from[1] { North }
		else if from[0] <= from[1] { East }
		else { South }
	}

	fn to_pos(pos: [isize; 2], from: [isize; 2]) -> Self {
		Self::to_origin([from[0] - pos[0], from[1] - pos[1]])
	}
}

impl From<Move> for i64 {
	fn from(r#move: Move) -> Self {
		use Move::*;
		match r#move { North => 1, South => 2, West => 3, East => 4 }
	}
}


#[derive(Clone, Copy)]
enum Tile { Empty, Wall, System, Oxygen}
type Tiles = std::collections::HashMap<[isize; 2], Tile>;


struct RepairDroid([isize; 2]);

impl RepairDroid {
	fn find_target(&self, tiles: &Tiles) -> Option<[isize; 2]> {
		use {std::collections::{HashSet, VecDeque}, Tile::*};

		let proto_move = Move::to_origin(self.0).prev();

		let mut seen = HashSet::new();
		let mut queue = VecDeque::from_iter(proto_move.next_pos_iter_from(self.0));
		while let Some((pos, _)) = queue.pop_front() {
			if !seen.insert(pos) { continue }
			match tiles.get(&pos) {
				Some(Wall) => continue,
				Some(_) => queue.extend(proto_move.next_pos_iter_from(pos)),
				None => return Some(pos)
			}
		}
		None
	}

	fn path(&self, tiles: &Tiles, target: [isize; 2]) -> Option<impl IntoIterator<Item = Move>> {
		use {std::collections::{BinaryHeap, HashMap, hash_map::Entry::*}, num_integer::Roots};

		// Dijkstra

		#[derive(PartialEq, Eq)]
		struct State { pos: [isize; 2], r#move: Option<Move>, cost: usize }

		impl Ord for State {
			fn cmp(&self, other: &Self) -> std::cmp::Ordering {
				other.cost.cmp(&self.cost)
					.then_with(|| self.pos.cmp(&other.pos))
					.then_with(|| self.r#move.cmp(&other.r#move))
			}
		}

		impl PartialOrd for State {
			fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
				Some(self.cmp(other))
			}
		}

		let proto_move = Move::to_pos(target, self.0).prev();

		let mut heap = BinaryHeap::new();
		heap.push(State { pos: self.0, r#move: None, cost: 0 });
		let mut found = HashMap::new();
		let mut fog_cost = 1_usize;

		while let Some(state) = heap.pop() {
			match found.entry(state.pos) {
				Vacant(entry) => {
					entry.insert((state.cost, state.r#move));
				}
				Occupied(mut entry) => {
					if state.cost > entry.get().0 { continue }
					*entry.get_mut() = (state.cost, state.r#move);
				}
			};

			if state.pos == target { break }

			for next_move in state.r#move.unwrap_or(proto_move).next_iter() {
				let next_pos = next_move.pos_from(&state.pos);
				let add_cost = match tiles.get(&next_pos) {
					Some(Tile::Wall) => continue,
					None => { fog_cost += fog_cost.sqrt(); fog_cost },
					_ => 1,
				};
				heap.push(State { pos: next_pos, r#move: Some(next_move), cost: state.cost + add_cost });
			}
		}

		// Walk back from the target
		let mut inv_path = (0..).scan(target, |target, _| {
			let Some(&(_, Some(found_move))) = found.get(target) else { return None };
			*target = found_move.inv().pos_from(target);
			Some(found_move)
		}).peekable();
		inv_path.peek().is_some().then(|| inv_path.collect::<Vec<_>>().into_iter().rev())
	}

	fn r#move<'a>(&mut self,
		r#move: Move,
		program: &mut impl Program<'a, i64>,
		program_state: &mut ProgramState<'a, i64>,
	) -> ([isize; 2], Tile) {
		use std::iter::once;
		let target = r#move.pos_from(&self.0);
		let tile = match program.safe_output(program_state, once(r#move.into())) {
			Ok(Some(0)) => return (target, Tile::Wall),
			Ok(Some(1)) => Tile::Empty,
			Ok(Some(2)) => Tile::System,
			Ok(Some(invalid)) => { panic!("Invalid program return code {invalid}"); }
			Ok(None) => { panic!("Unexpected end of program"); }
			Err(err) => { panic!("{err}"); }
		};
		self.0 = target;
		(target, tile)
	}
}


#[cfg(test)]
mod displaying {
	use {std::fmt::Display, super::*};

	#[cfg(test)]
	pub(super) struct ShipSection<'a>(pub(super) &'a Tiles, pub(super) &'a RepairDroid);

	#[cfg(test)]
	impl ShipSection<'_> {
		// Returns top-left (min. coords.) and bottom-right (max. coords) corner positions (inclusive).
		fn extents(&self) -> [[isize; 2]; 2] {
			let &ShipSection(tiles, &RepairDroid(droid_pos)) = self;
			let mut min = droid_pos;
			let mut max = droid_pos;
			for pos in tiles.keys() {
				min[0] = min[0].min(pos[0]);
				min[1] = min[1].min(pos[1]);
				max[0] = max[0].max(pos[0]);
				max[1] = max[1].max(pos[1]);
			}
			[min, max]
		}
	}

	#[cfg(test)]
	impl<'a> Display for ShipSection<'a> {
		fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
			use {std::fmt::Write, Tile::*};

			let &ShipSection(tiles, &RepairDroid(droid_pos)) = self;
			let extents = self.extents();

			for y in extents[0][1]..=extents[1][1] {
				for x in extents[0][0]..=extents[1][0] {
					f.write_char(match [x, y] {
						[0, 0] => 'o',
						xy if xy == droid_pos => 'D',
						[x, y] if x == y || x == -y => match tiles.get(&[x, y]) {
							Some(Empty) => 'x',
							Some(Wall) => 'X',
							Some(System) => 'Z',
							Some(Oxygen) => '0',
							None => ' ',
						},
						xy => match tiles.get(&xy) {
							Some(Empty) => '.',
							Some(Wall) => '#',
							Some(System) => 'S',
							Some(Oxygen) => 'O',
							None => ' ',
						}
					})?;
				}
				if y < extents[1][1] { f.write_char('\n')?; }
			}

			Ok(())
		}
	}
}


struct PreludeState<'a, P> where  P: Program<'a, i64> {
	program: P,
	program_state: ProgramState<'a, i64>,
	tiles: Tiles,
	droid: RepairDroid,
	system_pos: [isize; 2],
}

fn part1and2_prelude(stop_at_system: bool) -> PreludeState<'static, impl Program<'static>> {
	let mut program = input_program_from_str::<i64>(include_str!("day15.txt"));
	let mut program_state = ProgramState::new(true);

	let mut tiles = Tiles::new();
	let mut droid = RepairDroid([0; 2]);
	tiles.insert(droid.0, Tile::Empty);

	let mut system_pos = None;

	// Repeatedly find undiscovered tiles and send the droid to explore them
	'finding: while let Some(target) = droid.find_target(&tiles) {
		let path = droid.path(&tiles, target).unwrap();
		for r#move in path {
			let (tile_pos, tile) = droid.r#move(r#move, &mut program, &mut program_state);
			tiles.insert(tile_pos, tile);
			if matches!(tile, Tile::System) {
				system_pos = Some(tile_pos);
				if stop_at_system { break 'finding }
			}
		}
	};

	PreludeState { program, program_state, tiles, droid, system_pos: system_pos.unwrap() }
}


pub(crate) fn part1() -> usize {
	let PreludeState {
		mut program,
		mut program_state,
		mut tiles,
		mut droid,
		system_pos,
	} = part1and2_prelude(true);

	// Find the path back from the oxygen system to the origin
	'pathing: loop {
		let mut pos = system_pos;
		let path = RepairDroid(pos).path(&tiles, [0; 2]).unwrap();

		let mut moves = 0;
		for r#move in path {
			pos = r#move.pos_from(&pos);

			// If trying to path through an undiscovered tile, send the droid to explore whether it’s not a wall
			if !tiles.contains_key(&pos) {
				for r#move in droid.path(&tiles, pos).unwrap() {
					let (tile_pos, tile) = droid.r#move(r#move, &mut program, &mut program_state);
					if matches!(tile, Tile::Wall) {
						tiles.insert(tile_pos, tile);
						continue 'pathing
					}
				}
			}
			moves += 1;
		}
		return moves
	}
}


pub(crate) fn part2() -> usize {
	use std::collections::HashSet;

	let PreludeState {
		mut tiles,
		system_pos,
		..
	} = part1and2_prelude(false);
	
	let mut recently_filled = HashSet::new();
	assert!(recently_filled.insert(system_pos));
	for i in 0.. {
		let mut now_filled = HashSet::new();
		for filled_pos in recently_filled.drain() {
			for (pos, _) in Move::North.next_pos_iter_from(filled_pos) {
				match tiles.get(&pos) {
					Some(Tile::Empty) if now_filled.insert(pos) => {
						tiles.insert(pos, Tile::Oxygen);
					}
					Some(_) => continue,
					None => panic!("All tiles should already be explored"),
				}
			}
		}
		if now_filled.is_empty() { return i }
		recently_filled.clone_from(&now_filled);
	}

	unreachable!()
}


#[test]
fn tests() {
	assert_eq!(part1(), 318);
	assert_eq!(part2(), 390)
}
