// Copyright (c) 2022 Bastiaan Marinus van de Weerd


mod vault {
	#[cfg_attr(nop, derive(Debug))]
	#[derive(Clone, Copy, PartialEq, Eq)]
	pub(super) enum OpenSpaceItem {
		Key(u32),
		Door(u32),
	}

	#[cfg_attr(nop, derive(Debug))]
	#[derive(Clone, Copy, PartialEq, Eq)]
	pub(super) enum Space {
		Open(Option<OpenSpaceItem>),
		Wall,
	}

	// TODO(bm-w): Drop `NUM_COLLECTORS` (as of Rust 1.66-beta it’s needed to make `impl Diplay for Grid` work)
	pub(super) struct Grid<Collectors, const NUM_COLLECTORS: usize> {
		pub(super) spaces: Vec<Space>,
		pub(super) width: usize,
		pub(super) collectors: Collectors,
	}

	impl<Collectors, const NUM_COLLECTORS: usize> Grid<Collectors, NUM_COLLECTORS> {
		fn adjacent_positions(&self, from_pos: usize) -> impl Iterator<Item = usize> {
			let (p, s, l) = (from_pos as isize, self.width as isize, self.spaces.len() as isize);
			[p - s, p - 1, p + 1, p + s]
				.into_iter()
				.filter_map(move |p| (p >= 0 && p < l).then_some(p as usize))
		}

		// Returns an iterator over items (key or door), positions, and distances.
		fn reachable_items(&self, from_pos: usize) -> impl Iterator<Item = (&OpenSpaceItem, usize, usize)> + '_ {
			use std::{collections::{HashSet, VecDeque}, iter::from_fn};

			// Breadth-first flood-fill
			let mut queue = VecDeque::new();
			let mut seen = HashSet::new();
			queue.push_back((from_pos, 0));
			from_fn(move || {
				while let Some((pos, cost)) = queue.pop_front() {
					if !seen.insert(pos) { continue }
					if pos == from_pos || matches!(&self.spaces[pos], &Space::Open(None)) {
						for adj_pos in self.adjacent_positions(pos)
								.into_iter()
								.filter(move |p| !matches!(&self.spaces[*p], Space::Wall)) {
							queue.push_back((adj_pos, cost + 1));
						}
					}
					if pos != from_pos {
						if let Space::Open(Some(item)) = &self.spaces[pos] {
							return Some((item, pos, cost))
						}
					}
				}
				None
			})
		}
	}

	// TODO(bm-w): Turn `LEN` into an associated constant once support has improved
	// (See e.g. nightly features `associated_const_equality` and `generic_const_exprs`)
	pub(super) trait Collectors<const LEN: usize> {
		fn positions(&self) -> [usize; LEN];
	}

	#[cfg(LOGGING)]
	// NOTE(bm-w): This `impl` fails to compile without `NUM_COLLECTORS` on `Grid`.
	impl<const NUM_COLLECTORS: usize, C: Collectors<NUM_COLLECTORS>> std::fmt::Display for Grid<C, NUM_COLLECTORS> {
		fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
			use std::fmt::Write;
	
			let height = self.spaces.len() / self.width;
			for y in 0..height {
				for x in 0..self.width {
					use {OpenSpaceItem::*, Space::*};
					let pos = y * self.width + x;
					f.write_char(if self.collectors.positions().contains(&pos) {
						'@'
					} else { match &self.spaces[pos] {
						Open(None) => '.',
						Open(Some(Key(key))) => (b'a' + key.trailing_zeros() as u8) as char,
						Open(Some(Door(door))) => (b'A' + door.trailing_zeros() as u8) as char,
						Wall => '#',
					} })?
				}
				if y < height - 1 { f.write_char('\n')? }
			}
			Ok(())
		}
	}

	const NUM_KEYS: usize = 26;
	const NUM_DOORS: usize = NUM_KEYS;

	pub(super) struct Graph<const NUM_COLLECTORS: usize, const DOORS: bool> {
		edges: Vec<Option<usize>>,
		known_nodes: u64,
	}

	impl<
		const NUM_COLLECTORS: usize,
		Collectors: self::Collectors<NUM_COLLECTORS>
	> From<&Grid<Collectors, NUM_COLLECTORS>> for Graph<NUM_COLLECTORS, true> {
		fn from(grid: &Grid<Collectors, NUM_COLLECTORS>) -> Self {

			let collectors_poss = 0..NUM_COLLECTORS;
			let key_nodes = collectors_poss.end..collectors_poss.end + NUM_KEYS;
			let door_nodes = key_nodes.end..key_nodes.end + NUM_DOORS;
			let num_nodes = door_nodes.end;

			let mut known_nodes: u64 = 0;
			let mut edges = vec![None; num_nodes * num_nodes];
			let mut collectors_offset = 0;
			for (pos, space) in grid.spaces.iter().enumerate() {
				use {OpenSpaceItem::*, Space::*};
				let node = match space {
					_ if grid.collectors.positions().contains(&pos) => {
						let offset = collectors_offset;
						collectors_offset += 1;
						offset
					}
					Open(Some(Key(id))) =>
						key_nodes.start + id.trailing_zeros() as usize,
					Open(Some(Door(id))) =>
						door_nodes.start + id.trailing_zeros() as usize,
					Open(None) | Wall => continue,
				};
				known_nodes |= 1 << node;
				for (item, _, cost) in grid.reachable_items(pos) {
					let (id, cat) = match item {
						Key(id) => (*id, key_nodes.start),
						Door(id) => (*id, door_nodes.start),
					};
					edges[node * num_nodes + cat + id.trailing_zeros() as usize] = Some(cost);
				}
			}
			assert_eq!(collectors_offset, NUM_COLLECTORS);

			#[cfg(GRAPH_COMPACTING)]
			// NOTE(bm-w): Compacting doesn’t work for some inputs that “skip” key/door labels
			// (E.g. a test input has doors A, B, C, D, & F -- i.e. it “skips” door E)
			let num_nodes = if known != u64::MAX >> (64 - num_nodes) {
				let (mut sparse_node, mut compact_node) = (NUM_COLLECTORS, NUM_COLLECTORS);
				while let Some(node) = (sparse_node..num_nodes).find(|n| known & 1 << n != 0) {
					if node != compact_node {
						edges.copy_within(node * num_nodes..(node + 1) * num_nodes, compact_node * num_nodes);
					}
					sparse_node = node + 1;
					compact_node += 1;
				}

				let compact_num_nodes = compact_node;
				let (mut sparse_node, mut compact_node) = (NUM_COLLECTORS, NUM_COLLECTORS);
				while let Some(node) = (sparse_node..num_nodes).find(|n| known & 1 << n != 0) {
					if node != compact_node { for i in 0..compact_num_nodes {
						edges[i * num_nodes + compact_node] = edges[i * num_nodes + node];
					} }
					sparse_node = node + 1;
					compact_node += 1;
				}

				for node in 1..compact_num_nodes {
					let src = node * num_nodes;
					let src = src..src + compact_num_nodes;
					edges.copy_within(src, node * compact_num_nodes);
				}

				unsafe { edges.set_len(compact_num_nodes * compact_num_nodes); }
				edges.shrink_to_fit();

				compact_num_nodes
			} else {
				num_nodes
			};

			Graph { edges, known_nodes }
		}
	}

	impl<const NUM_COLLECTORS: usize, const DOORS: bool> Graph<NUM_COLLECTORS, DOORS> {
		const fn num_nodes() -> usize {
			NUM_COLLECTORS + NUM_KEYS + if DOORS { NUM_DOORS } else { 0 }
		}

		fn num_known_nodes(&self, nodes: impl Iterator<Item = usize>) -> usize {
			nodes.filter(|&n| self.known_nodes & 1 << n != 0).count()
		}

		pub(super) fn num_keys(&self) -> usize {
			self.num_known_nodes(NUM_COLLECTORS..NUM_COLLECTORS + NUM_KEYS)
		}

		fn is_key_node(node: usize) -> bool {
			node >= NUM_COLLECTORS && (!DOORS || node < NUM_COLLECTORS + NUM_KEYS)
		}

		fn key_id(node: usize) -> Option<u32> {
			#[allow(clippy::unnecessary_lazy_evaluations)]
			Self::is_key_node(node).then(|| 1 << (node - NUM_COLLECTORS))
		}

		#[cfg(LOGGING)]
		pub(super) fn node_as_char(&self, node: usize) -> char {
			if node < NUM_COLLECTORS { '@' }
			else if node < NUM_COLLECTORS + NUM_KEYS { (b'a' + (node - NUM_COLLECTORS) as u8) as char }
			else if node < Self::num_nodes() { (b'A' + (node - NUM_COLLECTORS - NUM_KEYS) as u8) as char }
			else { panic!("Invalid node {node}") }
		}
	}

	impl<const NUM_COLLECTORS: usize> Graph<NUM_COLLECTORS, false> {
		/// Returns an iterator over key nodes, key IDs, and costs.
		pub(super) fn keys_from(&self, node: usize) -> impl Iterator<Item = (usize, u32, usize)> + '_ {
			let num_nodes = Self::num_nodes();
			self.edges[node * num_nodes..(node + 1) * num_nodes].iter()
				.enumerate()
				.filter_map(|(node, &edge)|
					edge.zip(Self::key_id(node)).map(|(cost, key_id)| (node, key_id, cost)))
		}
	}

	impl<const NUM_COLLECTORS: usize> Graph<NUM_COLLECTORS, true> {

		#[cfg(LOGGING)]
		pub(super) fn num_doors(&self) -> usize {
			self.num_known_nodes(NUM_COLLECTORS + NUM_KEYS..NUM_COLLECTORS + NUM_KEYS + NUM_DOORS)
		}

		fn is_door_node(node: usize) -> bool {
			node >= NUM_COLLECTORS + NUM_KEYS
		}

		fn door_id(node: usize) -> Option<u32> {
			#[allow(clippy::unnecessary_lazy_evaluations)]
			Self::is_door_node(node).then(|| 1 << (node - NUM_COLLECTORS - NUM_KEYS))
		}

		pub(super) fn unlocked(&self, keys: u32) -> Graph<NUM_COLLECTORS, false> {
			use std::collections::BinaryHeap;

			#[derive(PartialEq, Eq)]
			struct State {
				node: usize,
				cost: usize,
			}
	
			impl PartialOrd for State {
				fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
					Some(self.cmp(other))
				}
			}
	
			impl Ord for State {
				fn cmp(&self, other: &Self) -> std::cmp::Ordering {
					self.cost.cmp(&other.cost).reverse().then_with(|| self.node.cmp(&other.node))
				}
			}

			let unlocked_num_nodes = Graph::<NUM_COLLECTORS, false>::num_nodes();
			let mut unlocked_edges = vec![None; unlocked_num_nodes * unlocked_num_nodes];

			let num_nodes = Self::num_nodes();
			let mut heap = BinaryHeap::new();
			let mut costs = vec![None; num_nodes];
			for node in 0..unlocked_num_nodes {
				if let Some(key) = Self::key_id(node) { if keys & key == 0 { continue } }

				heap.push(State { node, cost: 0 });
				if node > 0 { costs.fill(None); }

				while let Some(state) = heap.pop() {
					if let Some(cost) = costs[state.node] { if state.cost >= cost { continue } }
					costs[state.node] = Some(state.cost);
					if state.node != node {
						if let Some(key) = Self::key_id(state.node) {
							if keys & key == 0 {
								unlocked_edges[node * unlocked_num_nodes + state.node] = Some(state.cost);
								continue
							}
						}
					}
					let dests = state.node * num_nodes..(state.node + 1) * num_nodes;
					for (node, dest) in self.edges[dests].iter().enumerate() {
						let &Some(cost) = dest else { continue };
						if let Some(door) = Self::door_id(node) {
							if keys & door == 0 { continue }
						}
						heap.push(State { node, cost: state.cost + cost });
					}
				}
			}

			let unlocked_known_nodes = self.known_nodes & ((1 << (NUM_COLLECTORS + NUM_KEYS)) - 1);
			Graph { edges: unlocked_edges, known_nodes: unlocked_known_nodes }
		}
	}

	#[cfg(LOGGING)]
	impl<const NUM_COLLECTORS: usize, const DOORS: bool> std::fmt::Display for Graph<NUM_COLLECTORS, DOORS> {
		fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
			let num_nodes = Self::num_nodes();
			let known_nodes = (0..num_nodes).filter(|&n| self.known_nodes & 1 << n != 0);
			f.write_str("   ")?;
			for node in known_nodes.clone() { write!(f, "{:^5}|", self.node_as_char(node))?; }
			f.write_str("\n  +")?;
			for _ in known_nodes.clone() { f.write_str("-----+")?; }
			for node in known_nodes.clone() {
				write!(f, "\n{} |", self.node_as_char(node))?;
				let edges = node * num_nodes;
				for node in known_nodes.clone() {
					write!(f, "{:^5}|", match self.edges[edges + node] {
						Some(c) => c.to_string(),
						None => "".to_owned(),
					})?;
				}
			}
			Ok(())
		}
	}
}


struct Ship(usize);

impl vault::Collectors<1> for Ship {
	fn positions(&self) -> [usize; 1] {
		[self.0]
	}
}

struct Robots<const N: usize>([usize; N]);

impl<const N: usize> vault::Collectors<N> for Robots<N> {
	fn positions(&self) -> [usize; N] {
		self.0
	}
}


fn input_vault_for_str(s: &str) -> vault::Grid<Ship, 1> {
	s.parse().unwrap()
}

fn input_vault() -> vault::Grid<Ship, 1> {
	input_vault_for_str(include_str!("day18.txt"))
}


fn part1and2_impl<const NUM_COLLECTORS: usize>(input_vault_grid: vault::Grid<impl vault::Collectors<NUM_COLLECTORS>, NUM_COLLECTORS>) -> usize {

	use std::collections::{BinaryHeap, HashMap, hash_map::Entry::*};

	#[cfg(LOGGING)]
	use std::rc::Rc;

	#[cfg(LOGGING)]
	#[derive(PartialEq, Eq, Clone)]
	struct DbgPrevGraphNodes<const N: usize>([usize; N], Option<Rc<DbgPrevGraphNodes<N>>>);

	#[derive(PartialEq, Eq)]
	struct State<const N: usize> {
		graph_nodes: [usize; N],
		keys: u32,
		cost: usize,
		keys_len: usize,
		#[cfg(LOGGING)]
		dbg_prev_graph_nodes: Option<Rc<DbgPrevGraphNodes<N>>>,
	}

	impl<const N: usize> PartialOrd for State<N> {
		fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
			Some(self.cmp(other))
		}
	}

	impl<const N: usize> Ord for State<N> {
		fn cmp(&self, other: &Self) -> std::cmp::Ordering {
			self.cost.cmp(&other.cost).reverse()
				.then_with(|| self.keys_len.cmp(&other.keys_len))
				.then_with(|| self.graph_nodes[0].cmp(&other.graph_nodes[0]))
				.then_with(|| self.keys.cmp(&other.keys))
		}
	}

	#[cfg(LOGGING)]
	impl<const N: usize> State<N> {
		fn _dbg_graph_nodes(graph_poss: &[usize; N], node_as_char: impl Fn(usize) -> char) -> impl std::fmt::Display {
			graph_poss.iter().fold(String::new(), |mut s, &p| {
				if !s.is_empty() { s.push(','); }
				s.push(node_as_char(p));
				s
			})
		}

		fn dbg_graph_nodes(&self, node_as_char: impl Fn(usize) -> char) -> impl std::fmt::Display {
			Self::_dbg_graph_nodes(&self.graph_nodes, node_as_char)
		}

		fn dbg_keys(&self) -> String {
			if self.keys == 0 { return "∅".to_owned() }
			(b'a'..=b'z')
				.enumerate()
				.filter_map(|(i, k)|
					(self.keys & (1 << i) != 0).then_some(k as char))
				.collect()
		}

		fn dbg_path(&self, node_as_char: impl Fn(usize) -> char) -> impl std::fmt::Display {
			use itertools::Itertools as _;
			let mut prev_graph_pos = Some(
				DbgPrevGraphNodes(self.graph_nodes, self.dbg_prev_graph_nodes.clone()));
			#[allow(clippy::needless_collect)]
			let rev_path = std::iter::from_fn(move || {
				let elt = prev_graph_pos.take()?;
				prev_graph_pos = elt.1.map(|rc| (*rc).clone());
				Some(elt.0)
			}).collect::<Vec<_>>();
			rev_path.into_iter()
				.rev()
				.map(|nodes| Self::_dbg_graph_nodes(&nodes, &node_as_char))
				.join(" -> ")
		}
	}

	#[cfg(LOGGING)]
	println!("Grid:\n{input_vault_grid}");

	let graph = vault::Graph::<NUM_COLLECTORS, true>::from(&input_vault_grid);

	#[cfg(LOGGING)]
	println!("Graph (no. keys: {}, no. doors: {}):\n{graph}", graph.num_keys(), graph.num_doors());

	let mut heap = BinaryHeap::new();
	heap.push(State::<NUM_COLLECTORS> {
		graph_nodes: std::array::from_fn(|i| i),
		keys: 0, cost: 0, keys_len: 0,
		#[cfg(LOGGING)]
		dbg_prev_graph_nodes: None,
	});
	let mut found = HashMap::new();

	let mut unlocked_graphs_cache = HashMap::new();

	#[cfg(LOGGING)]
	let (
		mut dbg_nodes_visited,
		mut dbg_optimal_nodes_visited,
		mut dbg_cache_misses,
	) = (0_usize, 0_usize, 0_usize);

	let num_keys = graph.num_keys();
	while let Some(state) = heap.pop() {

		#[cfg(LOGGING)]
		let dbg_nodes_visited = {
			let next = dbg_nodes_visited + 1;
			std::mem::replace(&mut dbg_nodes_visited, next)
		};

		match found.entry((state.graph_nodes, state.keys)) {
			Vacant(entry) => {
				entry.insert(state.cost);
			}
			Occupied(mut entry) => {
				if state.cost >= *entry.get() { continue }
				*entry.get_mut() = state.cost;
			}
		}

		#[cfg(LOGGING)]
		let dbg_optimal_nodes_visited = {
			let next = dbg_optimal_nodes_visited + 1;
			std::mem::replace(&mut dbg_optimal_nodes_visited, next)
		};

		#[cfg(LOGGING)]
		let dbg_state_graph_nodes = state.dbg_graph_nodes(|n| graph.node_as_char(n));

		#[cfg(LOGGING)]
		println!("{dbg_nodes_visited} ({dbg_optimal_nodes_visited}): {} & {} @ {}",
			dbg_state_graph_nodes, state.dbg_keys(), state.cost);

		if state.keys_len == num_keys {
			#[cfg(LOGGING)]
			println!("{dbg_nodes_visited} ({dbg_optimal_nodes_visited}): Found vault path \
				(cost: {}, cache misses: {dbg_cache_misses}):\n{}\nPath: {}",
					state.cost, input_vault_grid, state.dbg_path(|n| graph.node_as_char(n)));
			return state.cost
		}

		let unlocked_graph: &_ = unlocked_graphs_cache
			.entry(state.keys)
			.or_insert_with(|| {
				let unlocked_graph = graph.unlocked(state.keys);
				#[cfg(LOGGING)]
				{
					dbg_cache_misses += 1;
					println!("{dbg_nodes_visited} ({dbg_optimal_nodes_visited}): Unlocked graph \
						(keys: {}, cache misses: {dbg_cache_misses}):\n{unlocked_graph}",
							state.dbg_keys());
				}
				#[allow(clippy::let_and_return)]
				unlocked_graph
			});

		#[cfg(LOGGING)]
		let dbg_prev_graph_poss =
			Rc::new(DbgPrevGraphNodes(state.graph_nodes, state.dbg_prev_graph_nodes));

		for (k, &node) in state.graph_nodes.iter().enumerate() {
			for (node, key, cost) in unlocked_graph.keys_from(node) {
				#[cfg(LOGGING)]
				println!("{dbg_nodes_visited}: {} -> {} (+{})",
					dbg_state_graph_nodes, graph.node_as_char(node), cost);

				heap.push(State {
					graph_nodes: { let mut nodes = state.graph_nodes; nodes[k] = node; nodes },
					keys: state.keys | key,
					cost: state.cost + cost,
					keys_len: state.keys_len + usize::from(key != 0 && state.keys & key == 0),
					#[cfg(LOGGING)]
					dbg_prev_graph_nodes: Some(dbg_prev_graph_poss.clone()),
				})
			}
		}
	}

	panic!("Could not find path between all keys")
}

pub(crate) fn part1() -> usize {
	part1and2_impl::<1>(input_vault())
}


fn part2_impl(mut input_vault_grid: vault::Grid<Ship, 1>) -> usize {
	use vault::{Space::*, Grid};
	let Ship(ship) = input_vault_grid.collectors;
	input_vault_grid.spaces[ship - input_vault_grid.width] = Wall;
	input_vault_grid.spaces[ship - 1] = Wall;
	input_vault_grid.spaces[ship] = Wall;
	input_vault_grid.spaces[ship + 1] = Wall;
	input_vault_grid.spaces[ship + input_vault_grid.width] = Wall;
	part1and2_impl::<4>(Grid {
		spaces: input_vault_grid.spaces,
		width: input_vault_grid.width,
		collectors: Robots([
			ship - input_vault_grid.width - 1,
			ship - input_vault_grid.width + 1,
			ship + input_vault_grid.width - 1,
			ship + input_vault_grid.width + 1,
		]),
	})
}

pub(crate) fn part2() -> usize {
	part2_impl(input_vault())
}


mod parsing {
	use std::str::FromStr;
	use super::{vault::{OpenSpaceItem as VaultItem, Space as VaultSpace, Grid}, Ship};

	#[derive(Debug)]
	pub(super) enum DuplicateKind {
		Door(char),
		Key(char),
		Ship
	}

	#[allow(dead_code)]
	#[derive(Debug)]
	pub(super) enum VaultError {
		Format { line: usize, width: Option<usize>, len: usize },
		Space { line: usize, column: usize, found: char },
		Duplicate { line: usize, column: usize, prev_line: usize, prev_column: usize, kind: DuplicateKind },
		UnmatchedDoor(char),
		NoKeysOrDoors,
		NoShip,
	}

	impl FromStr for Grid<Ship, 1> {
		type Err = VaultError;
		fn from_str(s: &str) -> Result<Self, Self::Err> {
			use {std::collections::HashMap, VaultError::*};

			let mut spaces = Vec::with_capacity(s.len());
			let mut width = None;
			let mut keys = HashMap::new();
			let mut doors = HashMap::new();
			let mut ship = None;
			for (l, line) in s.lines().enumerate() {

				let len = line.len();
				if len == 0 || len != *width.get_or_insert(len) {
					return Err(Format { line: l + 1, width, len });
				}

				for (c, chr) in line.chars().enumerate() {
					use {VaultSpace::*, VaultItem::*, DuplicateKind as Dup};
					macro_rules! duplicate { ( $prev_pos:expr, $kind:expr ) => { {
						let prev_pos = $prev_pos;
						let (prev_line, prev_column) = (prev_pos / len + 1, prev_pos % len + 1);
						Err(Duplicate { line: l + 1, column: c + 1, prev_line, prev_column, kind: $kind })
					} } }
					let pos = l * len + c;
					spaces.push(match chr {
						'.' => Open(None),
						'#' => Wall,
						'A'..='Z' => if let Some(prev_pos) = doors.insert(chr, pos) {
							return duplicate!(prev_pos, Dup::Door(chr))
						} else {
							Open(Some(Door(1 << (chr as u8 - b'A'))))
						}
						'a'..='z' => if let Some(prev_pos) = keys.insert(chr, pos) {
							return duplicate!(prev_pos, Dup::Key(chr))
						} else {
							Open(Some(Key(1 << (chr as u8 - b'a'))))
						}
						'@' => if let Some(prev_pos) = ship.replace(pos) {
							return duplicate!(prev_pos, Dup::Ship)
						} else {
							Open(None)
						}
						found => return Err(Space { line: l + 1, column: c + 1, found })
					})
				}
			}

			let width = width.ok_or(Format { line: 1, width: None, len: 0 })?;
			let ship = ship.ok_or(NoShip)?;

			for (chr, _) in doors {
				if !keys.contains_key(&chr.to_ascii_lowercase()) {
					return Err(UnmatchedDoor(chr))
				}
			}

			if keys.is_empty() { return Err(NoKeysOrDoors) }

			Ok(Grid { spaces, width, collectors: Ship(ship) })
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn part1() {
		const INPUTS: [&str; 5] = [
			indoc::indoc! { "
				#########
				#b.A.@.a#
				#########
			" },
			indoc::indoc! { "
				########################
				#f.D.E.e.C.b.A.@.a.B.c.#
				######################.#
				#d.....................#
				########################
			" },
			indoc::indoc! { "
				########################
				#...............b.C.D.f#
				#.######################
				#.....@.a.B.c.d.A.e.F.g#
				########################
			" },
			indoc::indoc! { "
				#################
				#i.G..c...e..H.p#
				########.########
				#j.A..b...f..D.o#
				########@########
				#k.E..a...g..B.n#
				########.########
				#l.F..d...h..C.m#
				#################
			" },
			indoc::indoc! { "
				########################
				#@..............ac.GI.b#
				###d#e#f################
				###A#B#C################
				###g#h#i################
				########################
			" },
		];
		assert_eq!(part1and2_impl::<1>(input_vault_for_str(INPUTS[0])), 8);
		assert_eq!(part1and2_impl::<1>(input_vault_for_str(INPUTS[1])), 86);
		assert_eq!(part1and2_impl::<1>(input_vault_for_str(INPUTS[2])), 132);
		assert_eq!(part1and2_impl::<1>(input_vault_for_str(INPUTS[3])), 136);
		assert_eq!(part1and2_impl::<1>(input_vault_for_str(INPUTS[4])), 81);
		assert_eq!(super::part1(), 3512);
	}

	#[test]
	fn part2() {
		const INPUTS: [&str; 3] = [
			indoc::indoc! { "
				#######
				#a.#Cd#
				##...##
				##.@.##
				##...##
				#cB#Ab#
				#######
			" },
			indoc::indoc! { "
				###############
				#d.ABC.#.....a#
				######...######
				######.@.######
				######...######
				#b.....#.....c#
				###############
			" },
			indoc::indoc! { "
				#############
				#DcBa.#.GhKl#
				#.###...#I###
				#e#d#.@.#j#k#
				###C#...###J#
				#fEbA.#.FgHi#
				#############
			" },
		];
		assert_eq!(part2_impl(input_vault_for_str(INPUTS[0])), 8);
		assert_eq!(part2_impl(input_vault_for_str(INPUTS[1])), 24);
		assert_eq!(part2_impl(input_vault_for_str(INPUTS[2])), 32);
		assert_eq!(super::part2(), 1514);
	}
}
