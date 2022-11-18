// Copyright (c) 2022 Bastiaan Marinus van de Weerd



mod maze {
	pub(super) enum Space {
		Open,
		Wall,
		Portal(u16),
	}

	pub(super) struct Grid {
		pub(super) spaces: Vec<Option<Space>>,
		pub(super) width: usize,
		pub(super) portals: std::collections::HashMap<u16, [usize; 2]>,
		pub(super) start: usize,
		pub(super) finish: usize,
	}

	#[derive(Clone, Copy, PartialEq, Eq, Hash)]
	struct Pos {
		grid: usize,
		level: usize,
	}

	impl Grid {

		fn grid_pos_to_xy(&self, pos: usize) -> [usize; 2] {
			[pos % self.width, pos / self.width]
		}

		fn adjacent_positions(&self, from: usize) -> impl Iterator<Item = usize> + '_ {
			// let len = self.spaces.len() as isize;
			let w = self.width as isize;
			let h = self.spaces.len() as isize / w;
			let [x, y] = self.grid_pos_to_xy(from);
			[[0, -1], [-1, 0], [1, 0], [0, 1]].into_iter()
				.filter_map(move |[dx, dy]| match [x as isize + dx, y as isize + dy] {
					[neg, _] | [_, neg] if neg < 0 => None,
					[exc, _] if exc >= w => None,
					[_, exc] if exc >= h => None,
					[x, y] => Some((y * w + x) as usize)
				})
		}

		fn reachable_positions(&self, from: Pos, recurse: bool) -> impl Iterator<Item = Pos> + '_ {

			macro_rules! is_outer { ( $pos:expr ) => { match self.grid_pos_to_xy($pos) {
				[0, _] | [_, 0] => true,
				[r, _] if r == self.width - 1 => true,
				[_, b] if b == self.spaces.len() / self.width - 1 => true,
				_ => false,
			} } }

			let portal = if let Some(Space::Portal(id)) = self.spaces[from.grid] {
				let [pos0, pos1] = self.portals[&id];
				let outer = recurse && is_outer!(from.grid);
				if recurse && from.level == 0 && outer {
					None
				} else {
					Some(Pos {
						grid: if pos0 == from.grid { pos1 } else { pos0 },
						level: if !recurse { 0 }
							else if outer { from.level - 1 }
							else { from.level + 1 }
					})
				}
			} else {
				None
			};

			use Space::*;
			portal.into_iter()
				.chain(self.adjacent_positions(from.grid)
					.filter(move |&pos| !recurse || if from.level > 0 {
						pos != self.start && pos != self.finish
					} else {
						pos == self.finish || !is_outer!(pos)
					})
					.filter(|&pos| matches!(self.spaces[pos], Some(Open | Portal(_))))
					.map(move |grid| Pos { grid, ..from }))
		}

		pub(super) fn path_steps(&self, recurse: bool) -> usize {
			use std::collections::{HashMap, VecDeque, hash_map::Entry::*};

			let mut queue = VecDeque::new();
			let mut costs = HashMap::new();

			queue.push_front((Pos { grid: self.start, level: 0 }, 0));

			while let Some((from_pos, cost)) = queue.pop_front() {

				if from_pos.grid == self.finish && (!recurse || from_pos.level == 0) {
					return cost
				}

				match costs.entry(from_pos) {
					Vacant(entry) =>
						_ = entry.insert(cost),
					Occupied(mut entry) => {
						if cost >= *entry.get() { continue }
						*entry.get_mut() = cost;
					}
				}

				#[cfg(LOGGING)]
				fn pos_to_xy(pos: usize, w: usize) -> [usize; 2] {
					[pos % w, pos / w]
				}

				#[cfg(LOGGING)]
				println!("{:?}@{}: {cost}", pos_to_xy(from_pos.grid, self.width), from_pos.level);

				for to_pos in self.reachable_positions(from_pos, recurse) {
					#[cfg(LOGGING)]
					println!("{:?}@{} -> {:?}@{}{}",
						pos_to_xy(from_pos.grid, self.width),
						from_pos.level,
						pos_to_xy(to_pos.grid, self.width),
						to_pos.level,
						match [&self.spaces[from_pos.grid], &self.spaces[to_pos.grid]] {
							[
								&Some(Space::Portal(from_id)),
								&Some(Space::Portal(to_id))
							] if from_id == to_id => format!(" ({}{})",
									(((from_id >> 8) & 0xff) as u8) as char,
									((from_id & 0xff) as u8) as char),
							_ => "".to_owned(),
						});
					queue.push_back((to_pos, cost + 1))
				}
			}

			panic!("Unable to find path from start to finish")

		}
	}

}


fn input_maze_grid_from_str(s: &str) -> maze::Grid {
	s.parse().unwrap()
}

fn input_maze_grid() -> maze::Grid {
	input_maze_grid_from_str(include_str!("day20.txt"))
}


fn part1_impl(input_maze_grid: maze::Grid) -> usize {
	input_maze_grid.path_steps(false)
}

pub(crate) fn part1() -> usize {
	part1_impl(input_maze_grid())
}


fn part2_impl(input_maze_grid: maze::Grid) -> usize {
	input_maze_grid.path_steps(true)
}

pub(crate) fn part2() -> usize {
	part2_impl(input_maze_grid())
}


mod parsing {
	use std::str::FromStr;
	use super::maze;

	#[allow(dead_code)]
	#[derive(Debug)]
	pub(super) enum PortalError {
		Incomplete,
		Misplaced,
		Duplicate { prev_line: usize, prev_column: usize },
		Unmatched
	}

	#[allow(dead_code)]
	#[derive(Debug)]
	pub(super) enum FormatError {
		Width { width: Option<usize>, len: usize },
		NonAscii { column: usize, found: char },
		Incomplete { column: usize },
	}

	#[allow(dead_code)]
	#[derive(Debug)]
	pub(super) enum MazeError {
		Format { line: usize, source: FormatError },
		Space { line: usize, column: usize, found: char },
		Portal { line: usize, column: usize, source: PortalError },
		MissingPortal(&'static str), // Portals “AA” & “ZZ”
	}

	impl FromStr for maze::Grid {
		type Err = MazeError;
		fn from_str(s: &str) -> Result<Self, Self::Err> {
			use {std::collections::{HashMap, BTreeSet}, maze::Space::*, MazeError::*};

			enum Geometry {
				I,
				Ii { w: usize },
				Iii { w: usize, tl: usize },
				Iv { w: usize, tl: usize, tr: usize },
				V { w: usize, tl: usize },
				Vi { w: usize, h: usize },
			}

			impl Geometry {
				fn w(&self) -> Option<usize> {
					use Geometry::*;
					match self {
						Ii { w, .. } | Iii { w, .. } | Iv { w, .. }
							| V { w, .. } | Vi { w, .. } => Some(*w),
						_ => None,
					}
				}

				fn with_w(&self, f: impl Fn(usize) -> bool) -> bool {
					self.w().map(f).unwrap_or(false)
				}
			}

			#[derive(Clone, Copy, PartialEq, Eq, Debug)]
			struct PortalPart {
				lc: [usize; 2],
				alt: bool,
				from_lc: [usize; 2],
				maze_lc: [usize; 2],
				id: u8,
			}

			impl Ord for PortalPart {
				fn cmp(&self, other: &Self) -> std::cmp::Ordering {
					self.lc.cmp(&other.lc)
				}
			}

			impl PartialOrd for PortalPart {
				fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
					Some(self.cmp(other))
				}
			}

			fn portal_id(b0: u8, b1: u8) -> u16 {
				let [low, high] = if b0 < b1 { [b0, b1] } else { [b1, b0] };
				high as u16 + ((low as u16) << 8)
			}

			let mut spaces = Vec::with_capacity(s.len());
			let mut portal_parts = BTreeSet::new();
			let mut prematched_portals = HashMap::new();
			let mut portals_lc = HashMap::new();
			let mut geometry = Geometry::I;

			let mut line_len = 0_usize;
			for (l, line) in s.lines().enumerate() {
				line_len = 0_usize;

				for (c, b) in line.bytes().enumerate() {
					line_len += 1;

					if !b.is_ascii() {
						return Err(Format { line: l + 1, source: FormatError::NonAscii {
							column: c + 1, found: line.chars().nth(c).unwrap() } })
					}

					macro_rules! ret_space_err { () => { {
						return Err(Space { line: l + 1, column: c + 1, found: b as char })
					} } }

					macro_rules! check_void { ( $( $inner:block )? ) => {
						'outer: { if l > 1 && c > 1 { use Geometry::*; match geometry {
							I => break 'outer,
							_ if geometry.with_w(|w| c >= w + 2 ) => break 'outer,
							Ii { w } => geometry = Iii { w, tl: c - 2 },
							Iii { tl, .. } | Iv { tl, .. } if c < tl + 2 =>
								ret_space_err!(),
							Iii { .. } => (),
							Iv { w, tr, .. } if c >= w - tr + 2 => ret_space_err!(),
							Iv { .. } => (),
							V { w, .. } => if c != 2 { ret_space_err!() } else {
								geometry = Vi { w, h: l - 2 };
								break 'outer
							}
							Vi { .. } => break 'outer,
						}; $( $inner )? } }
					} }

					macro_rules! check_maze { ( $( $inner:block )? ) => {
						{ if l < 2 || c < 2 {
							ret_space_err!()
						} else { use Geometry::*; match geometry {
							I => ret_space_err!(),
							_ if geometry.with_w(|w| c >= w + 2 ) => ret_space_err!(),
							Ii { .. } => (),
							Iii { tl, .. } | Iv { tl, .. } | V { tl, .. } if c < tl + 2 => (),
							Iii { w, tl, .. } => geometry = Iv { w, tl, tr: w - c + 2 },
							Iv { w, tl, tr } =>
								if c == tl + 2 { geometry = V { w, tl } }
								else if c < w - tr + 2 { ret_space_err!() }
							V { .. } => (),
							Vi { .. } => ret_space_err!(),
						} } }
					} }

					match b {
						b' ' => check_void!({ spaces.push(None) }),
						b'.' => { check_maze!(); spaces.push(Some(Open)) }
						b'#' => { check_maze!(); spaces.push(Some(Wall)) }
						upper if upper.is_ascii_uppercase() => {
							// TODO(bm-w): Detect misplaced portal in top-right corner & bottom-left corners!
							check_void!({ spaces.push(None) });

							// TODO(bm-w): Remove `.copied()` once Rust can end `front` borrow lifetime mid-arm (i.e. Polonius)
							match portal_parts.first().copied() {
								Some(part @ PortalPart { .. }) if part.lc == [l, c] => {
									let id = portal_id(part.id, upper);
									if let Some(other_maze_lc) = prematched_portals.remove(&id) {
										if let Some([prev_lc, _]) = portals_lc
												.insert(id, if other_maze_lc < part.maze_lc {
													[other_maze_lc, part.maze_lc]
												} else {
													[part.maze_lc, other_maze_lc]
												}) {
											return Err(MazeError::Portal { line: l + 1,
												column: c + 1, source: PortalError::Duplicate {
													prev_line: prev_lc[0] + 1,
													prev_column: prev_lc[1] + 1 } })
										}
									} else {
										prematched_portals.insert(id, part.maze_lc);
									}
									assert!(portal_parts.pop_first() == Some(part));
									if part.alt {
										// TODO(bm-w): Remove `.copied()` once Rust can end `front` borrow lifetime mid-arm (i.e. Polonius)
										_ = portal_parts.remove(&portal_parts.iter()
											.find(|p| p.alt && p.from_lc == part.from_lc)
											.copied()
											.unwrap());
									}
								},
								_ => {
									use Geometry::*;
									let (next_lc, maze_lc, alt) = match geometry {
										_ if c == 0 => ([l, c + 1], [l, c + 2], None),
										_ if l == 0 => ([l + 1, c], [l + 2, c], None),
										Vi { h, .. } if l == h + 2 =>
											([l + 1, c], [l - 1, c], None),
										_ if geometry.with_w(|w| c == w + 2) =>
											([l, c + 1], [l, c - 1], None),
										Iii { tl, .. } if c == tl + 2 =>
											// Assuming portals can’t be placed in the corners of the hole
											return Err(MazeError::Portal { line: l + 1,
												column: c + 1, source: PortalError::Misplaced }),
										Iii { .. } =>
											([l + 1, c], [l - 1, c], None),
										Iv { w, tl, tr, .. } =>
											if c == tl + 2 {
												([l, c + 1], [l, c - 1], None)
											} else if c == w - tr {
												([l, c + 1], [l, c + 2],
													Some(([l + 1, c], [l + 2, c])))
											} else {
												([l + 1, c], [l + 2, c], None)
											}
										_ => return Err(MazeError::Portal { line: l + 1,
											column: c + 1, source: PortalError::Incomplete })
									};
									portal_parts.insert(PortalPart { lc: next_lc,
										alt: alt.is_some(), from_lc: [l, c],
										maze_lc, id: upper });
									if let Some((lc, maze_lc)) = alt {
										portal_parts.insert(PortalPart { lc,
											alt: true, from_lc: [l, c],
											maze_lc, id: upper });
									}
								}
							}

							continue
						}
						_ => ret_space_err!(),
					}

					// TODO(bm-w): Remove `.copied()` once Rust can end `front` borrow lifetime mid-arm (i.e. Polonius)
					match portal_parts.first().copied() {
						Some(part) if part.lc == [l, c] => {
							if part.alt {
								assert!(portal_parts.pop_first() == Some(part));
							} else {
								return Err(MazeError::Portal { line: part.from_lc[0] + 1,
									column: part.from_lc[1] + 1, source: PortalError::Incomplete })
							}
						}
						_ => (),
					}
				}

				if !match geometry.w() {
					_ if line_len < 4 => false,
					None => { geometry = Geometry::Ii { w: line_len - 4 }; true }
					Some(w) => line_len - 4 == w,
				} {
					return Err(Format { line: l + 1, source: FormatError::Width {
						width: geometry.w(), len: line_len } })
				}
			}

			let Geometry::Vi { w, h: _h } = geometry else {
				return Err(Format { line: s.lines().count(), source: FormatError::Incomplete {
					column: line_len + 1 } })
			};

			fn space_pos(lc: [usize; 2], w: usize) -> usize {
				(lc[0] - 2) * w + lc[1] - 2
			}

			let start = space_pos(prematched_portals
				.remove(&portal_id(b'A', b'A'))
				.ok_or(MissingPortal("AA"))?, w);

			let end = space_pos(prematched_portals
				.remove(&portal_id(b'Z', b'Z'))
				.ok_or(MissingPortal("ZZ"))?, w);

			if let Some((_, [l, c])) = prematched_portals.into_iter().next() {
				return Err(MazeError::Portal { line: l + 1, column: c + 1,
					source: PortalError::Unmatched })
			}

			let mut portals = HashMap::new();
			for (id, lcs) in portals_lc {
				let poss = [
					(lcs[0][0] - 2) * w + lcs[0][1] - 2,
					(lcs[1][0] - 2) * w + lcs[1][1] - 2,
				];
				if !(matches!(&spaces[poss[0]], Some(Open))) {
					return Err(MazeError::Portal { line: lcs[0][0] + 1,
						column: lcs[0][1] + 1, source: PortalError::Misplaced })
				}
				spaces[poss[0]] = Some(maze::Space::Portal(id));
				if !(matches!(&spaces[poss[1]], Some(Open))) {
					return Err(MazeError::Portal { line: lcs[1][0] + 1,
						column: lcs[1][1] + 1, source: PortalError::Misplaced })
				}
				spaces[poss[1]] = Some(maze::Space::Portal(id));

				portals.insert(id, poss);
			}

			#[cfg(LOGGING)]
			{
				println!("Portals: {portals:?}");
				for y in 0.._h {
					println!("{}", unsafe { String::from_utf8_unchecked(spaces[y * w..(y + 1) * w].iter()
						.map(|s| match s {
							None => b' ',
							Some(Open) => b'.',
							Some(Wall) => b'#',
							Some(maze::Space::Portal(_)) => b'P'
						})
						.collect()) })
				}
			}

			Ok(maze::Grid { spaces, width: w, portals, start, finish: end })
		}
	}
}


#[test]
fn tests() {
	const INPUTS: [&str; 3] = [
		indoc::indoc! { "
			         A           
			         A           
			  #######.#########  
			  #######.........#  
			  #######.#######.#  
			  #######.#######.#  
			  #######.#######.#  
			  #####  B    ###.#  
			BC...##  C    ###.#  
			  ##.##       ###.#  
			  ##...DE  F  ###.#  
			  #####    G  ###.#  
			  #########.#####.#  
			DE..#######...###.#  
			  #.#########.###.#  
			FG..#########.....#  
			  ###########.#####  
			             Z       
			             Z       
		" },
		indoc::indoc! { "
			                   A               
			                   A               
			  #################.#############  
			  #.#...#...................#.#.#  
			  #.#.#.###.###.###.#########.#.#  
			  #.#.#.......#...#.....#.#.#...#  
			  #.#########.###.#####.#.#.###.#  
			  #.............#.#.....#.......#  
			  ###.###########.###.#####.#.#.#  
			  #.....#        A   C    #.#.#.#  
			  #######        S   P    #####.#  
			  #.#...#                 #......VT
			  #.#.#.#                 #.#####  
			  #...#.#               YN....#.#  
			  #.###.#                 #####.#  
			DI....#.#                 #.....#  
			  #####.#                 #.###.#  
			ZZ......#               QG....#..AS
			  ###.###                 #######  
			JO..#.#.#                 #.....#  
			  #.#.#.#                 ###.#.#  
			  #...#..DI             BU....#..LF
			  #####.#                 #.#####  
			YN......#               VT..#....QG
			  #.###.#                 #.###.#  
			  #.#...#                 #.....#  
			  ###.###    J L     J    #.#.###  
			  #.....#    O F     P    #.#...#  
			  #.###.#####.#.#####.#####.###.#  
			  #...#.#.#...#.....#.....#.#...#  
			  #.#####.###.###.#.#.#########.#  
			  #...#.#.....#...#.#.#.#.....#.#  
			  #.###.#####.###.###.#.#.#######  
			  #.#.........#...#.............#  
			  #########.###.###.#############  
			           B   J   C               
			           U   P   P               
		" },
		indoc::indoc! { "
			             Z L X W       C                 
			             Z P Q B       K                 
			  ###########.#.#.#.#######.###############  
			  #...#.......#.#.......#.#.......#.#.#...#  
			  ###.#.#.#.#.#.#.#.###.#.#.#######.#.#.###  
			  #.#...#.#.#...#.#.#...#...#...#.#.......#  
			  #.###.#######.###.###.#.###.###.#.#######  
			  #...#.......#.#...#...#.............#...#  
			  #.#########.#######.#.#######.#######.###  
			  #...#.#    F       R I       Z    #.#.#.#  
			  #.###.#    D       E C       H    #.#.#.#  
			  #.#...#                           #...#.#  
			  #.###.#                           #.###.#  
			  #.#....OA                       WB..#.#..ZH
			  #.###.#                           #.#.#.#  
			CJ......#                           #.....#  
			  #######                           #######  
			  #.#....CK                         #......IC
			  #.###.#                           #.###.#  
			  #.....#                           #...#.#  
			  ###.###                           #.#.#.#  
			XF....#.#                         RF..#.#.#  
			  #####.#                           #######  
			  #......CJ                       NM..#...#  
			  ###.#.#                           #.###.#  
			RE....#.#                           #......RF
			  ###.###        X   X       L      #.#.#.#  
			  #.....#        F   Q       P      #.#.#.#  
			  ###.###########.###.#######.#########.###  
			  #.....#...#.....#.......#...#.....#.#...#  
			  #####.#.###.#######.#######.###.###.#.#.#  
			  #.......#.......#.#.#.#.#...#...#...#.#.#  
			  #####.###.#####.#.#.#.#.###.###.#.###.###  
			  #.......#.....#.#...#...............#...#  
			  #############.#.#.###.###################  
			               A O F   N                     
			               A A D   M                     
		" },
	];
	assert_eq!(part1_impl(input_maze_grid_from_str(INPUTS[0])), 23);
	assert_eq!(part1_impl(input_maze_grid_from_str(INPUTS[1])), 58);
	assert_eq!(part1(), 490);
	assert_eq!(part2_impl(input_maze_grid_from_str(INPUTS[0])), 26);
	assert_eq!(part2_impl(input_maze_grid_from_str(INPUTS[2])), 396);
	assert_eq!(part2(), 5648);
}
