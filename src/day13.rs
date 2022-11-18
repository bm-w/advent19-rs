// Copyright (c) 2022 Bastiaan Marinus van de Weerd

use crate::day05::{parsing::from_str as input_program_from_str, Program};


enum TileId {
	Empty = 0,
	Wall = 1,
	Block = 2,
	Paddle = 3,
	Ball = 4,
}

impl TryFrom<i64> for TileId {
	type Error = i64;
	fn try_from(value: i64) -> Result<Self, Self::Error> {
		match value {
			0 => Ok(TileId::Empty),
			1 => Ok(TileId::Wall),
			2 => Ok(TileId::Block),
			3 => Ok(TileId::Paddle),
			4 => Ok(TileId::Ball),
			invalid => Err(invalid),
		}
	}
}

#[cfg(test)]
impl TileId {
	fn as_char(&self) -> char {
		use TileId::*;
		match self {
			Empty => ' ',
			Wall => '#',
			Block => '*',
			Paddle => '=',
			Ball => 'o',
		}
	}
}


enum Output {
	Tile { pos: [usize; 2], id: TileId },
	Score(usize),
}

use std::collections::HashMap;

#[derive(Default)]
struct GameState {
	score: Option<usize>,
	#[cfg(test)]
	width: Option<usize>,
	grid: HashMap<[usize; 2], TileId>,
}

impl GameState {

	#[cfg(test)]
	fn height(&self, width: usize) -> usize {
		self.grid.len() / width
	}

	#[cfg(test)]
	fn size(&mut self) -> [usize; 2] {
		if let Some(width) = self.width { return [width, self.height(width)] }
		self.width = self.grid.keys().fold(None, |w, [x, _]| Some(w.unwrap_or(0).max(*x + 1)));
		self.width.map(|w| [w, self.height(w)]).unwrap_or([0; 2])
	}

	/// # Panics
	/// When `self` does not contain any `Output::Tile` with `TileId::Paddle` or `TileId::Ball`.
	fn paddle_and_ball(&self) -> [[usize; 2]; 2] {
		self.grid.iter()
			.scan([None, None], |pb, (pos, id)| {
				match id {
					TileId::Paddle => pb[0] = Some(*pos),
					TileId::Ball => pb[1] = Some(*pos),
					_ => (),
				}
				Some(*pb)
			})
			.find_map(|pb| match pb {
				[Some(p), Some(b)] => Some([p, b]),
				_ => None,
			})
			.unwrap()
	}

	/// # Panics
	/// When writing the UTF-8 representation into `buf` fails for some reason.
	#[cfg(test)]
	fn write_utf8(&self, buf: &mut [u8], size: [usize; 2]) -> usize {
		use std::io::{Cursor, Write};

		let mut cursor = Cursor::new(buf);
		write!(cursor, "Score: ").unwrap();
		if let Some(score) = self.score { writeln!(cursor, "{score}") }
		else { writeln!(cursor, "N/A") }
			.unwrap();
		let score_offset = cursor.position() as usize;
		let buf = &mut cursor.into_inner()[score_offset..];

		buf.fill(b' ');
		let stride = size[0] + 1;
		for (pos, id) in &self.grid {
			buf[pos[0] + pos[1] * stride] = id.as_char() as u8
		}
		for y in 1..size[1] { buf[stride * y - 1] = b'\n' }

		score_offset + stride * size[1] - 1
	}
}


enum Input { Left = -1, Neutral = 0, Right = 1 }

const INTERACT_NOP: Option<fn() -> Input> = None;


trait Game<'a>: Program<'a, i64> {
	fn run<'b, F>(&'b mut self, mut input: Option<F>) -> Box<dyn Iterator<Item = Output> + 'b>
	where 'a: 'b, F: FnMut() -> Input + 'b {
		use {std::iter::from_fn, crate::day05::Int::Num};

		macro_rules! panic_expecting_3_outputs { ( $found:literal) => {
			panic!("Expecting 3 outputs, but found {}", $found)
		} }

		if input.is_some() { self.as_mut()[0] = Num(2) }

		let mut outputs = self.execute_ext(
			true,
			from_fn(move || input.as_mut().map(|f| f() as i64)),
		);

		Box::new(from_fn(move ||  {
			let outputs = match (outputs.next(), outputs.next(), outputs.next()) {
				(Some(o0), Some(o1), Some(o2)) => [o0, o1, o2],
				(Some(_), Some(_), _) => panic_expecting_3_outputs!(2),
				(Some(_), _, _) => panic_expecting_3_outputs!(1),
				(None, None, None) => return None,
				_ => unreachable!(),
			};

			use Output::*;
			Some(match outputs {
				[-1, 0, score] if score >= 0 => Score(score as usize),
				[-1, 0, neg_score] => panic!("Unexpected negative score {neg_score}!"),
				[x, y, tile_id] => match (
					usize::try_from(x),
					usize::try_from(y),
					TileId::try_from(tile_id)
				) {
					(Ok(x), Ok(y), Ok(tile_id)) => Tile { pos: [x, y], id: tile_id },
					(Err(x), _, _) => panic!("Unexpected invalid X; source: {x:?}"),
					(_, Err(y), _) => panic!("Unexpected invalid Y; source: {y:?}"),
					(_, _, Err(tid)) => panic!("Unexpected tile ID {tid}"),
				}
			})
		}))
	}

	fn play(&mut self) -> usize {
		use std::cell::RefCell;

		let game_state = RefCell::new(GameState::default());
		let input = {
			let game_state = &game_state;
			let mut prev_ball_x = None;

			#[cfg(test)]
			let (mut dbg_i, mut dbg_prev_score, mut dbg_repr) = (
				0,
				game_state.borrow_mut().score,
				String::new()
			);

			move || {
				#[cfg_attr(not(test), allow(unused_mut))]
				let mut game_state = game_state.borrow_mut();

				#[cfg(test)]
				{
					if dbg_i % 1000 == 0 {
						let prev_size = game_state.width.map(|w| [w, game_state.height(w)]);
						let prev_score = std::mem::replace(&mut dbg_prev_score, game_state.score);
						let size = game_state.size();
						if Some(size) != prev_size || game_state.score != prev_score {
							let max_len = (size[0] + 1) * (size[1] + 1);
							// SAFETY: Only adding valid UTF-8 characters, and never truncating.
							unsafe { dbg_repr.as_mut_vec() }.resize(max_len, b' ');
						}
						// SAFETY: `GameState::write_utf8` only writes valid UTF-8 characters,
						// and will leave a valid character boundary at `len` for truncation.
						let len = game_state.write_utf8(unsafe { dbg_repr.as_bytes_mut() }, size);
						dbg_repr.truncate(len);
						println!("({dbg_i}) {dbg_repr}");
					}
					dbg_i += 1;
				}

				let [paddle_pos, ball_pos] = game_state.paddle_and_ball();

				let Some(last_ball_x) = prev_ball_x.replace(ball_pos[0]) else { return Input::Neutral };
				let ball_vel_x = ball_pos[0] as isize - last_ball_x as isize;
				let pred_ball_x = ball_pos[0] as isize + ((paddle_pos[1] - ball_pos[1]) as isize - 1) * ball_vel_x;

				match [paddle_pos[0] as isize, pred_ball_x] {
					[p, b] if p > b => Input::Left,
					[p, b] if p < b => Input::Right,
					_ => Input::Neutral,
				}
			}
		};

		for output in self.run(Some(input)) {
			match output {
				Output::Tile { pos, id } => { game_state.borrow_mut().grid.insert(pos, id); },
				Output::Score(score) => game_state.borrow_mut().score = Some(score),
			}
		}

		game_state.into_inner().score.unwrap_or(0)
	}

	// TODO(bm-w): Return `impl Iterator<…>` once Rust allows it from trait methods
	fn idle<'b>(&'b mut self) -> Box<dyn Iterator<Item = Output> + 'b> where 'a: 'b {
		self.run(INTERACT_NOP)
	}
}

impl<'a, T: Program<'a>> Game<'a> for T {}


fn input_game() -> impl Game<'static> {
	input_program_from_str::<i64>(include_str!("day13.txt"))
}


pub(crate) fn part1() -> usize {
	let mut game = input_game();
	game.idle().filter(|o| matches!(o, Output::Tile { id: TileId::Block, .. })).count()
}


pub(crate) fn part2() -> usize {
	let mut game = input_game();
	game.play()
}


#[test]
fn tests() {
	assert_eq!(part1(), 432);
	assert_eq!(part2(), 22225);
}
