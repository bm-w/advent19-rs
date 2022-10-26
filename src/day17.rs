// Copyright (c) 2022 Bastiaan Marinus van de Weerd

use crate::day05::{parsing::from_str as input_program_from_str, Int, Program, ProgramState};


trait Cameras<'a>: Program<'a, i64> {
	fn output(&mut self) -> (Vec<u8>, usize) {
		use std::iter::{empty, from_fn};

		let mut program_state = ProgramState::new(true);

		let output = from_fn(|| self.safe_output(&mut program_state, empty()).transpose());

		let mut width = 0;
		let mut height = None;
		let mut view = Vec::new();
		for output in output {
			assert!(height.is_none());
			let b = output.unwrap() as u8;
			if b == b'\n' {
				if width == 0 { width = view.len(); }
				else if (view.len() + 1) % (width + 1) == 1 { height = Some(view.len() / (width + 1)) }
			}
			view.push(b);
		}
		assert!(height.is_some());

		(view, width)
	}
}

impl<'a, T> Cameras<'a> for T where T: Program<'a, i64> {}


fn is_robot_on_scaffolding(b: &u8) -> bool { [b'<', b'>', b'^', b'v'].contains(b) }
fn is_scaffolding(b: &u8) -> bool { *b == b'#' || is_robot_on_scaffolding(b) }

fn intersection_positions(view: &[u8], width: usize) -> impl Iterator<Item = usize> + '_ {
	use std::iter::from_fn;
	let mut offset = width + 1;
	let end = view.len() - offset - 2;
	from_fn(move || {
		let next = view[offset..end].iter().enumerate().position(|(i, b)| {
			if !is_scaffolding(b) { return false }
			let i  = i + offset;
			[i - width - 1, i - 1, i + 1, i + width + 1].into_iter().all(|i| is_scaffolding(&view[i]))
		})?;
		offset += next + 1;
		Some(offset - 1)
	})
}

fn is_robot(b: &u8) -> bool { *b == b'X' || is_robot_on_scaffolding(b) }

fn robot_position(view: &[u8]) -> Option<usize> {
	view.iter().position(is_robot)
}


pub(crate) fn part1() -> u64 {
	let (view, width) =
		Cameras::output(&mut input_program_from_str::<i64>(include_str!("day17.txt")));
	intersection_positions(&view, width)
		.map(|i| ((i % (width + 1)) * (i / (width + 1))) as u64)
		.sum()
}


pub(crate) fn part2() -> impl std::fmt::Display {
	let mut program = input_program_from_str::<i64>(include_str!("day17.txt"));
	let (view, width) = Cameras::output(&mut program.clone());

	let robot_pos = robot_position(&view).unwrap();
	let robot_dir = match view[robot_pos] {
		b'<' => -1, b'>' => 1, b'^' => -(width as isize) - 1, b'v' => width as isize + 1,
		b => panic!("Invalid robot direction ('{}')", char::from(b)),
	};

	let intersections = intersection_positions(&view, width).collect::<Vec<_>>();

	// Assuming the scaffolding forms a continuous path
	let mut from_pos = robot_pos;
	let mut nodes = vec![];
	nodes.push(robot_pos);
	#[cfg(test)]
	let mut dbg_edges = vec![];
	let mut to_pos = from_pos;
	let mut step = None;
	macro_rules! is_valid_i { ( $i:expr )
		=> { { let i = $i; i >= 0 && (i as usize) < view.len() } } }
	loop {
		if to_pos == from_pos {
			let i = from_pos as isize;
			let s = width as isize + 1;
			step = [-s, -1, 1, s]
				.into_iter()
				.find(|&s| Some(-s) != step // Don’t go back
					&& is_valid_i!(i + s)
					&& is_scaffolding(&view[(i + s) as usize]))
		}
		let Some(step) = step else { break };

		let pos = to_pos as isize + step;
		let (is_scaffolding, is_intersection) = if !is_valid_i!(pos) {
			(false, false)
		} else if intersections.contains(&(pos as usize)) {
			(true, true)
		} else {
			(is_scaffolding(&view[pos as usize]), false)
		};

		match (is_scaffolding, is_intersection) {
			(true, false) => to_pos = pos as usize,
			(_, true) => {
				to_pos = pos as usize;
				loop {
					nodes.push(to_pos);
					#[cfg(test)]
					dbg_edges.push([from_pos, to_pos]);
					from_pos = to_pos;
					// Guaranteed to be valid
					to_pos = (pos + step) as usize;
					if !intersections.contains(&to_pos) { break }
				}
			}
			(false, _) => {
				nodes.push(to_pos);
				#[cfg(test)]
				dbg_edges.push([from_pos, to_pos]);
				from_pos = to_pos;
			}
		}
	}

	// Returns the signed step size and number of steps
	fn edge_steps(edge: [usize; 2], width: usize) -> Option<(isize, usize)> {
		let s = (width + 1) as isize;
		let d = edge[1] as isize - edge[0] as isize;
		let s = match d {
			d if d <= -s => -s,
			d if d < 0 => -1,
			d if d > s => s,
			_ => 1,
		};
		let n = d / s; 
		(n * s == d).then_some((s, n as usize))
	}

	#[cfg(test)]
	{
		let mut dbg_view = view;
		for (i, &pos) in nodes.iter().enumerate() {
			let i = i % (2 * 26);
			let b = if i < 26 { b'a' } else { b'A' };
			dbg_view[pos] = b + (i as u8 % 26);
			
		}
		for &[from, to] in &dbg_edges {
			let (s, _) = edge_steps([from, to], width).unwrap();
			let b = if s.abs() == 1 { b'-' } else { b'|' };
			let mut p = (from as isize + s) as usize;
			while p != to {
				assert!(dbg_view[p] == b'#');
				dbg_view[p] = b;
				p = (p as isize + s) as usize;
			}
		}

		println!("View ({width} x {}):\n{}",
			dbg_view.len() / (width + 1),
			unsafe { String::from_utf8_unchecked(dbg_view) });
	}

	fn uncompressed_move_commands(path: &[usize], width: usize, init_dir: isize) -> Result<String, String> {
		use std::{io::Write, iter::once};

		let s = width as isize + 1;
		let mut sequence = Vec::with_capacity(2 * path.len());
		let mut push = |dir, step, num| {
			if !sequence.is_empty() { sequence.push(b',') }
			sequence.push(match (dir, step) {
				sd if [(1, -s), (s, 1), (-1, s), (-s, -1)].contains(&sd) => b'L',
				sd if [(-1, -s), (-s, 1), (1, s), (s, -1)].contains(&sd) => b'R',
				_ => {
					let err_dir = |dir, label| match dir {
						d if d == -s => "north".to_owned(),
						d if d == -1 => "west".to_owned(),
						d if d == 1 => "east".to_owned(),
						d if d == s => "south".to_owned(),
						_ => format!("some unknown direction [{label}: {dir}]"),
					};
					return Err(format!(
						"Only right-angle turns are supported (i.e. left / right, not turning 180° around; \
						facing {}, trying to move {})", err_dir(dir, "dir"), err_dir(step, "step")));
				}
			});
			sequence.push(b',');
			write!(&mut sequence, "{num}").unwrap();
			Ok(())
		};
		let mut prev = None;
		for pos in path.iter().map(|p| Some(*p)).chain(once(None)) {
			match (prev.as_mut(), pos) {
				(None, None) => break,
				(None, Some(pos)) =>
					prev = Some((pos, init_dir, None)),
				(Some((prev_pos, _, to @ None)), Some(pos)) => {
					let (step, num) = edge_steps([*prev_pos, pos], width).unwrap();
					*to = Some((pos, step, num));
				}
				(Some((from_pos, from_dir, Some(to))), Some(pos)) => {
					let (to_pos, to_step, to_num) = to;
					if let Some((step, num)) = edge_steps([*from_pos, pos], width) {
						assert_eq!(step, *to_step);
						*to = (pos, step, num);
					} else {
						push(*from_dir, *to_step, *to_num)?;
						let (step, num) = edge_steps([*to_pos, pos], width).unwrap();
						*from_pos = *to_pos;
						*from_dir = *to_step;
						*to = (pos, step, num);
					}
				}
				(Some(&mut (_, prev_dir, Some((_, to_step, to_num)))), None) => {
					push(prev_dir, to_step, to_num)?;
				}
				(Some((_, _, None)), None) => break,
			}
		}

		// SAFETY: Only pushed valid UTF-8 sequences
		Ok(unsafe { String::from_utf8_unchecked(sequence) })
	}

	fn commands(uncompressed_move_commands: &str) -> Option<String> {
		fn find_subcommands<'a>(full: &'a str, prefixes: &[&'a str]) -> Option<(Vec<&'a str>, Vec<usize>)> {
			use std::iter::once;

			let mut limit = 20;
			loop {
				let prefix = full.match_indices(',')
					.take_while(|&(i, _)| i <= limit)
					.last()
					.map(|(i, _)| &full[..i])?;

				let mut rest = &full[prefix.len() + 1..];
				let prefixes = Vec::from_iter(prefixes.iter().copied().chain(once(prefix)));
				let mut sequence = vec![prefixes.len() - 1];
				while let Some((i, prefix)) = prefixes.iter()
						.enumerate()
						.find_map(|(i, &p)| rest.starts_with(p).then_some((i, p))) {
					sequence.push(i);
					rest = &rest[(prefix.len() + 1).min(rest.len())..];
				}

				if rest.is_empty() {
					return Some((prefixes, sequence));
				} else if prefixes.len() < 3 {
					if let Some(tail) = find_subcommands(rest, &prefixes) {
						let (prefixes, tail_sequence) = tail;
						sequence.extend(tail_sequence);
						return Some((prefixes, sequence));
					} else {
						limit = prefix.len() - 1;
						continue
					}
				} else if limit >= 2 {
					limit -= 2;
				} else {
					return None
				}
			}
		}

		let (subcommands, sequence) = find_subcommands(uncompressed_move_commands, &[])?;

		let mut command = String::new();
		for i in sequence {
			if !command.is_empty() { command.push(','); }
			command.push(['A', 'B', 'C'][i]);
		}
		command.push('\n');
		for subcommand in subcommands {
			command.push_str(subcommand);
			command.push('\n');
		} 
		command.push('n'); // No live video; push `'y'` otherwise
		command.push('\n');
		
		Some(command)
	}

	let uncompressed_move_commands = match uncompressed_move_commands(&nodes, width, robot_dir) {
		Ok(uncompressed_move_commands) => uncompressed_move_commands,
		Err(err) => todo!("{err}"),
	};

	program.as_mut()[0] = Int::Num(2);
	program.execute_ext(true, commands(&uncompressed_move_commands).unwrap()
			.bytes()
			.map(|b| b as i64))
		.last().unwrap()
}


#[test]
fn tests() {
	assert_eq!(part1(), 5972);
	assert_eq!(part2().to_string(), "933214");
}
