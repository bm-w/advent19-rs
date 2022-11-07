// Copyright (c) 2022 Bastiaan Marinus van de Weerd

use crate::day05::{parsing::from_str as input_program_from_str, ProgramState, Program};


trait DroneProgram<'a>: Program<'a, i64> {
	fn execute(&self, pos: [usize; 2]) -> Result<bool, String> {
		let mut program = self.clone();
		let mut program_state = ProgramState::new(true);
		let input = [pos[0] as i64, pos[1] as i64].into_iter();

		fn exactly_one_err(got: impl AsRef<str>) -> String {
			format!("Expected exactly one output, got {}", got.as_ref())
		}

		let pulled = match program.safe_output(&mut program_state, input)? {
			Some(0) => false,
			Some(1) => true,
			Some(invalid) => return Err(format!("Expected output 0 or 1, got {invalid}")),
			None => return Err(exactly_one_err("none")),
		};

		let mut took_more_input = false;
		let input = std::iter::from_fn(|| { took_more_input = true; None });
		if let Some(output) = program.safe_output(&mut program_state, input)? {
			return Err(exactly_one_err(format!("two ({} and {output})",
				if pulled { '1' } else { '0' })))
		}
		if took_more_input {
			return Err("Expected program to only take 2 inputs".to_owned())
		}

		Ok(pulled)
	}
}

impl<'a, T> DroneProgram<'a> for T where T: Program<'a, i64> {}


pub(crate) fn part1() -> usize {
	use itertools::iproduct;

	let input_program = input_program_from_str::<i64>(include_str!("day19.txt"));
	let mut dbg_affected = [false; 50 * 50];
	let mut num_affected = 0_usize;
	for (x, y) in iproduct!(0..50, 0..50) {
		let pulled = input_program.execute([x, y]).unwrap();
		if pulled { num_affected += 1; dbg_affected[y * 50 + x] = true }
	}

	#[cfg(LOGGING)]
	println!("Affected (no.: {num_affected}):\n{}", {
		let mut b = vec![b'.'; 50 * 50 + 49];
		for y in 0..50 {
			for x in 0..50 { b[y * 51 + x] = if dbg_affected[y * 50 + x] { b'#' } else { b'.' } }
			if y < 49 { b[(y + 1) * 51 - 1] = b'\n'; }
		}
		unsafe { String::from_utf8_unchecked(b) }
	});

	num_affected
}


// FIXME(bm-w): Does not work if the lower edge of the beam follows a slope above x = y
pub(crate) fn part2() -> usize {

	let input_program = input_program_from_str::<i64>(include_str!("day19.txt"));

	// Tracing circles with radius `r` using Bresenham’s algorithm
	let [mut x, mut y] = (1..).find_map(|r| {
		let [mut x, mut y] = [0, r];
		let mut d = 3 - 2 * r as i32;

		while y >= x {
			x += 1;
			if d > 0 {
				y -= 1;
				d += 4 * (x as i32 - y as i32) + 10;
			} else {
				d += 4 * x as i32 + 6;
			}

			if input_program.execute([x, y]).unwrap() {
				return Some([x, y])
			}
		}

		None
	}).unwrap();

	assert!(y > x);

	#[cfg(LOGGING)]
	let mut dbg_trace = {
		let mut map = std::collections::HashMap::new();
		map.insert([x, y], true);
		map
	};

	let mut pulled = true;
	loop {
		y += 1;
		if !pulled { x += 1 }

		pulled = input_program.execute([x, y]).unwrap();

		#[cfg(LOGGING)]
		dbg_trace.insert([x, y], pulled);

		if y > 100 {
			if !pulled {
				x += 1;
				pulled = true;

				#[cfg(LOGGING)]
				dbg_trace.insert([x, y], true);
			}

			if input_program.execute([x + 99, y - 99]).unwrap() {
				break
			}
		}
	}

	#[cfg(LOGGING)]
	println!("Trace & ship (x,y: {x},{y}):\n{}", {
		let s = x + 104;
		let mut b = vec![b' '; s * y - 1];
		for y in 0..y {
			if y > 0 { b[y * s - 1] = b'\n'; }
			for x in 0..x { b[y * s + x] = match dbg_trace.get(&[x, y]) {
				Some(true) => b'#',
				Some(false) => b'.',
				None => b' ',
			} }
		}
		for (x, y) in itertools::iproduct!(x + 96..x + 103, y - 102..y-95) {
			let pulled = input_program.execute([x, y]).unwrap();
			b[y * s + x] = if pulled { b'#'} else { b'.' }
		}
		for y in (y - 99..y).rev() { b[y * s + x] = b'O' }
		for x in (x + 1..=x + 99).rev() { b[(y - 99) * s + x] = b'O' }
		unsafe { String::from_utf8_unchecked(b) }
	});

	x * 10_000 + y - 99
}


#[test]
fn tests() {
	assert_eq!(part1(), 213);
	assert_eq!(part2(), 7830987);
}
