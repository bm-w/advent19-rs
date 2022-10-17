// Copyright (c) 2022 Bastiaan Marinus van de Weerd

use crate::day05::{self, parsing::from_str as input_program_from_str, ProgramState};


fn part1_impl<'a>(input_program: impl day05::Program<'a>) -> i64 {
	use {std::iter::once, itertools::{Either, Itertools as _}};

	let mut input_programs = vec![input_program; 5];
	let mut highest_output = i64::MIN;
	for phase_settings in (0..=4).permutations(5) {
		let mut input = Either::Left(once(0));
		for (input_program, phase_setting) in input_programs.iter_mut()
				.zip(phase_settings.into_iter()) {
			input = Either::Right(input_program.execute(once(phase_setting).chain(input)));
		}
		highest_output = highest_output.max(input.exactly_one().ok().unwrap());
	}
	highest_output
}

pub(crate) fn part1() -> i64 {
	part1_impl(input_program_from_str(include_str!("day07.txt")))
}


/// When passing `phase_setttings: Some(…)`, the the output for those specific phase
/// settings is returned. When passing `None`, all combinations of phase settings are
/// tried and the highest output is returned.
/// The `phase_settings` parameter exists to support some tests for which specific
/// combinations are given; trying some other combinations with those test programs
/// results in infinite loops.
fn part2_impl<'a>(input_program: impl day05::Program<'a>, phase_settings: Option<[i64; 5]>) -> i64 {
	use std::{array::from_fn as array_from_fn, iter::once as iter_once};
	use itertools::{Either, Itertools as _};

	let mut input_programs = vec![input_program; 5];
	let mut highest_output = i64::MIN;

	let phase_settings = if let Some(phase_settings) = phase_settings {
		Either::Left(iter_once(Vec::from(phase_settings)))
	} else {
		Either::Right((5i64..=9).permutations(5))
	};

	'phase_settings: for phase_settings in phase_settings {
		let mut program_states = array_from_fn::<_, 5, _>(|_| ProgramState::new(false));
		let mut phase_settings_ = phase_settings.into_iter().map(Some).collect::<Vec<_>>();
		let mut input = Some(0);
		let mut final_output = None;
		'feedback: loop {
			for ((program, program_state), phase_setting)
					in input_programs.iter_mut().zip(program_states.iter_mut()).zip(phase_settings_.iter_mut()) {
				match program.safe_output(program_state,
						&mut phase_setting.take().into_iter().chain(input.into_iter())) {
					Ok(None) => break 'feedback,
					Ok(Some(output)) => input = Some(output),
					Err(_) => continue 'phase_settings,
				}
			}
			final_output = input;
		}
		let Some(final_output) = final_output else { continue };
		highest_output = highest_output.max(final_output);
	}
	highest_output
}

pub(crate) fn part2() -> i64 {
	part2_impl(input_program_from_str(include_str!("day07.txt")), None)
}


#[test]
fn tests() {
	const INPUTS: ([&str; 3], [&str; 2]) = (
		[
			"3,15,3,16,1002,16,10,16,1,16,15,15,4,15,99,0,0",
			"3,23,3,24,1002,24,10,24,1002,23,-1,23,101,5,23,23,1,24,23,23,4,23,99,0,0",
			"3,31,3,32,1002,32,10,32,1001,31,-2,31,1007,31,0,33,1002,33,7,33,1,33,31,31,1,32,31,31,4,31,99,0,0,0",
		],
		[
			"3,26,1001,26,-4,26,3,27,1002,27,2,27,1,27,26,27,4,27,1001,28,-1,28,1005,28,6,99,0,0,5",
			"3,52,1001,52,-5,52,3,53,1,52,56,54,1007,54,5,55,1005,55,26,1001,54,-5,54,1105,1,12,1,53,54,53,1008,54,0,55,1001,55,1,55,2,53,55,53,4,53,1001,56,-1,56,1005,56,6,99,0,0,0,0,10",
		]
	);
	assert_eq!(part1_impl(input_program_from_str(INPUTS.0[0])), 43210);
	assert_eq!(part1_impl(input_program_from_str(INPUTS.0[1])), 54321);
	assert_eq!(part1_impl(input_program_from_str(INPUTS.0[2])), 65210);
	assert_eq!(part1(), 38834);
	assert_eq!(part2_impl(input_program_from_str(INPUTS.1[0]), Some([9, 8, 7, 6, 5])), 139629729);
	assert_eq!(part2_impl(input_program_from_str(INPUTS.1[1]), Some([9, 7, 8, 5, 6])), 18216);
	assert_eq!(part2(), 69113332);
}
