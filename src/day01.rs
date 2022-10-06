// Copyright (c) 2022 Bastiaan Marinus van de Weerd


fn mass_fuel(mass: u64) -> u64 {
	mass / 3 - 2
}

fn module_total_fuel(module_mass: u64) -> u64 {
	let mut total = 0;
	let mut fuel = mass_fuel(module_mass);
	loop {
		total += fuel;
		if fuel <= 6 { break }
		fuel = mass_fuel(fuel);
	}
	total
}

fn sum_fuel(fuel_per_module: fn(u64) -> u64) -> u64 {

	use std::num::ParseIntError;

	#[allow(dead_code)]
	#[derive(Debug)]
	struct ParseModuleMassesError { line: usize, source: ParseIntError }

	include_str!("day01.txt")
		.lines()
		.enumerate()
		.map(|(l, line)| line.parse()
			.map(fuel_per_module)
			.map_err(|e| ParseModuleMassesError { line: l + 1, source: e }))
		.try_fold(0, |acc, fuel| fuel.map(|f| acc + f))
		.unwrap()
}


pub(crate) fn part1() -> u64 {
	sum_fuel(mass_fuel)
}


pub(crate) fn part2() -> u64 {
	sum_fuel(module_total_fuel)
}


#[test]
fn tests() {
	assert_eq!(part1(), 3457681);
	assert_eq!(mass_fuel(6), 0);
	assert_eq!(module_total_fuel(14), 2);
	assert_eq!(module_total_fuel(1969), 966);
	assert_eq!(module_total_fuel(100756), 50346);
	assert_eq!(part2(), 5183653);
}
