// Copyright (c) 2022 Bastiaan Marinus van de Weerd

mod util;
util::mod_days![01];

fn main() {
	println!("Day 1; part 1: {}, part 2: {}", day01::part1(), day01::part2());
}
