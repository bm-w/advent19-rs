// Copyright (c) 2022 Bastiaan Marinus van de Weerd

mod util;
util::mod_days![01, 02, 03];

fn main() {
	println!("Day 1; part 1: {}, part 2: {}", day01::part1(), day01::part2());
	println!("Day 2; part 1: {}, part 2: {}", day02::part1(), day02::part2());
	println!("Day 3; part 1: {}, part 2: {}", day03::part1(), day03::part2());
}
