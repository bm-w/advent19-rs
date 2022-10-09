// Copyright (c) 2022 Bastiaan Marinus van de Weerd

mod util;
util::mod_days![01, 02, 03, 04, 05, 06, 07];

fn main() {
	println!("Day 1; part 1: {}, part 2: {}", day01::part1(), day01::part2());
	println!("Day 2; part 1: {}, part 2: {}", day02::part1(), day02::part2());
	println!("Day 3; part 1: {}, part 2: {}", day03::part1(), day03::part2());
	println!("Day 4; part 1: {}, part 2: {}", day04::part1(), day04::part2());
	println!("Day 5; part 1: {}, part 2: {}", day05::part1(), day05::part2());
	println!("Day 6; part 1: {}, part 2: {}", day06::part1(), day06::part2());
	println!("Day 7; part 1: {}, part 2: {}", day07::part1(), day07::part2());
}
