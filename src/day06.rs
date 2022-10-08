// Copyright (c) 2022 Bastiaan Marinus van de Weerd

use std::collections::{HashMap, HashSet};


const COM_OBJECT: &str = "COM";
const YOU_OBJECT: &str = "YOU";
const SANTA_OBJECT: &str = "SAN";

/// Target as key, `HashSet` of orbiters as value.
type TargetOrbitersMap<'a> = HashMap<&'a str, HashSet<&'a str>>;
/// Orbiter as key, target as value.
type OrbiterTargetMap<'a> = HashMap<&'a str, &'a str>;


fn part1_impl(s: &str) -> usize {
	let input_map = parsing::try_target_orbiters_map_from_str(s).unwrap();

	let mut total_orbits = 0;
	let mut queue = std::collections::VecDeque::new();
	queue.push_back((COM_OBJECT, 0));
	while let Some((object, orbits)) = queue.pop_front() {
		total_orbits += orbits;
		for orbiter in input_map.get(object).into_iter().flatten() {
			queue.push_back((orbiter, orbits + 1));
		}
	}
	total_orbits
}

pub(crate) fn part1() -> usize {
	part1_impl(include_str!("day06.txt"))
}


fn part2_impl(s: &str) -> usize {
	use std::collections::hash_map::Entry;

	let input_map = parsing::try_orbiter_target_map_from_str(s).unwrap();

	let mut visited = HashMap::new();
	let mut you = (YOU_OBJECT, 0usize);
	let mut santa = (SANTA_OBJECT, 0usize);
	loop {
		macro_rules! visit { ( $who:ident ) => {
			if let Some(&target) = input_map.get($who.0) {
				$who = (target, $who.1 + 1);
				match visited.entry(target) {
					Entry::Vacant(entry) => entry.insert($who.1),
					Entry::Occupied(entry) => {
						let other_orbits = *entry.get();
						return other_orbits + $who.1 - 2;
					},
				};
				true
			} else {
				false
			}
		} }
		if !visit!(you) && !visit!(santa) {
			panic!("No orbital transfers path between you and Santa!")
		}
	}
}

pub(crate) fn part2() -> usize {
	part2_impl(include_str!("day06.txt"))
}


mod parsing {
	use super::{COM_OBJECT, TargetOrbitersMap, OrbiterTargetMap};

	struct MapEntry<'a> { target: &'a str, orbiter: &'a str }

	#[derive(Debug)]
	#[allow(dead_code)]
	pub(super) enum MapEntryError<'a> {
		Format,
		Target { found: &'a str, orbiter: &'a str },
		Orbiter(&'a str),
	}

	impl<'a> TryFrom<&'a str> for MapEntry<'a> {
		type Error = MapEntryError<'a>;
		fn try_from(s: &'a str) -> Result<Self, Self::Error> {
			let (target, orbiter) = s.split_once(')')
				.ok_or(MapEntryError::Format)?;
			fn valid_object(s: &str) -> bool {
				s.chars().all(|c| c.is_ascii_uppercase() || c.is_ascii_digit())
			}
			if !valid_object(target) { return Err(MapEntryError::Target { found: target, orbiter }) }
			if !valid_object(orbiter) { return Err(MapEntryError::Orbiter(orbiter)) }
			Ok(MapEntry { target, orbiter })
		}
	}

	#[derive(Debug)]
	#[allow(dead_code)]
	pub(super) enum MapError<'a> { 
		Empty,
		Entry { line: usize, source: MapEntryError<'a> },
		Duplicate { line: usize, orbiter: &'a str },
		MissingCom,
	}

	fn enumerate_map_entries_from_str(s: &str) -> impl Iterator<Item = Result<(usize, MapEntry), MapError>> {
		s.lines()
			.enumerate()
			.map(|(l, line)| MapEntry::try_from(line)
				.map_err(move |e| MapError::Entry { line: l + 1, source: e })
				.map(|entry| (l, entry)))
	}

	pub(super) fn try_target_orbiters_map_from_str(s: &str) -> Result<TargetOrbitersMap, MapError> {
		use std::collections::HashSet;
		if s.is_empty() { return Err(MapError::Empty) }
		let map = enumerate_map_entries_from_str(s).try_fold((
			TargetOrbitersMap::new(),
			HashSet::new(),
		), |(mut map, mut seen_orbiters), res| {
			let (l, MapEntry { target, orbiter }) = res?;
			if !seen_orbiters.insert(orbiter) { return Err(MapError::Duplicate { line: l + 1, orbiter }) }
			map.entry(target).or_default().insert(orbiter);
			Ok((map, seen_orbiters))
		})?.0;
		if !map.contains_key(COM_OBJECT) { return Err(MapError::MissingCom) }
		Ok(map)
	}

	pub(super) fn try_orbiter_target_map_from_str(s: &str) -> Result<OrbiterTargetMap, MapError> {
		if s.is_empty() { return Err(MapError::Empty) }
		let (map, found_com) = enumerate_map_entries_from_str(s).try_fold((
			OrbiterTargetMap::new(),
			false
		), |(mut map, found_com), res| {
			let (l, MapEntry { target, orbiter }) = res?;
			if map.insert(orbiter, target).is_some() {
				return Err(MapError::Duplicate { line: l + 1, orbiter })
			}
			Ok((map, found_com || target == COM_OBJECT))
		})?;
		if !found_com { return Err(MapError::MissingCom) }
		Ok(map)
	}
}


#[cfg(test)]
mod tests {
	use super::*;

	const INPUT: &str = indoc::indoc! { "
		COM)B
		B)C
		C)D
		D)E
		E)F
		B)G
		G)H
		D)I
		E)J
		J)K
		K)L
	" };

	#[test]
	fn tests() {
		assert_eq!(part1_impl(INPUT), 42);
		assert_eq!(part1(), 200001);
		assert_eq!(part2_impl(&format!("{}\nK){YOU_OBJECT}\nI){SANTA_OBJECT}", INPUT.trim_end())), 4);
		assert_eq!(part2(), 379);
	}
}
