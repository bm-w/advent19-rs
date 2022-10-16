// Copyright (c) 2022 Bastiaan Marinus van de Weerd


const ORE: &str = "ORE";
const FUEL: &str = "FUEL";

type Quantity = std::num::NonZeroUsize;
type Chemical<'a> = &'a str;

struct ReactionInfo<'a> {
	consumes: Vec<(Quantity, Chemical<'a>)>,
	produces: Quantity,
}

struct Reaction<'a>(Chemical<'a>, ReactionInfo<'a>);

use std::collections::HashMap;

use num_integer::Roots;

struct Nanofactory<'a> {
	reactions: HashMap<Chemical<'a>, ReactionInfo<'a>>,
}

impl<'a> FromIterator<Reaction<'a>> for Nanofactory<'a> {
	fn from_iter<T: IntoIterator<Item = Reaction<'a>>>(iter: T) -> Self {
		Self { reactions: HashMap::from_iter(iter.into_iter().map(|r| (r.0, r.1))) }
	}
}

impl<'a> Nanofactory<'a> {
	/// Returns the quantity of ore consumed to produce `quantity` fuel.
	fn produce_fuel(&self, quantity: usize) -> usize {
		use std::collections::{VecDeque, hash_map::Entry::Occupied};

		if quantity == 0 { return 0 }

		let mut leftovers = HashMap::new();
	
		let mut queue = VecDeque::new();
		let mut ore_req = 0;
		queue.push_back((quantity, FUEL));

		while let Some((mut req, chemical)) = queue.pop_front() {

			let mut leftover = leftovers.entry(chemical);
			if let Occupied(left_over) = &mut leftover {
				let left_over = left_over.get_mut();
				if *left_over >= req {
					*left_over -= req;
					continue;
				} else {
					req -= *left_over;
					*left_over = 0;
				}
			}

			let ReactionInfo { produces: quant, consumes } = self.reactions.get(chemical).unwrap();
			let quant = usize::from(*quant);
			let mul = (req - 1) / quant + 1;
			let excess = mul * quant - req;
			if excess > 0 { *leftover.or_insert(0) += excess; }

			for &(quant, chemical) in consumes {
				let req = mul * usize::from(quant);
				if chemical == ORE { ore_req += req; }
				else { queue.push_back((req, chemical)); }
			}
		}

		ore_req
	}
}


fn input_reactions_from_string(s: &str) -> impl IntoIterator<Item = Reaction> {
	parsing::try_reactions_from_str(s).unwrap()
}

fn input_reactions() -> impl IntoIterator<Item =Reaction<'static>> {
	input_reactions_from_string(include_str!("day14.txt"))
}


fn part1_impl<'a>(input_reactions: impl IntoIterator<Item = Reaction<'a>>) -> usize {
	Nanofactory::from_iter(input_reactions).produce_fuel(1)
}

pub(crate) fn part1() -> usize {
	part1_impl(input_reactions())
}


fn part2_impl<'a>(input_reactions: impl IntoIterator<Item = Reaction<'a>>) -> usize {
	const ORE_STORED: usize = 1_000_000_000_000;

	let nanofactory = Nanofactory::from_iter(input_reactions);

	let ore_consumed = nanofactory.produce_fuel(1);
	let mut low = ORE_STORED / ore_consumed;
	// Assuming we’ll always need at least 1 ore per fuel
	let mut high = ORE_STORED;

	while high > low + 1 {
		let mid = low.saturating_mul(high).sqrt();
		let mid = if mid == low { (low + high) / 2 } else { mid };
		let ore_consumed = nanofactory.produce_fuel(mid);
		*if ore_consumed > ORE_STORED { &mut high } else { &mut low } = mid;
	}

	low
}

pub(crate) fn part2() -> usize {
	part2_impl(input_reactions())
}


mod parsing {
	use super::{ORE, FUEL, Quantity, Chemical, ReactionInfo, Reaction};
	use std::num::ParseIntError;

	#[derive(Debug)]
	pub(super) enum QuantityChemicalError {
		MissingSpace,
		Quantity(ParseIntError),
		Chemical(char)
	}

	fn try_quantity_chemical_from(s: &str) -> Result<(Quantity, Chemical), QuantityChemicalError> {
		use QuantityChemicalError::*;
		let (quantity, chemical) = s.split_once(' ').ok_or(MissingSpace)?;
		let quantity = quantity.parse().map_err(Quantity)?;
		if let Some(c) = chemical.chars().find(|c| !c.is_ascii_uppercase()) {
			return Err(Chemical(c))
		}
		Ok((quantity, chemical))
	}

	#[allow(dead_code)]
	#[derive(Debug)]
	pub(super) enum ReactionError {
		Empty,
		MissingArrow,
		Consumes{ offset: usize, source: QuantityChemicalError },
		Produces(QuantityChemicalError)
	}

	impl<'a> TryFrom<&'a str> for Reaction<'a> {
		type Error = ReactionError;
		fn try_from(s: &'a str) -> Result<Self, Self::Error> {
			use ReactionError::*;
			if s.is_empty() { return Err(Empty) }
			let (consumes, produces) = s.split_once(" => ")
				.ok_or(MissingArrow)?;
			let consumes = consumes.split(", ")
				.enumerate()
				.map(|(offset, c)| try_quantity_chemical_from(c)
					.map_err(|e| Consumes { offset, source: e }))
				.collect::<Result<_, _>>()?;
			let (produces, chemical) = try_quantity_chemical_from(produces)
				.map_err(Produces)?;
			Ok(Reaction(chemical, ReactionInfo { produces, consumes }))
		}
	}

	#[allow(dead_code)]
	#[derive(Debug)]
	pub(super) enum ReactionsError {
		Empty,
		Reaction { line: usize, source: ReactionError },
		MissingOre,
		MissingFuel,
	}

	pub(super) fn try_reactions_from_str(s: &str) -> Result<impl IntoIterator<Item = Reaction>, ReactionsError> {
		use ReactionsError::*;
		if s.is_empty() { return Err(Empty) }
		let reactions = s.lines()
			.enumerate()
			.map(|(l, line)| line.try_into()
				.map_err(|e| Reaction { line: l + 1, source: e }))
			.collect::<Result<Vec<self::Reaction>, _>>()?;
		if !reactions.iter().flat_map(|r| r.1.consumes.iter()).any(|&(_, c)| c == ORE) { return Err(MissingOre) }
		if !reactions.iter().any(|r| r.0 == FUEL) { return Err(MissingFuel) }
		Ok(reactions)
	}
}


#[test]
fn tests() {
	const INPUTS: [(&str, usize); 5] = [
		(indoc::indoc! { "
			10 ORE => 10 A
			1 ORE => 1 B
			7 A, 1 B => 1 C
			7 A, 1 C => 1 D
			7 A, 1 D => 1 E
			7 A, 1 E => 1 FUEL
		" }, 31),
		(indoc::indoc! { "
			9 ORE => 2 A
			8 ORE => 3 B
			7 ORE => 5 C
			3 A, 4 B => 1 AB
			5 B, 7 C => 1 BC
			4 C, 1 A => 1 CA
			2 AB, 3 BC, 4 CA => 1 FUEL
		" }, 165),
		(indoc::indoc! { "
			157 ORE => 5 NZVS
			165 ORE => 6 DCFZ
			44 XJWVT, 5 KHKGT, 1 QDVJ, 29 NZVS, 9 GPVTF, 48 HKGWZ => 1 FUEL
			12 HKGWZ, 1 GPVTF, 8 PSHF => 9 QDVJ
			179 ORE => 7 PSHF
			177 ORE => 5 HKGWZ
			7 DCFZ, 7 PSHF => 2 XJWVT
			165 ORE => 2 GPVTF
			3 DCFZ, 7 NZVS, 5 HKGWZ, 10 PSHF => 8 KHKGT
		" }, 13312),
		(indoc::indoc! { "
			2 VPVL, 7 FWMGM, 2 CXFTF, 11 MNCFX => 1 STKFG
			17 NVRVD, 3 JNWZP => 8 VPVL
			53 STKFG, 6 MNCFX, 46 VJHF, 81 HVMC, 68 CXFTF, 25 GNMV => 1 FUEL
			22 VJHF, 37 MNCFX => 5 FWMGM
			139 ORE => 4 NVRVD
			144 ORE => 7 JNWZP
			5 MNCFX, 7 RFSQX, 2 FWMGM, 2 VPVL, 19 CXFTF => 3 HVMC
			5 VJHF, 7 MNCFX, 9 VPVL, 37 CXFTF => 6 GNMV
			145 ORE => 6 MNCFX
			1 NVRVD => 8 CXFTF
			1 VJHF, 6 MNCFX => 4 RFSQX
			176 ORE => 6 VJHF
		" }, 180697),
		(indoc::indoc! { "
			171 ORE => 8 CNZTR
			7 ZLQW, 3 BMBT, 9 XCVML, 26 XMNCP, 1 WPTQ, 2 MZWV, 1 RJRHP => 4 PLWSL
			114 ORE => 4 BHXH
			14 VRPVC => 6 BMBT
			6 BHXH, 18 KTJDG, 12 WPTQ, 7 PLWSL, 31 FHTLT, 37 ZDVW => 1 FUEL
			6 WPTQ, 2 BMBT, 8 ZLQW, 18 KTJDG, 1 XMNCP, 6 MZWV, 1 RJRHP => 6 FHTLT
			15 XDBXC, 2 LTCX, 1 VRPVC => 6 ZLQW
			13 WPTQ, 10 LTCX, 3 RJRHP, 14 XMNCP, 2 MZWV, 1 ZLQW => 1 ZDVW
			5 BMBT => 4 WPTQ
			189 ORE => 9 KTJDG
			1 MZWV, 17 XDBXC, 3 XCVML => 2 XMNCP
			12 VRPVC, 27 CNZTR => 2 XDBXC
			15 KTJDG, 12 BHXH => 5 XCVML
			3 BHXH, 2 VRPVC => 7 MZWV
			121 ORE => 7 VRPVC
			7 XCVML => 6 RJRHP
			5 BHXH, 4 VRPVC => 5 LTCX
		" }, 2210736),
	];
	for (input, ans) in INPUTS {
		assert_eq!(part1_impl(input_reactions_from_string(input)), ans);
	}
	assert_eq!(part1(), 720484);
	for (&(input, _), ans) in INPUTS[2..].iter().zip([82892753, 5586022, 460664]) {
		assert_eq!(part2_impl(input_reactions_from_string(input)), ans);
	}
	assert_eq!(part2(), 1993284);
}
