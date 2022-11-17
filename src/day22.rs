// Copyright (c) 2022 Bastiaan Marinus van de Weerd


enum Technique {
	NewStack,
	Cut(isize),
	Increment(usize),
}

#[derive(Clone)]
struct ComposedTechnique<const N: usize>(i64, u64);

impl<const N: usize> From<(i64, i64)> for ComposedTechnique<N> {
	fn from((a, b): (i64, i64)) -> Self {
		let b = if b < 0 { N as u64 - b.unsigned_abs() } else { b.unsigned_abs() };
		Self(a, b)
	}
}

impl<const N: usize> ComposedTechnique<N> {
	fn from(a: i64, b: i64) -> Self {
		<Self as From<(i64, i64)>>::from((a, b))
	}

	fn compose(&mut self, other: &Self) {
		use num_integer::Integer as _;
		let a = (self.0 as i128 * other.0 as i128).mod_floor(&(N as i128)) as i64;
		let bc = (self.1 as i128 * other.0 as i128).mod_floor(&(N as i128));
		let b = (bc + other.1 as i128).mod_floor(&(N as i128)) as i64;
		*self = Self::from(a, b);
	}

	fn compose_pow(&mut self, mut times: usize) {
		use num_integer::Integer as _;
		let mut composed = ComposedTechnique(1, 0);
		while times > 0 {
			if times.is_odd() { composed.compose(self) }
			times /= 2;
			self.compose(&self.clone())
		}
		*self = composed
	}

	fn apply(&self, x: usize) -> usize {
		use num_integer::Integer as _;
		let ax = (self.0 as i128 * x as i128).mod_floor(&(N as i128));
		(ax + self.1 as i128).mod_floor(&(N as i128)) as usize
	}

	fn inv_apply(&self, i: usize) -> Option<usize> {
		use {num_integer::Integer as _, num_modular::{ModularCoreOps as _, ModularPow as _}};

		// TODO(bm-w): Generalize
		if self.0 > 0 && (self.0 as usize).gcd(&N) == 1 {
			let sub = i.subm(self.1 as usize, &N);
			let inv = (self.0 as usize).powm(N - 2, &N);
			let res = sub.mulm(inv, &N);
			// TODO(bm-w): Check that `N` is prime instead
			if (self.0 as usize).mulm(res, &N).addm(self.1 as usize, &N) == i {
				return Some(res)
			}
		}

		for n in 0.. {
			let numerator = (n * N as i128  + i as i128) - self.1 as i128;
			let (q, r) = numerator.div_rem(&(self.0 as i128));
			if r == 0 && q >= 0 { return Some(q as usize) }
		}
		None
	}
}

impl<const N: usize> FromIterator<ComposedTechnique<N>> for ComposedTechnique<N> {
	fn from_iter<T: IntoIterator<Item = ComposedTechnique<N>>>(iter: T) -> Self {
		let mut composed = ComposedTechnique::<N>(1, 0);
		for composed_technique in iter {
			composed.compose(&composed_technique);
		}
		composed
	}
}

impl<'t, const N: usize> FromIterator<&'t Technique> for ComposedTechnique<N> {
	fn from_iter<T: IntoIterator<Item = &'t Technique>>(iter: T) -> Self {
		iter.into_iter().map(|t| t.composed()).collect()
	}
}

impl Technique {
	fn composed<const N: usize>(&self) -> ComposedTechnique<N> {
		use {Technique::*, ComposedTechnique as C};
		match self {
			NewStack => C::from(-1, -1),
			&Cut(offset) => C::from(1, -offset as i64),
			&Increment(stride) => C(stride as i64, 0),
		}
	}
}

trait ComposableTechniques: AsRef<[Technique]> {
	fn composed<const N: usize>(&self) -> ComposedTechnique<N> {
		self.as_ref().iter().collect()
	}
}

impl<T> ComposableTechniques for T where T: AsRef<[Technique]> {}


fn input_techniques_from_str(s: &str) -> impl AsRef<[Technique]> {
	parsing::try_techniques_from_str(s).unwrap()
}

fn input_techniques() -> impl AsRef<[Technique]> {
	input_techniques_from_str(include_str!("day22.txt"))
}


#[cfg(test)]
fn part1_brute<const N: usize, R>(input_techniques: &[Technique], transform: impl Fn(&[usize]) -> R) -> R {
	use Technique::*;
	let mut cards = (0..N).collect::<Vec<_>>();
	for technique in input_techniques.iter() { match technique {
		NewStack => cards.reverse(),
		&Cut(offset) => {
			let offset =
				if offset < 0 { N - offset.unsigned_abs() }
				else { offset as usize };
			let tmp = Vec::from(&cards[0..offset]);
			cards.copy_within(offset..N, 0);
			cards[N - offset..N].copy_from_slice(&tmp);
		}
		&Increment(stride) => {
			let mut i = 0;
			let mut tmp = vec![N; N];
			for &card in &cards {
				tmp[i] = card;
				i = (i + stride) % N;
			}
			std::mem::swap(&mut tmp, &mut cards);
		}
	} }
	transform(&cards)
}

fn part1_impl<const N: usize>(input_techniques: &[Technique], card: usize) -> usize {
	input_techniques.composed::<N>().apply(card)
}

pub(crate) fn part1() -> usize {
	part1_impl::<10_007>(input_techniques().as_ref(), 2019)
}


fn part2_impl<const N: usize, const M: usize>(input_techniques: &[Technique], position: usize) -> usize {
	let mut composed = input_techniques.composed::<N>();
	composed.compose_pow(M);
	composed.inv_apply(position).unwrap()
}

pub(crate) fn part2() -> usize {
	part2_impl::<119315717514047, 101741582076661>(input_techniques().as_ref(), 2020)
}


mod parsing {
	use std::{num::ParseIntError, str::FromStr};
	use super::Technique;

	#[derive(Debug)]
	pub(super) enum TechniqueError {
		Unknown,
		CutOffset(ParseIntError),
		IncrementStride(ParseIntError),
	}

	impl FromStr for Technique {
		type Err = TechniqueError;
		fn from_str(s: &str) -> Result<Self, Self::Err> {
			use {Technique::*, TechniqueError::*};
			if s == "deal into new stack" {
				Ok(NewStack)
			} else if let Some(cut) = s.strip_prefix("cut ") {
				Ok(Cut(cut.parse().map_err(CutOffset)?))
			} else if let Some(increment) = s.strip_prefix("deal with increment ") {
				Ok(Increment(increment.parse().map_err(IncrementStride)?))
			} else {
				return Err(Unknown)
			}
		}
	}

	#[allow(dead_code)]
	#[derive(Debug)]
	pub(super) struct TechniquesError {
		line: usize,
		source: TechniqueError,
	}

	pub(super) fn try_techniques_from_str(s: &str) -> Result<impl AsRef<[Technique]>, TechniquesError> {
		s.lines()
			.enumerate()
			.map(|(l, line)| line.parse()
				.map_err(|e| TechniquesError { line: l + 1, source: e }))
			.collect::<Result<Vec<_>, _>>()

	}
}


#[test]
fn tests() {
	const INPUTS: [(&str, [usize; 10]); 5] = [
		("deal with increment 3", [0, 7, 4, 1, 8, 5, 2, 9, 6, 3]),
		(indoc::indoc! { "
			deal with increment 7
			deal into new stack
			deal into new stack
		" }, [0, 3, 6, 9, 2, 5, 8, 1, 4, 7]),
		(indoc::indoc! { "
			cut 6
			deal with increment 7
			deal into new stack
		" }, [3, 0, 7, 4, 1, 8, 5, 2, 9, 6]),
		(indoc::indoc! { "
			deal with increment 7
			deal with increment 9
			cut -2
		" }, [6, 3, 0, 7, 4, 1, 8, 5, 2, 9]),
		(indoc::indoc! { "
			deal into new stack
			cut -2
			deal with increment 7
			cut 8
			cut -4
			deal with increment 7
			cut 3
			deal with increment 9
			deal with increment 3
			cut -1
		" }, [9, 2, 5, 8, 1, 4, 7, 0, 3, 6]),
	];
	for (input, cards) in INPUTS {
		let techniques = input_techniques_from_str(input);
		assert_eq!(part1_brute::<10, _>(techniques.as_ref(), |cards| Vec::from(cards)), cards);
		for i in 0..cards.len() {
			assert_eq!(cards[part1_impl::<10>(techniques.as_ref(), i)], i)
		}
	}
	assert_eq!(part1(), 1879);
	for (input, cards) in INPUTS {
		let techniques = input_techniques_from_str(input);
		for (i, &card) in cards.iter().enumerate() {
			assert_eq!(part2_impl::<10, 1>(techniques.as_ref(), i), card)
		}
	}
	assert_eq!(part2(), 73729306030290);
}
