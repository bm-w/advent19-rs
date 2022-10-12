// Copyright (c) 2022 Bastiaan Marinus van de Weerd

use std::{ops::{Add, Mul}, str::FromStr, fmt::Display};
use crate::day05::{self, Op, parsing::from_str as input_program_from_str, Program};


#[derive(Debug, PartialEq, PartialOrd, Default, Clone)]
struct BigInt(num_bigint::BigInt);

impl From<bool> for BigInt {
	fn from(b: bool) -> Self {
		Self(num_bigint::BigInt::from(i32::from(b)))
	}
}

impl day05::IntNum for BigInt {
	type TryAsIsizeError = <isize as TryFrom<num_bigint::BigInt>>::Error;

	fn from_op(o: day05::Op) -> Self {
		Self(num_bigint::BigInt::from(u16::from(&o)))
	}

	fn from_isize(i: isize) -> Self {
		Self(num_bigint::BigInt::from(i))
	}

	fn try_as_op(&self) -> Result<day05::Op, day05::parsing::OpError> {
		Op::try_from((self.0.clone().try_into() as Result<u16, _>)
			.map_err(|_| day05::parsing::OpError::Format)?)
	}

	fn try_as_isize(&self) -> Result<isize, Self::TryAsIsizeError> {
		self.0.clone().try_into()
	}
}

impl Add<BigInt> for BigInt {
	type Output = BigInt;
	fn add(self, rhs: BigInt) -> Self::Output {
		Self(self.0 + rhs.0)
	}
}

impl Mul<BigInt> for BigInt {
	type Output = BigInt;
	fn mul(self, rhs: BigInt) -> Self::Output {
		Self(self.0 * rhs.0)
	}
}

impl FromStr for BigInt {
	type Err = <num_bigint::BigInt as FromStr>::Err;
	fn from_str(s: &str) -> Result<Self, Self::Err> {
		num_bigint::BigInt::from_str(s).map(BigInt)
	}
}

impl Display for BigInt {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		self.0.fmt(f)
	}
}


fn part1and2_impl(input: u8) -> String {
	use itertools::Itertools as _;
	let input = BigInt(num_bigint::BigInt::from(input));
	let mut p = input_program_from_str::<BigInt>(include_str!("day09.txt"));
	p.execute_ext(true, std::iter::once(input))
		.exactly_one().map_err(|_| ()).unwrap().to_string()
}

pub(crate) fn part1() -> String {
	part1and2_impl(1)
}

pub(crate) fn part2() -> String {
	part1and2_impl(2)
}


#[test]
fn tests() {
	use itertools::Itertools as _;
	const INPUTS: [&str; 3] = [
		"109,1,204,-1,1001,100,1,100,1008,100,16,101,1006,101,0,99",
		"1102,34915192,34915192,7,4,7,99,0",
		"104,1125899906842624,99",
	];
	assert_eq!(input_program_from_str::<i64>(INPUTS[0]).execute_ext(true, std::iter::empty())
		.map(|x| x.to_string()).join(","), INPUTS[0]);
	assert_eq!(input_program_from_str::<BigInt>(INPUTS[1]).execute_ext(true, std::iter::empty()).exactly_one().map_err(|_| ()).unwrap(),
		BigInt::from_str("1219070632396864").unwrap());
		assert_eq!(input_program_from_str::<BigInt>(INPUTS[2]).execute_ext(true, std::iter::empty()).exactly_one().map_err(|_| ()).unwrap(),
			BigInt::from_str("1125899906842624").unwrap());
	assert_eq!(part1(), "2377080455");
	assert_eq!(part2(), "74917");
}
