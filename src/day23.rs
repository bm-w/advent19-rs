// Copyright (c) 2022 Bastiaan Marinus van de Weerd

use std::collections::VecDeque;
use crate::day05::{
	parsing::from_str as input_nic_from_str,
	ProgramState as NicState,
	Program as Nic
};


enum PartialPackageOut {
	Dest { dest: usize },
	X { dest: usize, x: i64 },
}

struct PackageOut {
	dest: usize,
	xy: [i64; 2],
}

struct Computer<Nic, NicState> {
	nic: Nic,
	nic_state: NicState,
	partial_package_out: Option<PartialPackageOut>,
	package_y_in: Option<i64>,
	packages_xy_in: VecDeque<[i64; 2]>,
	maybe_idle: bool,
}

impl<Nic, NicState> Computer<Nic, NicState> {
	fn new(nic: Nic, nic_state: NicState) -> Self {
		Self {
			nic,
			nic_state,
			partial_package_out: None,
			package_y_in: None,
			packages_xy_in: Default::default(),
			maybe_idle: false,
		}
	}

	fn send_package_in(&mut self, package_xy_in: [i64; 2]) {
		self.maybe_idle = false;
		self.packages_xy_in.push_back(package_xy_in)
	}

	fn is_idle(&self) -> bool {
		self.maybe_idle
			&& self.partial_package_out.is_none()
			&& self.package_y_in.is_none()
			&& self.packages_xy_in.is_empty()
	}
}

impl<'a, N: Nic<'a, i64>> Computer<N, NicState<'a, i64>> {

	fn try_init(&mut self, address: usize) -> Result<(), String> {
		let mut input = Some(address as i64);
		let output = self.nic.try_step(&mut self.nic_state, || input.take())?;
		if input.is_some() {
			return Err("Unexpectedly did not take network address input".to_owned())
		} else if let Some(output) = output {
			return Err(format!("Unexpectedly returned output {output}"))
		}
		Ok(())
	} 

	fn try_nic_step(&mut self) -> Result<Option<PackageOut>, String> {

		let mut input = Some(match (self.package_y_in, self.packages_xy_in.front()) {
			(Some(package_y_in), _) => package_y_in,
			(_, Some(&[package_x_in, _])) => package_x_in,
			_ => -1,
		});

		let output = if let Some(output)
				= self.nic.try_step(&mut self.nic_state, || input.take())? {
			self.maybe_idle = false;
			use PartialPackageOut::*;
			match self.partial_package_out {
				None => {
					self.partial_package_out = Some(Dest { dest: output as usize });
					None
				}
				Some(Dest { dest }) => {
					self.partial_package_out = Some(X { dest, x: output});
					None
				}
				Some(X { dest, x }) => {
					self.partial_package_out = None;
					Some(PackageOut { dest, xy: [x, output] })
				}
			}
		} else {
			if input.is_none() {
				self.maybe_idle = false;
				if self.package_y_in.is_some() {
					self.package_y_in = None;
				} else if let Some([_, package_y_in]) = self.packages_xy_in.pop_front() {
					self.package_y_in = Some(package_y_in);
				} else {
					self.maybe_idle = true;
				}
			}

			None
		};

		Ok(output)
	}
}


fn input_nic() -> impl Nic<'static, i64> {
	input_nic_from_str::<i64>(include_str!("day23.txt"))
}


fn part1and2_impl(input_nic: impl Nic<'static, i64>, with_nat: bool) -> i64 {

	let mut computers: [_; 50] = std::array::from_fn(|i| {
		let mut computer = Computer::new(
			input_nic.clone(),
			NicState::new(true)
		);
		computer.try_init(i).unwrap();
		computer
	});

	let mut nat_package_xy = None;
	let mut last_nat_packge_y = None;

	#[cfg(test)]
	let mut dbg_i = 0;
	loop {
		#[cfg(test)]
		if dbg_i > 10_000_000 { todo!() }

		for i in 0..computers.len() {
			if let Some(package_out) = computers[i].try_nic_step().unwrap() {

				#[cfg(LOGGING)]
				println!("{dbg_i}: {i} -> {}: {:?}", package_out.dest, package_out.xy);

				if package_out.dest == 255 {
					if !with_nat {
						return package_out.xy[1]
					} else {
						nat_package_xy = Some(package_out.xy)
					}
				} else {
					computers[package_out.dest].send_package_in(package_out.xy);
				}
			}
		}

		if let Some(nat_package_xy) = nat_package_xy {
			if let Some(_nonidle) = (0..computers.len()).find(|&i| !computers[i].is_idle()) {
				#[cfg(LOGGING)]
				{
					let nc = &computers[_nonidle];
					println!("{dbg_i}: Computer {_nonidle} not idle: {}",
						if !nc.maybe_idle { "just took non-empty input".to_owned() }
						else if nc.packages_xy_in.is_empty() { format!("{} packages in queue", nc.packages_xy_in.len()) }
						else if nc.package_y_in.is_some() { "currently receiving a package".to_owned() }
						else if nc.partial_package_out.is_some() { "currently sending a package".to_owned() }
						else { "not sure why…?".to_owned() });
				}
			} else {
				#[cfg(LOGGING)]
				println!("{dbg_i}: NAT -> 0: {:?}", nat_package_xy);

				if Some(nat_package_xy[1]) == last_nat_packge_y { return nat_package_xy[1] }
				last_nat_packge_y = Some(nat_package_xy[1]);
				computers[0].send_package_in(nat_package_xy);
			}
		}

		#[cfg(test)]
		{ dbg_i += 1; }
	}
}

pub(crate) fn part1() -> i64 {
	part1and2_impl(input_nic(), false)
}

pub(crate) fn part2() -> i64 {
	part1and2_impl(input_nic(), true)
}


#[test]
fn tests() {
	assert_eq!(part1(), 16685);
	assert_eq!(part2(), 11048);
}
