// Copyright (c) 2022 Bastiaan Marinus van de Weerd

use std::fmt::{Display, Write};


struct Layer<Pixels, const W: usize, const DMAX: char>(Pixels);

impl<Pixels: AsRef<[u8]>, const W: usize, const DMAX: char> Layer<Pixels, W, DMAX> {
	fn num_digit_pixels(&self, digit: char) -> usize {
		assert!(digit.is_ascii_digit());
		self.0.as_ref().iter().filter(|&&b| b == digit as u8).count()
	}
}

impl<Pixels: AsRef<[u8]>, const W: usize, const DMAX: char> Display for Layer<Pixels, W, DMAX> {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		let bytes = self.0.as_ref();
		let height = bytes.len() / W;
		for y in 0..height {
			for x in 0..W {
				f.write_char(bytes[y * W + x] as char)?
			}
			if y < height - 1 { f.write_char('\n')? }
		}
		Ok(())
	}
}

struct Image<LayersPixels, const W: usize, const H: usize, const DMAX: char>(LayersPixels);

impl<LayersPixels: AsRef<[u8]>, const W: usize, const H: usize, const DMAX: char> Image<LayersPixels, W, H, DMAX> {
	fn num_layers(&self) -> usize {
		self.0.as_ref().len() / (W * H)
	}

	fn layers(&self) -> impl Iterator<Item = Layer<impl AsRef<[u8]> + '_, W, DMAX>> {
		let pixels_per_layer = W * H;
		(0..self.num_layers()).map(move |i| {
			let start = i * pixels_per_layer;
			Layer(&self.0.as_ref()[start..start + pixels_per_layer])
		})
	}

	fn decode(&self) -> Result<Layer<impl AsRef<[u8]> + '_, W, '1'>, usize> {
		let layers = self.layers().collect::<Vec<_>>();
		let mut decoded_pixels = vec![b'2'; W * H];
		for (offset, pixel) in decoded_pixels.iter_mut().enumerate() {
			if let Some(b) = layers.iter()
					.map(|l| (l.0.as_ref()[offset]))
					.find(|&b| b != b'2') {
				*pixel = b;
			} else {
				return Err(offset)
			}
		}
		Ok(Layer(decoded_pixels))
	}
}


fn input_image_from_str<const W: usize, const H: usize, const DMAX: char>(s: &str) -> Image<&str, W, H, DMAX> {
	Image::try_from(s).unwrap()
}

fn input_image() -> Image<&'static str, 25, 6, '2'> {
	input_image_from_str(include_str!("day08.txt"))
}


fn part1_impl<LayersPixels: AsRef<[u8]>, const W: usize, const H: usize, const DMAX: char>(
	input_image: Image<LayersPixels, W, H, DMAX>
) -> usize {
	let layer = input_image.layers()
		.min_by_key(|l| l.num_digit_pixels('0'))
		.unwrap();
	layer.num_digit_pixels('1') * layer.num_digit_pixels('2')
}

pub(crate) fn part1() -> usize {
	part1_impl(input_image())
}


fn part2_impl<LayersPixels: AsRef<[u8]>, const W: usize, const H: usize, const DMAX: char>(
	input_image: Image<LayersPixels, W, H, DMAX>
) -> String {
	input_image.decode().unwrap().to_string()
}

pub(crate) fn part2() -> String {
	part2_impl(input_image()).replace('0', " ").replace('1', "#")
}


mod parsing {
	use super::Image;

	#[derive(Debug)]
	#[allow(dead_code)]
	pub(super) enum ImageError {
		Empty,
		NumBytes(usize),
		Pixel { column: usize, found: char }
	}

	impl<'a, const W: usize, const H: usize, const DMAX: char> TryFrom<&'a str>
	for Image<&'a str, W, H, DMAX> {
		type Error = ImageError;
		fn try_from(s: &'a str) -> Result<Self, Self::Error> {
			let s = s.trim_end_matches('\n');
			if s.is_empty() { return Err(ImageError::Empty) }
			let bytes = s.as_bytes();
			if bytes.len() % (W * H) != 0 {
				return Err(ImageError::NumBytes(bytes.len()))
			}
			if let Some(c) = bytes.iter()
					.position(|b| !(b'0'..=DMAX as u8).contains(b)) {
				return Err(ImageError::Pixel { column: c + 1, found: s.chars().nth(c).unwrap() })
			}
			Ok(Image(s))
		}
	}
}


#[test]
fn tests() {
	assert_eq!(part1_impl(input_image_from_str::<3, 2, '9'>("123456789012")), 1);
	assert_eq!(part1(), 2159);
	assert_eq!(&part2_impl(input_image_from_str::<2, 2, '2'>("0222112222120000")), "01\n10");
	assert_eq!(&part2(), indoc::indoc! { "
		 ##    ## #### #  # ###  
		#  #    #    # #  # #  # 
		#       #   #  #### #  # 
		#       #  #   #  # ###  
		#  # #  # #    #  # # #  
		 ##   ##  #### #  # #  # 
	" }.trim_end_matches('\n'));
}
