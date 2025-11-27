use num::complex::Complex;
use rayon::prelude::*;

pub struct Config {
    pub max_iter: usize,
    pub bound: f64,
    pub window_size: (usize, usize),
    pub x_lims: (f64, f64),
    pub y_lims: (f64, f64),
}

impl Config {
    fn get_resolution(&self) -> (f64, f64) {
        let (x_min, x_max) = self.x_lims;
        let (y_min, y_max) = self.y_lims;
        let (width, height) = self.window_size;

        let delta_x = (x_max - x_min) / width as f64;
        let delta_y = (y_max - y_min) / height as f64;

        (delta_x, delta_y)
    }
}

struct Pixel {
    number: Complex<f64>,
}

impl Pixel {
    fn new(config: &Config, coords: (usize, usize)) -> Pixel {
        let number = Self::get_complex_number(coords, config);

        Pixel { number }
    }

    fn get_complex_number(coords: (usize, usize), config: &Config) -> Complex<f64> {
        let (x_idx, y_idx) = coords;
        let (x_min, _) = config.x_lims;
        let (y_min, _) = config.y_lims;

        let (delta_x, delta_y) = config.get_resolution();

        let x_coord = x_min + x_idx as f64 * delta_x;
        let y_coord = y_min + y_idx as f64 * delta_y;

        Complex::new(x_coord, y_coord)
    }

    fn iter_to_color(iter: usize, config: &Config) -> u32 {
        let max_iter = config.max_iter;
        if iter == max_iter {
            return 0x000000;
        }

        let t = iter as f64 / max_iter as f64;
        let color = colorous::VIRIDIS.eval_continuous(t);

        ((color.r as u32) << 16) | ((color.g as u32) << 8) | (color.b as u32)
    }

    fn get_color(&self, config: &Config) -> u32 {
        let c = self.number;
        let mut z = Complex::new(0.0, 0.0);

        let mut final_iter = config.max_iter;

        for iter in 1..config.max_iter {
            z = z * z + c;
            if z.norm() > config.bound {
                final_iter = iter;
                break;
            }
        }

        Self::iter_to_color(final_iter, config)
    }
}

pub struct Image {
    config: Config,
    pixels: Box<[Pixel]>,
}

impl Image {
    pub fn new(config: Config) -> Image {
        let (width, height) = config.window_size;
        let mut data: Vec<Pixel> = Vec::new();

        for y in 0..height {
            for x in 0..width {
                data.push(Pixel::new(&config, (x, y)));
            }
        }

        Image {
            config,
            pixels: data.into_boxed_slice(),
        }
    }

    pub fn render(&mut self) -> Box<[u32]> {
        self.update_pixels();

        let render: Vec<u32> = self
            .pixels
            .par_iter()
            //.iter()
            .map(|pixel| pixel.get_color(&self.config))
            .collect();
        render.into_boxed_slice()
    }

    fn update_pixels(&mut self) {
        let (width, height) = self.config.window_size;
        let mut data: Vec<Pixel> = Vec::new();

        for y in 0..height {
            for x in 0..width {
                data.push(Pixel::new(&self.config, (x, y)));
            }
        }
        self.pixels = data.into_boxed_slice();
    }

    pub fn move_window(&mut self, mouse_move: (f32, f32)) {
        let (dx, dy) = mouse_move;
        let dx = dx as f64;
        let dy = dy as f64;

        let (delta_x, delta_y) = self.config.get_resolution();

        let x_window_move = delta_x * dx;
        let y_window_move = delta_y * dy;

        let (x_min, x_max) = self.config.x_lims;
        let (y_min, y_max) = self.config.y_lims;

        self.config.x_lims = (x_min - x_window_move, x_max - x_window_move);
        self.config.y_lims = (y_min - y_window_move, y_max - y_window_move);
    }
}
