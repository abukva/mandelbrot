use num::complex::Complex;
use rayon::prelude::*;

pub struct Config {
    pub max_iter: usize,
    pub bound: f64,
    pub window_size: (usize, usize),
    pub x_lims: (f64, f64),
    pub y_lims: (f64, f64),
    base_iter: usize,
    initial_width: f64,
}

impl Config {
    pub fn new(
        max_iter: usize,
        bound: f64,
        window_size: (usize, usize),
        x_lims: (f64, f64),
        y_lims: (f64, f64),
    ) -> Config {
        let (x_min, x_max) = x_lims;
        let initial_width = x_max - x_min;

        Config {
            max_iter,
            bound,
            window_size,
            x_lims,
            y_lims,
            base_iter: max_iter,
            initial_width,
        }
    }

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

    fn iter_to_color(iter: f64, config: &Config) -> u32 {
        let max_iter = config.max_iter as f64;

        if iter >= max_iter {
            return 0x000000;
        }

        let log_iter = iter.log2();
        let log_max = max_iter.log2();

        let t = (log_iter / log_max).clamp(0.0, 1.0);
        let color = colorous::VIRIDIS.eval_continuous(t);

        ((color.r as u32) << 16) | ((color.g as u32) << 8) | (color.b as u32)
    }

    fn get_color(&self, config: &Config) -> u32 {
        let max_iter = self.get_iter(config);
        Self::iter_to_color(max_iter, config)
    }

    fn get_iter(&self, config: &Config) -> f64 {
        let c = self.number;
        let mut smoothed_iter = config.max_iter as f64;

        let re_shifted = c.re - 0.25;
        let q = re_shifted * re_shifted + c.im * c.im;
        let re_plus_one = c.re + 1.0;

        let cardioid_check = q * (q + re_shifted) < 0.25 * c.im * c.im;
        let period_bulb_check = re_plus_one * re_plus_one + c.im * c.im < 0.0625;

        if !(cardioid_check || period_bulb_check) {
            let mut z = Complex::new(0.0, 0.0);

            for iter in 1..config.max_iter {
                z = z * z + c;
                if z.norm() > config.bound {
                    smoothed_iter = iter as f64;
                    break;
                }
            }
            smoothed_iter = smoothed_iter + 1.0 - z.norm().log2().log2();
        }
        smoothed_iter
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

    pub fn zoom_window(&mut self, zoom: f32) {
        let zoom_factor = if zoom > 0.0 { 0.7 } else { 1.3 };

        let (x_min, x_max) = self.config.x_lims;
        let (y_min, y_max) = self.config.y_lims;

        let x_center = (x_max + x_min) / 2.0;
        let y_center = (y_max + y_min) / 2.0;

        let x_range = (x_max - x_min) * zoom_factor;
        let y_range = (y_max - y_min) * zoom_factor;

        self.config.x_lims = (x_center - x_range / 2.0, x_center + x_range / 2.0);
        self.config.y_lims = (y_center - y_range / 2.0, y_center + y_range / 2.0);

        let sqrt_zoom = (self.config.initial_width / x_range).sqrt().max(0.0);
        let additional_iter = (sqrt_zoom * 0.5) as usize;
        self.config.max_iter = self.config.base_iter + additional_iter;
    }

    pub fn update_max_iter(&mut self, iter_change: f64) {
        let new_max_iter = self.config.max_iter as f64 * (1.0 + iter_change / 100.0);
        self.config.max_iter = new_max_iter as usize;
    }

    pub fn get_image_info(&self) -> (f64, f64, f64, usize) {
        let (x_min, x_max) = self.config.x_lims;
        let (y_min, y_max) = self.config.y_lims;

        let x_range = x_max - x_min;
        let zoom = self.config.initial_width / x_range;

        let x_center = (x_max + x_min) / 2.0;
        let y_center = (y_max + y_min) / 2.0;

        (zoom, x_center, y_center, self.config.max_iter)
    }
}
