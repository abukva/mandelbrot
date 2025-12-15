#![feature(generic_const_exprs)]
#![allow(incomplete_features)]

use mandelbrot_rust::{Config, Image, bigfloat::BigFloat, text_render::TextRender};
use minifb::{Key, KeyRepeat, MouseButton, MouseMode, ScaleMode, Window, WindowOptions};

type BF = BigFloat<2>;

fn main() {
    let x_center = BF::parse("-0.743030");
    let y_center = BF::parse("0.126433");
    let offset = 0.001;
    let config = Config::<2>::new(
        30000,
        BF::from(4.0),
        (800, 800),
        (x_center - offset, x_center + offset),
        (y_center - offset, y_center + offset),
    );

    // let text_render = TextRender::new();

    let (width, height) = config.window_size;

    let mut image = Image::new(config);
    let mut buffer = image.render();

    let mut window = Window::new(
        "Mandelbrot set - Press ESC to exit",
        width,
        height,
        WindowOptions {
            resize: false,
            scale_mode: ScaleMode::UpperLeft,
            ..WindowOptions::default()
        },
    )
    .expect("Unable to create the window");

    let mut drag_start: Option<(f32, f32)> = None;
    let mut needs_redraw = true;
    let mut was_mouse_down = false;

    while window.is_open() && !window.is_key_down(Key::Escape) {
        let current_mouse_pos = window.get_mouse_pos(MouseMode::Clamp);
        let mouse_down = window.get_mouse_down(MouseButton::Left);

        if mouse_down && !was_mouse_down {
            drag_start = current_mouse_pos;
        }

        if window.is_key_pressed(Key::I, KeyRepeat::No) {
            image.update_max_iter(30.0);
            needs_redraw = true;
        } else if window.is_key_pressed(Key::O, KeyRepeat::No) {
            image.update_max_iter(-30.0);
            needs_redraw = true;
        } else if window.is_key_pressed(Key::Z, KeyRepeat::No) {
            image.zoom_window(10.0);
            needs_redraw = true;
        }

        if !mouse_down && was_mouse_down {
            if let (Some((curr_x, curr_y)), Some((last_x, last_y))) =
                (current_mouse_pos, drag_start)
            {
                let dx = curr_x - last_x;
                let dy = curr_y - last_y;

                image.move_window((dx, dy));
                needs_redraw = true;
            }
            drag_start = None;
        }

        if let Some((_, scroll_y)) = window.get_scroll_wheel()
            && scroll_y.abs() > 0.0
        {
            image.zoom_window(scroll_y);
            needs_redraw = true;
        }

        was_mouse_down = mouse_down;

        if needs_redraw {
            buffer = image.render();
            // let (zoom, x_center, y_center, max_iter) = image.get_image_info();
            // let text_info = format!(
            //     "Zoom: {:.2e} Center: ({:.6}, {:.6})i MaxIter: {}",
            //     zoom, x_center, y_center, max_iter
            // );
            //
            // text_render.draw_text(
            //     &mut buffer,
            //     width,
            //     height,
            //     &text_info,
            //     10,
            //     10,
            //     20.0,
            //     0xFFFFFF,
            // );
            needs_redraw = false;
        }

        window.update_with_buffer(&buffer, width, height).unwrap();
    }
}
