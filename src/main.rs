use mandelbrot_rust::{Config, Image};
use minifb::{Key, MouseButton, MouseMode, ScaleMode, Window, WindowOptions};

fn main() {
    let config = Config {
        max_iter: 100,
        bound: 2.0,
        window_size: (800, 600),
        x_lims: (-2.0, 1.0),
        y_lims: (-1.5, 1.5),
    };

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

    // window.set_target_fps(30);

    let mut drag_start: Option<(f32, f32)> = None;
    let mut needs_redraw = true;
    let mut was_mouse_down = false;

    while window.is_open() && !window.is_key_down(Key::Escape) {
        let current_mouse_pos = window.get_mouse_pos(MouseMode::Clamp);
        let mouse_down = window.get_mouse_down(MouseButton::Left);

        if mouse_down && !was_mouse_down {
            drag_start = current_mouse_pos;
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

        was_mouse_down = mouse_down;

        if needs_redraw {
            buffer = image.render();
            needs_redraw = false;
        }

        window.update_with_buffer(&buffer, width, height).unwrap();
    }
}
