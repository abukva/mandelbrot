use fontdue::{Font, FontSettings};

pub struct TextRender {
    font: Font,
}

impl TextRender {
    pub fn new() -> Self {
        let font_data = include_bytes!("../0xProtoNerdFont-Regular.ttf");
        let font = Font::from_bytes(font_data as &[u8], FontSettings::default())
            .expect("Failed to load the font!");

        TextRender { font }
    }

    pub fn draw_text(
        &self,
        buffer: &mut [u32],
        width: usize,
        height: usize,
        text: &str,
        x: usize,
        y: usize,
        size: f32,
        color: u32,
    ) {
        let mut cursor_x = x;

        for ch in text.chars() {
            let (metrics, bitmap) = self.font.rasterize(ch, size);

            for py in 0..metrics.height {
                for px in 0..metrics.width {
                    let screen_x = cursor_x + px;
                    let screen_y = y + py;

                    if screen_x >= width || screen_y >= height {
                        continue;
                    }

                    let alpha = bitmap[py * metrics.width + px];
                    if alpha > 128 {
                        let buffer_idx = screen_y * width + screen_x;
                        buffer[buffer_idx] = color;
                    }
                }
            }
            cursor_x += metrics.advance_width as usize;
        }
    }
}
