use fr32::Fr32Ary;
use std::cmp;
use std::fmt::{self, Debug};
use std::io::{Read, Result, Write};

pub struct Fr32Writer<W> {
    inner: W,
    prefix: u8,
    prefix_size: usize,
    bits_needed: usize,
}

//impl<W> Debug for Fr32Writer<W> {
//    fn fmt(&self, f: &'_ mut fmt::Formatter<'_>) -> fmt::Result {
//        unimplemented!();
//    }
//}

pub struct Fr32Reader<R> {
    _inner: R,
}

pub const FR_INPUT_BYTE_LIMIT: usize = 254;

/// Given in_bytes written to Fr32Writer, how many bytes are written to its inner writer?
pub fn writer_bytes_out(in_bytes: u64) -> u64 {
    expand_byte_pos(in_bytes)
}

fn div_rem(a: u64, b: u64) -> (u64, u64) {
    let div = a / b;
    let rem = a % b;
    (div, rem)
}

fn transform_bit_pos(p: u64, from_size: u64, to_size: u64) -> u64 {
    let (div, rem) = div_rem(p, from_size);
    (div * to_size) + rem
}

fn expand_bit_pos(p: u64) -> u64 {
    transform_bit_pos(p, 254, 256)
}

fn contract_bit_pos(p: u64) -> u64 {
    transform_bit_pos(p, 256, 254)
}

fn transform_byte_pos(p: u64, from_bit_size: u64, to_bit_size: u64) -> u64 {
    let bit_pos = p * 8;
    let transformed_bit_pos = transform_bit_pos(bit_pos, from_bit_size, to_bit_size);
    let transformed_byte_pos1 = (transformed_bit_pos as f64 / 8.);

    (if from_bit_size < to_bit_size {
        transformed_byte_pos1.ceil()
    } else {
        transformed_byte_pos1.floor()
    }) as u64
}

fn transform_byte_posx(p: u64, from_bit_size: u64, to_bit_size: u64) -> u64 {
    if from_bit_size == to_bit_size {
        return p;
    }
    let bit_pos = p * 8;
    let (div, rem) = div_rem(bit_pos, from_bit_size);
    let transformed_bit_pos = (div * to_bit_size) + rem;
    let transformed_full_bytes = transformed_bit_pos / 8;
    let remainder_byte = if rem > 0 { ((rem + 7) / 8) } else { 0 };
    println!(
        "p: {}; from: {}; to: {}; div: {}; rem: {}; transformed_bit_pos: {};
         transformed_full_bytes: {}; remainder_byte: {}",
        p,
        from_bit_size,
        to_bit_size,
        div,
        rem,
        transformed_bit_pos,
        transformed_full_bytes,
        remainder_byte
    );
    if from_bit_size < to_bit_size {
        transformed_full_bytes + remainder_byte
    } else {
        println!("tfb: {}; rb: {}", transformed_full_bytes, remainder_byte);
        transformed_full_bytes + remainder_byte
    }
}

pub fn expand_byte_pos(p: u64) -> u64 {
    transform_byte_pos(p, 254, 256)
}

fn contract_byte_pos(p: u64) -> u64 {
    transform_byte_pos(p, 256, 254)
}

/// How many bytes must be written to Fr32Writer for out_bytes to be written to its inner writer?
/// FIXME: Is this actually always true?
pub fn writer_bytes_in(out_bytes: u64) -> u64 {
    contract_byte_pos(out_bytes)
}

impl<W: Write> Write for Fr32Writer<W> {
    fn write(&mut self, mut buf: &[u8]) -> Result<usize> {
        println!("--->writing {} bytes…", buf.len());
        println!(
            "Fr32Writer--> prefix_size: {}; prefix: {}; bits_needed: {}",
            self.prefix_size, self.prefix, self.bits_needed
        );
        let bytes_remaining = buf.len();
        let mut total_bytes_consumed = 0;
        let mut bytes_written = 0;

        while total_bytes_consumed < bytes_remaining {
            let (remainder, remainder_size, bytes_consumed, bytes_to_write, more) =
                self.process_bytes(&buf);
            total_bytes_consumed += bytes_consumed;
            println!(
                "bytes_consumed: {}; total_bytes_consumed: {}",
                bytes_consumed, total_bytes_consumed
            );
            if more {
                // We read a complete chunk and should continue.
                bytes_written += self.ensure_write(&bytes_to_write)?;
            } else {
                // We read an incomplete chunk, so this is the last iteration.
                // We must have consumed all the bytes in buf.
                assert!(buf.len() == bytes_consumed);
                assert!(bytes_consumed < 32);

                // Write those bytes but no more (not a whole 32-byte chunk).
                let real_length = buf.len();
                assert!(real_length <= bytes_to_write.len());

                let truncated = &bytes_to_write[0..real_length];
                bytes_written += self.ensure_write(truncated)?;

                if self.prefix_size > 0 {
                    // Since this chunk was incomplete, what would have been the remainder was included as the last byte to write.
                    // We shouldn't write it now, though, because we may need to write more bytes later.
                    // However, we do need to save the prefix.
                    self.prefix = bytes_to_write[real_length];
                }

                break;
            }

            self.prefix = remainder;
            self.prefix_size = remainder_size;

            let residual_bytes_size = buf.len() - bytes_consumed;
            let residual_bytes = &buf[(buf.len() - residual_bytes_size)..buf.len()];
            buf = residual_bytes;
        }
        Ok(bytes_written)
    }

    fn flush(&mut self) -> Result<()> {
        self.inner.flush()
    }
}

impl<W: Write> Fr32Writer<W> {
    pub fn new(inner: W) -> Fr32Writer<W> {
        Fr32Writer {
            inner,
            prefix: 0,
            prefix_size: 0,
            bits_needed: FR_INPUT_BYTE_LIMIT,
        }
    }
    // Tries to process bytes.
    // Returns result of (remainder, remainder size, bytes_consumed, byte output, complete). Remainder size is in bits.
    // Complete is true iff we read a complete chunk of data.
    pub fn process_bytes(&mut self, bytes: &[u8]) -> (u8, usize, usize, Fr32Ary, bool) {
        let bits_needed = self.bits_needed;
        let full_bytes_needed = bits_needed / 8;

        // The non-byte-aligned tail bits are the suffix and will become the final byte of output.
        let suffix_size = bits_needed % 8;

        // Anything left in the byte containing the suffix will become the remainder.
        let mut remainder_size = 8 - suffix_size;

        // Consume as many bytes as needed, unless there aren't enough.
        let bytes_to_consume = cmp::min(full_bytes_needed, bytes.len());
        println!(
            "bits_needed: {}; bytes.len(): {}; bytes_to_consume: {}; remainder_size: {}",
            bits_needed,
            bytes.len(),
            bytes_to_consume,
            remainder_size,
        );
        let mut final_byte = 0;
        let mut bytes_consumed = bytes_to_consume;
        let mut incomplete = false;

        if bytes_to_consume <= bytes.len() {
            if remainder_size != 0 {
                if (bytes_to_consume + 1) > bytes.len() {
                    // Too few bytes were sent.
                    incomplete = true;
                } else {
                    // This iteration's remainder will be included in next iteration's output.
                    self.bits_needed = FR_INPUT_BYTE_LIMIT - remainder_size;

                    // The last byte we consume is special.
                    final_byte = bytes[bytes_to_consume];

                    // Increment the count of consumed bytes, since we just consumed another.
                    bytes_consumed += 1;
                }
            }
        } else {
            // Too few bytes were sent.
            incomplete = true;
        }

        println!(
            "bytes_consumed: {}; final_byte: {}",
            bytes_consumed, final_byte
        );

        if incomplete {
            println!("incomplete!");
            // Too few bytes were sent.

            // We will need the unsent bits next iteration.
            self.bits_needed = bits_needed - bytes.len();

            // We only consumed the bytes that were sent.
            bytes_consumed = bytes.len();

            // The current prefix and remainder have the same size; no padding is added in this iteration.
            remainder_size = self.prefix_size;
        } else {
            println!("COMPLETE!!!!!");
        }

        // Grab all the full bytes (excluding suffix) we intend to consume.
        let full_bytes = &bytes[0..bytes_to_consume];

        // The suffix is the last part of this iteration's output.
        // The remainder will be the first part of next iteration's output.
        let (suffix, remainder) = split_byte(final_byte, suffix_size);
        println!("remainder: {}", remainder);
        let out_bytes = assemble_bytes(self.prefix, self.prefix_size, full_bytes, suffix);
        (
            remainder,
            remainder_size,
            bytes_consumed,
            out_bytes,
            !incomplete,
        )
    }

    pub fn finish(&mut self) -> Result<usize> {
        println!("finishing");
        if self.prefix_size > 0 {
            assert!(self.prefix_size <= 8);
            let b = self.prefix;
            self.ensure_write(&[b])?;
            self.flush()?;
            self.prefix_size = 0;
            self.prefix = 0;
            Ok(1)
        } else {
            Ok(0)
        }
    }

    fn ensure_write(&mut self, mut buffer: &[u8]) -> Result<usize> {
        println!("writing {:?}", buffer);
        let mut bytes_written = 0;

        while !buffer.is_empty() {
            let n = self.inner.write(buffer)?;

            buffer = &buffer[n..buffer.len()];
            bytes_written += n;
        }
        println!("wrote: {}", bytes_written);
        Ok(bytes_written)
    }
}

// Splits byte into two parts at position, pos.
// The more significant part is right-shifted by pos bits, and both parts are returned,
// least-significant first.
fn split_byte(byte: u8, pos: usize) -> (u8, u8) {
    if pos == 0 {
        return (0, byte);
    };
    let b = byte >> pos;
    let mask_size = 8 - pos;
    let mask = (0xff >> mask_size) << mask_size;
    let a = (byte & mask) >> mask_size;
    (a, b)
}

// Safely shift left by up to 8, truncating overflow.
// NOTE: We don't need this anymore since we handle prefix of size 8 specially.
fn left_shift_safe(byte: u8, shift: usize) -> u8 {
    assert!(shift <= 8);
    let shifted = (byte as u16) << shift;
    shifted as u8
}

// Prepend prefix to bytes, shifting all bytes left by prefix_size.
fn assemble_bytes(mut prefix: u8, prefix_size: usize, bytes: &[u8], suffix: u8) -> Fr32Ary {
    assert!(bytes.len() <= 31);
    let mut out = [0u8; 32];
    out[0] = prefix;

    assert!(prefix_size <= 8, "prefix_size must not be greater than 8.");

    // We have to handle a 'full-sized prefix' specially because otherwise we lose data.
    if prefix_size == 8 {
        println!("************* PREFIX_SIZE==8 *****************");
        for (place, data) in out.iter_mut().skip(1).zip(bytes.iter()) {
            *place = *data
        }
        out[bytes.len() + 1] = suffix;
        return out;
    }

    let left_shift = prefix_size;
    let right_shift = 8 - prefix_size;
    for (i, b) in bytes.iter().enumerate() {
        if prefix_size == 0 {
            out[i] |= b;
        } else {
            let shifted = *b << left_shift; // This may overflow 8 bits, truncating the most significant bits.
            out[i] = prefix | shifted;
            prefix = b >> right_shift;
        }
    }
    out[bytes.len()] = prefix | (suffix << left_shift);
    out
}

impl<R: Read> Fr32Reader<R> {
    pub fn new(inner: R) -> Fr32Reader<R> {
        Fr32Reader { _inner: inner }
    }
}

impl<R: Read + Debug> Read for Fr32Reader<R> {
    fn read(&mut self, _buf: &mut [u8]) -> Result<usize> {
        unimplemented!();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_left_shift_safe() {
        let shifted = left_shift_safe(0xff, 2);
        assert_eq!(shifted, 0xff ^ 3);

        let shifted = left_shift_safe(0xff, 8);
        assert_eq!(shifted, 0);
    }

    fn write_test(bytes: &[u8], extra_bytes: &[u8]) -> (usize, Vec<u8>) {
        let mut data = Vec::new();

        let write_count = {
            let mut writer = Fr32Writer::new(&mut data);
            let mut count = writer.write(&bytes).unwrap();
            // This tests to make sure state is correctly maintained so we can restart writing mid-32-byte chunk.
            count += writer.write(extra_bytes).unwrap();
            count += writer.finish().unwrap();
            count
        };

        (write_count, data)
    }

    #[test]
    fn test_write() {
        let source = vec![
            1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24,
            25, 26, 27, 28, 29, 30, 31, 0xff, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
            16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0xff, 9, 9,
        ];
        let extra = vec![9, 0xff];

        let (write_count, buf) = write_test(&source, &extra);
        assert_eq!(write_count, 69);
        assert_eq!(buf.len(), 69);

        for i in 0..31 {
            assert_eq!(buf[i], i as u8 + 1);
        }
        assert_eq!(buf[31], 63); // Six least significant bits of 0xff
        assert_eq!(buf[32], (1 << 2) | 0b11); // 7
        for i in 33..63 {
            assert_eq!(buf[i], (i as u8 - 31) << 2);
        }
        assert_eq!(buf[63], (0x0f << 2)); // 4-bits of ones, half of 0xff, shifted by two, followed by two bits of 0-padding.
        assert_eq!(buf[64], 0x0f | 9 << 4); // The last half of 0xff, 'followed' by 9.
        assert_eq!(buf[65], 9 << 4); // A shifted 9.
        assert_eq!(buf[66], 9 << 4); // Another.
        assert_eq!(buf[67], 0xf0); // The final 0xff is split into two bytes. Here is the first half.
        assert_eq!(buf[68], 0x0f); // And here is the second.
    }

    #[test]
    fn test_in_out_size() {
        for i in 0..1000 {
            let out = writer_bytes_out(i);
            let back_in = writer_bytes_in(out);
            println!("i: {}; out: {}; back_in: {}", i, out, back_in);
            assert_eq!(i, back_in);
        }
    }
    #[test]
    fn test_expand_contract_byte_pos() {
        for p in 0..545 {
            let expanded = expand_byte_pos(p);
            let back = contract_byte_pos(expanded);
            println!("p: {}; expanded: {}; back: {}", p, expanded, back);
            //assert_eq!(p, back);
        }
    }
}
