use std::cmp::min;
use std::io::{self, Write};
use std::iter::FromIterator;

use bitvec::{self, BitVec};
use itertools::Itertools;

pub const FR_UNPADDED_BITS: usize = 254;
pub const FR_PADDED_BITS: usize = 256;

#[derive(Debug)]

// Invariant: it is an error for bit_part to be > 7.
pub struct BytesBits {
    bytes: usize,
    bits: usize,
}

impl BytesBits {
    pub fn from_bits(bits: usize) -> BytesBits {
        BytesBits {
            bytes: bits / 8,
            bits: bits % 8,
        }
    }
    pub fn total_bits(&self) -> usize {
        self.bytes * 8 + self.bits
    }

    pub fn is_byte_aligned(&self) -> bool {
        self.bits == 0
    }

    // How many distinct bytes are needed to represent data of this size?
    pub fn bytes_needed(&self) -> usize {
        self.bytes + if self.bits == 0 {
            0
        } else {
            (self.bits + 8) / 8
        }
    }
}

#[derive(Debug)]
pub struct PaddingMap {
    data_chunk_bits: usize,
    padded_chunk_bits: usize,
}

fn div_rem(a: usize, b: usize) -> (usize, usize) {
    let div = a / b;
    let rem = a % b;
    (div, rem)
}

fn transform_bit_pos(p: usize, from_size: usize, to_size: usize) -> usize {
    let (div, rem) = div_rem(p, from_size);
    (div * to_size) + rem
}

fn transform_byte_pos(p: usize, from_bit_size: usize, to_bit_size: usize) -> usize {
    let bit_pos = p * 8;
    let transformed_bit_pos = transform_bit_pos(bit_pos, from_bit_size, to_bit_size);
    let transformed_byte_pos1 = transformed_bit_pos as f64 / 8.;

    (if from_bit_size < to_bit_size {
        transformed_byte_pos1.ceil()
    } else {
        transformed_byte_pos1.floor()
    }) as usize
}

impl PaddingMap {
    pub fn new(data_bits: usize, representation_bits: usize) -> PaddingMap {
        assert!(data_bits <= representation_bits);
        PaddingMap {
            data_chunk_bits: data_bits,
            padded_chunk_bits: representation_bits,
        }
    }

    pub fn padding_bits(&self) -> usize {
        self.padded_chunk_bits - self.data_chunk_bits
    }

    pub fn expand_bits(&self, size: usize) -> usize {
        transform_bit_pos(size, self.data_chunk_bits, self.padded_chunk_bits)
    }

    pub fn contract_bits(&self, size: usize) -> usize {
        transform_bit_pos(size, self.padded_chunk_bits, self.data_chunk_bits)
    }

    pub fn expand_bytes(&self, bytes: usize) -> usize {
        transform_byte_pos(bytes, self.data_chunk_bits, self.padded_chunk_bits)
    }

    pub fn contract_bytes(&self, bytes: usize) -> usize {
        transform_byte_pos(bytes, self.padded_chunk_bits, self.data_chunk_bits)
    }

    pub fn padded_bytes_bits_from_bits(&self, bits: usize) -> BytesBits {
        let expanded = self.expand_bits(bits);
        BytesBits::from_bits(expanded)
    }

    pub fn padded_bytes_bits_from_bytes(&self, bytes: usize) -> BytesBits {
        self.padded_bytes_bits_from_bits(bytes * 8)
    }

    pub fn padded_bytes_are_aligned(&self, bytes: usize) -> bool {
        self.padded_bytes_bits_from_bytes(bytes).is_byte_aligned()
    }

    pub fn next_fr_end(&self, current: BytesBits) -> BytesBits {
        let current_bits = current.total_bits();

        let (previous, remainder) = div_rem(current_bits, self.padded_chunk_bits);

        let next_bit_boundary = if remainder == 0 {
            current_bits + self.padded_chunk_bits
        } else {
            previous + self.padded_chunk_bits
        };

        BytesBits::from_bits(next_bit_boundary)
    }
}

pub const FR32_PADDING_MAP: PaddingMap = PaddingMap {
    data_chunk_bits: FR_UNPADDED_BITS,
    padded_chunk_bits: FR_PADDED_BITS,
};

pub fn write_padded<W: ?Sized>(source: &[u8], target: &mut W) -> io::Result<usize>
where
    W: Write,
{
    write_padded_aux(FR32_PADDING_MAP, source, target)
}

pub fn write_padded_aux<W: ?Sized>(
    padding_map: PaddingMap,
    source: &[u8],
    target: &mut W,
) -> io::Result<usize>
where
    W: Write,
{
    let unpadded_chunks = BitVec::<bitvec::LittleEndian, u8>::from(source)
        .into_iter()
        .chunks(padding_map.data_chunk_bits);

    for chunk in unpadded_chunks.into_iter() {
        let mut bits = BitVec::<bitvec::LittleEndian, u8>::from_iter(chunk);

        // pad
        while bits.len() < padding_map.padded_chunk_bits {
            bits.push(false);
        }
        let out = &bits.into_boxed_slice();

        target.write_all(&out)?;
    }
    // Always return the expected number of bytes, since this function will fail if write_all does.
    Ok(source.len())
}

// offset and num_bytes are based on the unpadded data, so
// if [0, 1, ..., 255] was the original unpadded data, offset 3 and len 4 would return
// [2, 3, 4, 5].
pub fn write_unpadded<W: ?Sized>(
    source: &[u8],
    target: &mut W,
    offset: usize,
    len: usize,
) -> io::Result<usize>
where
    W: Write,
{
    write_unpadded_aux(FR32_PADDING_MAP, source, target, offset, len)
}

pub fn write_unpadded_aux<W: ?Sized>(
    padding_map: PaddingMap,
    source: &[u8],
    target: &mut W,
    offset_bytes: usize,
    len: usize,
) -> io::Result<usize>
where
    W: Write,
{
    let mut bits_remaining = padding_map.expand_bits(len * 8);
    let mut offset = padding_map.padded_bytes_bits_from_bytes(offset_bytes);

    let mut bits_out = BitVec::<bitvec::LittleEndian, u8>::new();
    while bits_remaining > 0 {
        let start = offset.bytes;
        let bits_to_skip = offset.bits;
        let offset_total_bits = offset.total_bits();
        let next_boundary = padding_map.next_fr_end(offset);
        let end = next_boundary.bytes;

        let current_fr_bits_end = next_boundary.total_bits() - padding_map.padding_bits();
        let bits_to_next_boundary = current_fr_bits_end - offset_total_bits;

        let raw_bits = BitVec::<bitvec::LittleEndian, u8>::from(&source[start..end]);
        let skipped = raw_bits.into_iter().skip(bits_to_skip);

        //let restricted = skipped.take(padding_map.data_chunk_bits);
        let restricted = skipped.take(bits_to_next_boundary);

        let available_bits = ((end - start) * 8) - bits_to_skip;

        let bits_to_take = min(bits_remaining, available_bits);

        let taken = restricted.into_iter().take(bits_to_take);
        bits_out.extend(taken);

        bits_remaining -= bits_to_take;

        offset = BytesBits {
            bytes: end,
            bits: 0,
        };
    }

    // TODO: Don't write the whole output into a huge BitVec.
    // Instead, write it incrementally –
    // but ONLY when the bits waiting in bits_out are byte-aligned. i.e. a multiple of 8

    let boxed_slice = bits_out.into_boxed_slice();

    target.write_all(&boxed_slice)?;

    Ok(len)
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::{Rng, SeedableRng, XorShiftRng};

    #[test]
    fn test_position() {
        let mut bits = 0;
        for i in 0..10 {
            for j in 0..8 {
                let position = BytesBits { bytes: i, bits: j };
                assert_eq!(position.total_bits(), bits);
                bits += 1;
            }
        }
    }

    #[test]
    fn test_write_padded() {
        let data = vec![255u8; 32];
        let mut padded = Vec::new();
        let written = write_padded(&data, &mut padded).unwrap();
        assert_eq!(written, 32);
        assert_eq!(padded.len(), 64);
        assert_eq!(&padded[0..31], &data[0..31]);
        assert_eq!(padded[31], 0b0011_1111);
        assert_eq!(padded[32], 0b0000_0011);
        assert_eq!(&padded[33..], vec![0u8; 31].as_slice());
    }

    #[test]
    fn test_write_padded_alt() {
        let mut source = vec![
            1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24,
            25, 26, 27, 28, 29, 30, 31, 0xff, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
            16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0xff, 9, 9,
        ];
        // FIXME: This doesn't exercise the ability to write a second time, which is the point of the extra_bytes in write_test.
        source.extend(vec![9, 0xff]);

        let mut buf = Vec::new();
        write_padded(&source, &mut buf).unwrap();

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
    fn test_read_write_padded() {
        let len = 1016; // Use a multiple of 254.
        let data = vec![255u8; len];
        let mut padded = Vec::new();
        let padded_written = write_padded(&data, &mut padded).unwrap();
        assert_eq!(padded_written, len);
        assert_eq!(padded.len(), FR32_PADDING_MAP.expand_bytes(len));

        let mut unpadded = Vec::new();
        let unpadded_written = write_unpadded(&padded, &mut unpadded, 0, len).unwrap();
        assert_eq!(unpadded_written, len);
        assert_eq!(data, unpadded);
    }

    #[test]
    fn test_read_write_padded_offset() {
        let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        let len = 1016;
        let data: Vec<u8> = (0..len).map(|_| rng.gen()).collect();
        let mut padded = Vec::new();
        write_padded(&data, &mut padded).unwrap();

        {
            let mut unpadded = Vec::new();
            write_unpadded(&padded, &mut unpadded, 0, 1016).unwrap();
            let expected = &data[0..1016];

            assert_eq!(expected.len(), unpadded.len());
            assert_eq!(expected, &unpadded[..]);
        }

        {
            let mut unpadded = Vec::new();
            write_unpadded(&padded, &mut unpadded, 0, 44).unwrap();
            let expected = &data[0..44];

            assert_eq!(expected.len(), unpadded.len());
            assert_eq!(expected, &unpadded[..]);
        }
        {
            let mut unpadded = Vec::new();
            let start = 1;
            let len = 35;
            write_unpadded(&padded, &mut unpadded, start, len).unwrap();
            let expected = &data[start..start + len];

            assert_eq!(expected, &unpadded[..]);
        }
    }
}
