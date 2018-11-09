#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(non_snake_case)]

extern crate ffi_toolkit;
extern crate libc;
extern crate rand;
extern crate tempfile;
#[macro_use(defer)]
extern crate scopeguard;
extern crate sector_base;

include!(concat!(env!("OUT_DIR"), "/libfilecoin_proofs.rs"));

use ffi_toolkit::c_str_to_rust_str;
use ffi_toolkit::rust_str_to_c_str;
use rand::{thread_rng, Rng};
use std::error::Error;
use std::sync::atomic::AtomicPtr;
use std::sync::mpsc;
use std::thread;
use std::time::Duration;

///////////////////////////////////////////////////////////////////////////////
// SectorBuilder lifecycle test
///////////////////////////////

fn make_piece(num_bytes_in_piece: usize) -> (String, Vec<u8>) {
    let mut rng = thread_rng();
    let bytes = (0..num_bytes_in_piece).map(|_| rng.gen()).collect();
    let key = (0..16)
        .map(|_| (0x20u8 + (rand::random::<f32>() * 96.0) as u8) as char)
        .collect();
    (key, bytes)
}

unsafe fn create_and_add_piece(
    sector_builder: *mut SectorBuilder,
    num_bytes_in_piece: usize,
) -> *mut AddPieceResponse {
    let (piece_key, piece_bytes) = make_piece(num_bytes_in_piece);

    add_piece(
        sector_builder,
        rust_str_to_c_str(&piece_key),
        &piece_bytes[0],
        piece_bytes.len(),
    )
}

unsafe fn sector_builder_lifecycle() -> Result<(), Box<Error>> {
    let (sector_builder, max_bytes) = {
        let metadata_dir = tempfile::tempdir().unwrap();
        let staging_dir = tempfile::tempdir().unwrap();
        let sealed_dir = tempfile::tempdir().unwrap();
        let mut prover_id: [u8; 31] = [0; 31];
        let sector_store_config: ConfiguredStore = ConfiguredStore_ProofTest;

        let resp = init_sector_builder(
            &sector_store_config,
            123,
            rust_str_to_c_str(metadata_dir.path().to_str().unwrap()),
            &mut prover_id,
            rust_str_to_c_str(sealed_dir.path().to_str().unwrap()),
            rust_str_to_c_str(staging_dir.path().to_str().unwrap()),
        );
        defer!(destroy_init_sector_builder_response(resp));

        if (*resp).status_code != 0 {
            panic!("{}", c_str_to_rust_str((*resp).error_msg))
        }

        let resp_2 = get_max_user_bytes_per_staged_sector((*resp).sector_builder);
        defer!(destroy_get_max_user_bytes_per_staged_sector_response(
            resp_2
        ));

        (
            (*resp).sector_builder,
            (*resp_2).max_staged_bytes_per_sector,
        )
    };
    defer!(destroy_sector_builder(sector_builder));

    // TODO: Replace the hard-coded byte amounts with values computed
    // from whatever was retrieved from the SectorBuilder.
    if max_bytes != 127 {
        panic!(
            "test assumes the wrong number of bytes (expected: {}, actual: {})",
            127, max_bytes
        );
    }

    // add first piece, which lazily provisions a new staged sector
    {
        let resp = create_and_add_piece(sector_builder, 10);
        defer!(destroy_add_piece_response(resp));

        if (*resp).status_code != 0 {
            panic!("{}", c_str_to_rust_str((*resp).error_msg))
        }

        assert_eq!(124, (*resp).sector_id);
    }

    // add second piece, which fits into existing staged sector
    {
        let resp = create_and_add_piece(sector_builder, 50);
        defer!(destroy_add_piece_response(resp));

        if (*resp).status_code != 0 {
            panic!("{}", c_str_to_rust_str((*resp).error_msg))
        }

        assert_eq!(124, (*resp).sector_id);
    }

    // add third piece, which won't fit into existing staging sector
    {
        let resp = create_and_add_piece(sector_builder, 100);
        defer!(destroy_add_piece_response(resp));

        if (*resp).status_code != 0 {
            panic!("{}", c_str_to_rust_str((*resp).error_msg))
        }

        // note that the sector id changed here
        assert_eq!(125, (*resp).sector_id);
    }

    // add fourth piece, where size(piece) == max
    {
        let resp = create_and_add_piece(sector_builder, 127);
        defer!(destroy_add_piece_response(resp));

        if (*resp).status_code != 0 {
            panic!("{}", c_str_to_rust_str((*resp).error_msg))
        }

        // sector id changed again (piece wouldn't fit)
        assert_eq!(126, (*resp).sector_id);
    }

    // poll for sealed sector metadata through the FFI
    {
        let (result_tx, result_rx) = mpsc::channel();
        let (kill_tx, kill_rx) = mpsc::channel();

        let atomic_ptr = AtomicPtr::new(sector_builder);

        let _join_handle = thread::spawn(move || {
            let sector_builder = atomic_ptr.into_inner();

            loop {
                match kill_rx.try_recv() {
                    Ok(_) => return,
                    _ => (),
                };

                let resp = find_sealed_sector_metadata(sector_builder, 124);
                if (*resp).status_code != 0 {
                    return;
                }

                if (*resp).metadata_exists {
                    let _ = result_tx.send((*resp).sector_id).unwrap();
                }

                thread::sleep(Duration::from_millis(1000));
            }
        });

        defer!({
            let _ = kill_tx.send(true).unwrap();
        });

        // wait up to 5 minutes for sealing to complete
        let now_sealed_sector_id = result_rx.recv_timeout(Duration::from_secs(300)).unwrap();

        assert_eq!(now_sealed_sector_id, 124);
    }

    Ok(())
}

fn main() {
    unsafe { sector_builder_lifecycle().unwrap() };
}