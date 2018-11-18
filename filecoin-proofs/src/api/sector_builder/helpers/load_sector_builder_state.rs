use api::sector_builder::kv_store::KeyValueStore;
use api::sector_builder::state::SectorBuilderState;
use error::Result;

pub fn load_sector_builder_state<T: KeyValueStore>(
    mut kv_store: T,
    prover_id: [u8; 31],
) -> Result<Option<SectorBuilderState>> {
    let x = kv_store.get(&prover_id[..]);

    Ok(None)
}
