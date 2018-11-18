use api::sector_builder::kv_store::KeyValueStore;
use error::Result;
use rocksdb::{DBVector, DB};
use std::path::Path;

#[derive(Debug)]
pub struct RocksDb {
    db: DB,
}

impl RocksDb {
    pub fn new<P: AsRef<Path>>(path: P) -> Result<Self> {
        let db = DB::open_default(path)?;
        Ok(RocksDb { db })
    }
}

impl KeyValueStore for RocksDb {
    type OwnedValue = DBVector;

    fn put(&mut self, key: &[u8], value: &[u8]) -> Result<()> {
        self.db.put(key, value)?;
        Ok(())
    }

    fn get(&mut self, key: &[u8]) -> Result<Option<Self::OwnedValue>> {
        let value = self.db.get(key)?;
        Ok(value)
    }

    fn delete(&mut self, key: &[u8]) -> Result<()> {
        self.db.delete(key)?;
        Ok(())
    }
}
