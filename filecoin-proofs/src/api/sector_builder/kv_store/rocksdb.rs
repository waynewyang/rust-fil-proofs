use api::sector_builder::kv_store::KeyValueStore;
use error::Result;
use rocksdb::Options;
use rocksdb::DB;
use std::path::Path;

#[derive(Debug)]
pub struct RocksDb {
    db: DB,
}

impl RocksDb {
    pub fn new<P: AsRef<Path>>(path: P) -> Result<Self> {
        let mut opts = Options::default();
        opts.create_if_missing(true);

        let db = DB::open(&opts, path)?;
        Ok(RocksDb { db })
    }
}

impl KeyValueStore for RocksDb {
    fn put(&self, key: &[u8], value: &[u8]) -> Result<()> {
        self.db.put(key, value)?;
        Ok(())
    }

    fn get(&self, key: &[u8]) -> Result<Option<Vec<u8>>> {
        let value = self.db.get(key)?;
        Ok(value.map(|x| x.to_vec()))
    }

    fn delete(&self, key: &[u8]) -> Result<()> {
        self.db.delete(key)?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use api::sector_builder::kv_store::KeyValueStore;
    use api::sector_builder::kv_store::rocksdb::RocksDb;

    #[test]
    fn test_alpha() {
        let metadata_dir = tempfile::tempdir().unwrap();

        let db = RocksDb::new(metadata_dir).unwrap();

        let k_a = b"key-xx";
        let k_b = b"key-yy";
        let v_a = b"value-aa";
        let v_b = b"value-bb";

        db.put(k_a, v_a).unwrap();
        db.put(k_b, v_b).unwrap();

        let opt = db.get(k_a).unwrap();
        assert_eq!(format!("{:x?}", opt.unwrap()), format!("{:x?}", v_a));
    }
}
