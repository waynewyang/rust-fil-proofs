use error::Result;

pub mod rocksdb;

pub trait KeyValueStore {
    type OwnedValue;

    fn put(&mut self, key: &[u8], value: &[u8]) -> Result<()>;
    fn get(&mut self, key: &[u8]) -> Result<Option<Self::OwnedValue>>;
    fn delete(&mut self, key: &[u8]) -> Result<()>;
}
