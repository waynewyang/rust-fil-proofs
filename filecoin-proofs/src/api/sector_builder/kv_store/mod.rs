use error::Result;

pub mod rocksdb;

pub trait KeyValueStore {
    fn put(&mut self, key: &[u8], value: &[u8]) -> Result<()>;
    fn get(&mut self, key: &[u8]) -> Result<Option<Vec<u8>>>;
    fn delete(&mut self, key: &[u8]) -> Result<()>;
}
