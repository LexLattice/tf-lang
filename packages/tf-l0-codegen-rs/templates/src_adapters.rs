use std::collections::{HashMap, HashSet};

use anyhow::Result;
use sha2::{Digest, Sha256};

pub trait Network {
    fn publish(&mut self, topic: &str, key: &str, payload: &str) -> Result<()>;
}

pub trait Observability {
    fn emit_metric(&mut self, name: &str, value: Option<f64>) -> Result<()>;
}

pub trait Storage {
    fn write_object(
        &mut self,
        uri: &str,
        key: &str,
        value: &str,
        idempotency_key: Option<&str>,
    ) -> Result<()>;
    fn read_object(&self, uri: &str, key: &str) -> Result<Option<String>>;
    fn compare_and_swap(
        &mut self,
        uri: &str,
        key: &str,
        expect: Option<&str>,
        update: &str,
    ) -> Result<bool>;
}

pub trait Crypto {
    fn sign(&self, key: &str, data: &[u8]) -> Result<Vec<u8>>;
    fn verify(&self, key: &str, data: &[u8], signature: &[u8]) -> Result<bool>;
    fn hash(&self, data: &[u8]) -> Result<String>;
}

#[derive(Debug, Clone, Default)]
pub struct PublishedMessage {
    pub topic: String,
    pub key: String,
    pub payload: String,
}

#[derive(Default)]
pub struct InMemoryAdapters {
    published: Vec<PublishedMessage>,
    storage: HashMap<(String, String), String>,
    idempotency: HashSet<String>,
    metrics: HashMap<String, f64>,
}

impl InMemoryAdapters {
    pub fn new() -> Self {
        Self::default()
    }

    fn token(uri: &str, key: &str, idempotency_key: Option<&str>) -> Option<String> {
        idempotency_key.map(|value| format!("{}::{}::{}", uri, key, value))
    }
}

impl Network for InMemoryAdapters {
    fn publish(&mut self, topic: &str, key: &str, payload: &str) -> Result<()> {
        self.published.push(PublishedMessage {
            topic: topic.to_string(),
            key: key.to_string(),
            payload: payload.to_string(),
        });
        Ok(())
    }
}

impl Observability for InMemoryAdapters {
    fn emit_metric(&mut self, name: &str, value: Option<f64>) -> Result<()> {
        let entry = self.metrics.entry(name.to_string()).or_insert(0.0);
        *entry += value.unwrap_or(1.0);
        Ok(())
    }
}

impl Storage for InMemoryAdapters {
    fn write_object(
        &mut self,
        uri: &str,
        key: &str,
        value: &str,
        idempotency_key: Option<&str>,
    ) -> Result<()> {
        if let Some(token) = Self::token(uri, key, idempotency_key) {
            if self.idempotency.contains(&token) {
                return Ok(());
            }
            self.idempotency.insert(token);
        }
        self.storage
            .insert((uri.to_string(), key.to_string()), value.to_string());
        Ok(())
    }

    fn read_object(&self, uri: &str, key: &str) -> Result<Option<String>> {
        Ok(self
            .storage
            .get(&(uri.to_string(), key.to_string()))
            .cloned())
    }

    fn compare_and_swap(
        &mut self,
        uri: &str,
        key: &str,
        expect: Option<&str>,
        update: &str,
    ) -> Result<bool> {
        let entry_key = (uri.to_string(), key.to_string());
        let current = self.storage.get(&entry_key).map(|value| value.to_string());
        if current.as_deref() != expect {
            return Ok(false);
        }
        self.storage.insert(entry_key, update.to_string());
        Ok(true)
    }
}

impl Crypto for InMemoryAdapters {
    fn sign(&self, key: &str, data: &[u8]) -> Result<Vec<u8>> {
        let mut hasher = Sha256::new();
        hasher.update(key.as_bytes());
        hasher.update(data);
        Ok(hasher.finalize().to_vec())
    }

    fn verify(&self, key: &str, data: &[u8], signature: &[u8]) -> Result<bool> {
        let expected = self.sign(key, data)?;
        Ok(expected == signature)
    }

    fn hash(&self, data: &[u8]) -> Result<String> {
        let digest = Sha256::digest(data);
        Ok(format!("sha256:{}", hex::encode(digest)))
    }
}
