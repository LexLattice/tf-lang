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
}

pub trait Crypto {
    fn sign(&mut self, key_id: &str, payload: &[u8]) -> Result<Vec<u8>>;
    fn verify(&mut self, key_id: &str, payload: &[u8], signature: &[u8]) -> Result<bool>;
    fn hash(&mut self, payload: &[u8]) -> Result<String>;
}

fn keyed_digest(key_id: &str, payload: &[u8]) -> Vec<u8> {
    let mut hasher = Sha256::new();
    hasher.update(key_id.as_bytes());
    hasher.update(payload);
    hasher.finalize().to_vec()
}

#[derive(Clone, Debug, Default)]
pub struct PublishedMessage {
    pub topic: String,
    pub key: String,
    pub payload: String,
}

#[derive(Clone, Debug, Default)]
pub struct InMemoryAdapters {
    published: Vec<PublishedMessage>,
    storage: HashMap<String, HashMap<String, String>>,
    idempotency_tokens: HashSet<String>,
    metrics: HashMap<String, f64>,
}

impl InMemoryAdapters {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn published(&self) -> &[PublishedMessage] {
        &self.published
    }

    pub fn storage_snapshot(&self) -> HashMap<String, HashMap<String, String>> {
        self.storage.clone()
    }

    pub fn metric_totals(&self) -> HashMap<String, f64> {
        self.metrics.clone()
    }

    pub fn reset(&mut self) {
        self.published.clear();
        self.storage.clear();
        self.idempotency_tokens.clear();
        self.metrics.clear();
    }

    fn idempotency_token(uri: &str, key: &str, idempotency: Option<&str>) -> Option<String> {
        idempotency
            .filter(|value| !value.is_empty())
            .map(|value| format!("{uri}#{key}#{value}"))
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
        let increment = value.unwrap_or(1.0);
        let entry = self.metrics.entry(name.to_string()).or_insert(0.0);
        *entry += increment;
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
        let bucket = self
            .storage
            .entry(uri.to_string())
            .or_insert_with(HashMap::new);

        if let Some(token) = Self::idempotency_token(uri, key, idempotency_key) {
            if self.idempotency_tokens.contains(&token) {
                return Ok(());
            }
            self.idempotency_tokens.insert(token);
        }

        bucket.insert(key.to_string(), value.to_string());
        Ok(())
    }
}

impl Crypto for InMemoryAdapters {
    fn sign(&mut self, key_id: &str, payload: &[u8]) -> Result<Vec<u8>> {
        Ok(keyed_digest(key_id, payload))
    }

    fn verify(&mut self, key_id: &str, payload: &[u8], signature: &[u8]) -> Result<bool> {
        Ok(keyed_digest(key_id, payload) == signature)
    }

    fn hash(&mut self, payload: &[u8]) -> Result<String> {
        let mut hasher = Sha256::new();
        hasher.update(payload);
        Ok(format!("sha256:{:x}", hasher.finalize()))
    }
}
