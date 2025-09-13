CREATE TABLE meta(key TEXT PRIMARY KEY, value TEXT);
CREATE TABLE claims(
  id TEXT PRIMARY KEY,
  modality TEXT,
  jurisdiction TEXT,
  effective_from TEXT,
  effective_to TEXT,
  status TEXT,
  data TEXT
);
