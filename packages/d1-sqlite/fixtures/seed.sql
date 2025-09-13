INSERT INTO meta(key,value) VALUES('dataset_version','ro-mini-2025-09-09');
INSERT INTO claims VALUES ('C1','FORBIDDEN','RO','2024-01-01',NULL,'determinate','{"id":"C1","kind":"DEONTIC","modality":"FORBIDDEN","scope":{"jurisdiction":"RO"},"effective":{"from":"2024-01-01","to":null},"status":"determinate","explanation":null,"evidence":[{"source_uri":"https://gov.ro/lege-sanatate#art10","span":null,"hash":"b8395a9234b7b33300dda4a0d382ec09","rule_id":"regex.v1"}],"dataset_version":"ro-mini-2025-09-09","query_hash":"0"}');
WITH RECURSIVE cnt(x) AS (SELECT 0 UNION ALL SELECT x+1 FROM cnt WHERE x < 19)
INSERT INTO claims
SELECT 'A'||x, modality, jurisdiction, effective_from, effective_to, status,
       json_set(data,'$.id','A'||x,'$.evidence[0].hash','h'||x)
FROM cnt, (SELECT * FROM claims WHERE id='C1');
