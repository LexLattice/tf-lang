txn{
  compare-and-swap(uri="res://kv/bucket", key="x", value="1", ifMatch=0);
  write-object(uri="res://kv/bucket", key="y", value="2", idempotency_key="abc-123")
}
