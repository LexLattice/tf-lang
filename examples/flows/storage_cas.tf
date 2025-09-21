seq{
  write-object(uri="res://kv/users", key="alice", value="v1", idempotency_key="init-1");
  compare-and-swap(uri="res://kv/users", key="alice", value="v2", ifMatch="mismatch");
  compare-and-swap(uri="res://kv/users", key="alice", value="v3", ifMatch="v1");
}
