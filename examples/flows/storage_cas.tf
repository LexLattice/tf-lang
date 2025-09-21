seq{
  write-object(uri="res://kv/users", key="alice", value="pending", idempotency_key="init");
  compare-and-swap(uri="res://kv/users", key="alice", value="archived", if_match="inactive");
  compare-and-swap(uri="res://kv/users", key="alice", value="active", if_match="pending");
  read-object(uri="res://kv/users", key="alice")
}
