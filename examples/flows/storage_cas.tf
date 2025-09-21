seq{
  write-object(uri="res://kv/users", key="alice", value="v1");
  compare-and-swap(uri="res://kv/users", key="alice", expect="v0", update="v2");
  compare-and-swap(uri="res://kv/users", key="alice", expect="v1", update="v3")
}
