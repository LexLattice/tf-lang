seq{
  write-object(uri="res://kv/bucket", key="z", value="1");
  read-object(uri="res://kv/bucket", key="z")
}
