authorize{
  seq{
    write-object(uri="res://kv/bucket", key="x", value="1");
    write-object(uri="res://kv/bucket", key="y", value="2")
  }
}
