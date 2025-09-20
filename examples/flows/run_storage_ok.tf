authorize{
  seq{
    write-object(uri="res://kv/bucket", key="a", value="1");
    write-object(uri="res://kv/bucket", key="b", value="2")
  }
}
