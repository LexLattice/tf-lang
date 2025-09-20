authorize{
  par{
    write-object(uri="res://kv/bucket", key="x", value="1");
    write-object(uri="res://kv/other", key="y", value="2")
  }
}
