authorize{
  seq{
    write-object(uri="res://kv/run", key="a", value="1");
    write-object(uri="res://kv/run", key="b", value="2")
  }
}
