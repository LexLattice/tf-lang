authorize{
  seq{
    write-object(uri="res://inmem/kv", key="alpha", value="1");
    write-object(uri="res://inmem/kv", key="beta", value="2")
  }
}
