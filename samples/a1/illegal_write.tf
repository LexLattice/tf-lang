# illegal_write.tf (valid syntax; used by parser smoke + generic diag smoke)
authorize{
  seq{
    write-object(uri="res://kv/orders", key="order-1", value="payload");
  }
}
