# syntax_error.tf (intentionally broken to surface parse error)
authorize{
  seq{
    write-object(uri="res://kv/orders", key="order-1", value="payload"
  }
}
