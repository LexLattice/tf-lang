# protected_write.tf (violates policy on purpose for cp2)
write-object(uri="res://kv/orders", key="order-1", value="payload")
