read-object(uri="res://kv/users", key="alice") |> transform(fn="setField", field="status", value="active") |> compare-and-swap(uri="res://kv/users", key="alice")
