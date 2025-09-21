seq{
  emit-metric(name="pilot.replay.start");
  write-object(
    uri="res://pilot-full/config",
    key="run",
    value={
      input:"tests/data/ticks-mini.csv",
      seed:42,
      slice:"0:50:1",
      strategies:["momentum","meanReversion"],
      risk:{mode:"exposure"}
    }
  );
  write-object(uri="res://pilot-full/replay", key="frames.ndjson", value={});
  write-object(uri="res://pilot-full/strategy", key="orders.ndjson", value={});
  write-object(uri="res://pilot-full/risk", key="metrics.ndjson", value={});
  emit-metric(name="pilot.exec.sent");
  publish(topic="pilot.exec.orders", key="seed-42", payload="{\"orders\":\"res://pilot-full/orders.ndjson\"}");
  write-object(uri="res://pilot-full/exec", key="fills.ndjson", value={});
  write-object(uri="res://pilot-full/ledger", key="state.json", value={});
  emit-metric(name="pilot.ledger.write")
}
