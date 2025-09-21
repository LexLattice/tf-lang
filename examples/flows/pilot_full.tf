seq{
  emit-metric(name="pilot.replay.start");
  publish(topic="pilot.replay.frames", key="seed=42:slice=0:50:1", payload="bootstrap");
  emit-metric(name="pilot.strategy.momentum.done");
  publish(topic="pilot.strategy.orders", key="momentum", payload="bootstrap");
  emit-metric(name="pilot.strategy.mean_reversion.done");
  publish(topic="pilot.strategy.orders", key="mean_reversion", payload="bootstrap");
  emit-metric(name="pilot.risk.exposure.done");
  publish(topic="pilot.risk.metrics", key="exposure", payload="bootstrap");
  emit-metric(name="pilot.exec.sent");
  publish(topic="pilot.exec.orders", key="all", payload="bootstrap");
  write-object(uri="res://pilot-full/ledger", key="state", value="bootstrap");
  write-object(uri="res://pilot-full/ledger", key="digests", value="bootstrap");
  emit-metric(name="pilot.ledger.write")
}
