seq{
  emit-metric(name="pilot.replay.start");
  read-object(uri="res://pilot-full/state", key="initial.json");
  write-object(uri="res://pilot-full/replay", key="frames.ndjson", value="__PILOT_FULL::FRAMES__");
  emit-metric(name="pilot.strategy.momentum.start");
  publish(topic="pilot.orders.momentum", key="momentum", payload="__PILOT_FULL::ORDERS_MOMENTUM__");
  emit-metric(name="pilot.strategy.mean-reversion.start");
  publish(topic="pilot.orders.mean-reversion", key="mean-reversion", payload="__PILOT_FULL::ORDERS_MEAN_REVERSION__");
  write-object(uri="res://pilot-full/orders", key="combined.ndjson", value="__PILOT_FULL::ORDERS_COMBINED__");
  emit-metric(name="pilot.risk.start");
  write-object(uri="res://pilot-full/risk", key="metrics.ndjson", value="__PILOT_FULL::RISK__");
  emit-metric(name="pilot.exec.start");
  write-object(uri="res://pilot-full/fills", key="fills.ndjson", value="__PILOT_FULL::FILLS__");
  write-object(uri="res://pilot-full/state", key="state.json", value="__PILOT_FULL::STATE__");
  emit-metric(name="pilot.ledger.write")
}
