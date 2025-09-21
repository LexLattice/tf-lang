seq{
  emit-metric(name="pilot.replay.start");
  pilot-replay(input="tests/data/ticks-mini.csv", slice="0:50:1", seed=42);
  emit-metric(name="pilot.strategy.momentum.start");
  pilot-strategy(strategy="momentum", seed=42);
  emit-metric(name="pilot.strategy.meanrev.start");
  pilot-strategy(strategy="mean-reversion", seed=42);
  pilot-risk(mode="exposure");
  pilot-exec;
  pilot-ledger;
  emit-metric(name="pilot.full.complete")
}
