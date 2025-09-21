seq{
  emit-metric(name="pipeline.run", value=1);
  publish(topic="events", key="run-1", payload="{\"ok\":true}");
}
