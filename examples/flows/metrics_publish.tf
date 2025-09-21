seq{
  emit-metric(name="flows.processed", value=2);
  publish(topic="flows", key="demo", payload="{\"ok\":true}")
}
