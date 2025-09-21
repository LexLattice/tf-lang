seq{
  publish(topic="orders", key="o-1", payload="{}");
  emit-metric(name="sent")
}
