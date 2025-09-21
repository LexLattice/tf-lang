seq{
  emit-metric(name="jobs.processed", value=1);
  publish(topic="events", key="job-1", payload="{}")
}
