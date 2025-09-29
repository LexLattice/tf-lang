seq{
  sign-data(key="ops", payload="{}") |> emit-metric(name="signing.start");
  emit-metric(name="signing.after") |> hash;
  hash |> hash;
}
