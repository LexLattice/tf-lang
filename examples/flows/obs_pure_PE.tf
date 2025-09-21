authorize{
  seq{
    hash-bytes(value="payload");
    emit-metric(name="hits", value=1)
  }
}
