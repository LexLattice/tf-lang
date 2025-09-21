authorize{
  seq{
    emit-metric(name="hits", value=1);
    hash-bytes(value="payload")
  }
}
