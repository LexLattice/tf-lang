authorize(scope="kms.sign"){
  seq{
    sign-data(key="k1", payload="hello");
    verify-signature(key="k1", payload="hello", signature="iKqz7ejTrflNJquQ07r9SiCDBww7zOnAFO4EpEOEfAs=")
  }
}
