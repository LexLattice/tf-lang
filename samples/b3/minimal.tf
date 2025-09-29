# Minimal sample flow for tf-run-wasm
# Each line maps to a primitive executed by the host shim.
tf:pure/identity@1 return identity
tf:resource/write-object@1 persist payload
