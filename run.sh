#!/bin/sh

echo -n '' > sample.smaller.jsonl
echo '{"id":42,"name":"JD"}' >> sample.smaller.jsonl
echo '{"id":43,"name":"DJ"}' >> sample.smaller.jsonl

echo '
  {"seqno":1, "user_id":42}
  {"seqno":2, "user_id":43}
  {"seqno":3, "user_id":42}
  {"seqno":4, "user_id":43}
' |
  fgrep seqno |
  wazero \
    run \
    -env ENV_KEY_L=user_id \
    -env ENV_KEY_S=id \
    -env ENV_MAP_KEYS=id,name \
    -env ENV_MAP_VALS=uid,uname \
    -env ENV_SMALLER_JSONL=/guest.d/sample.smaller.jsonl \
    -timeout 10s \
    -mount "${PWD}:/guest.d:ro" \
    ./rs-json-join.wasm
