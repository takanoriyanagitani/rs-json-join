#!/bin/sh

cargo \
	build \
    --target wasm32-wasi \
    --features flat-mem-keystr-simple,std \
    --profile release-wasi
