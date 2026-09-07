#!/bin/sh
set -eu
cd "$(dirname "$0")/.."
opam exec -- dunecho build
_build/default/test/kernel_test.exe
_build/default/test/binding_test.exe
node scripts/e2e.mjs
