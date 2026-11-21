#!/usr/bin/env bash
# Runs the CakeML-compiled checker on con-leche's end-to-end fixtures and
# compares its verdict with con-leche's expected exit code
# (deps/con-leche/tests/e2e-expected.txt: 0 accept; 1 reject, 2 decline and
# 3 error are all "not accepted"; 124, a timeout, and gzipped fixtures are
# skipped).
#
# usage: release/test.sh [checker] [max-fixture-bytes] [timeout-seconds]
# CHECKER_ARGS, if set, is passed to the checker (e.g. CHECKER_ARGS=--jobs=8
# for build/con-pastel-par).
set -u
here=$(cd "$(dirname "$0")" && pwd)
bin=${1:-$here/build/con-pastel}
maxsize=${2:-1000000}
tmo=${3:-600}
fx=$here/../deps/con-leche/tests
pass=0; fail=0; skip=0
while read -r code file; do
  case "$code" in ''|\#*) continue ;; esac
  f=$fx/e2e/$file
  [ -f "$f" ] || { skip=$((skip+1)); continue; }
  # gzipped fixtures expand to gigabytes; 124 marks a timeout fixture
  if [ "$code" = 124 ] || [ "${file%.gz}" != "$file" ] || [ "$(stat -c %s "$f")" -gt "$maxsize" ]; then
    skip=$((skip+1)); continue
  fi
  # shellcheck disable=SC2086
  out=$(timeout "$tmo" "$bin" ${CHECKER_ARGS:-} < "$f" 2>/dev/null)
  st=$?
  if [ "$code" = 0 ]; then want=accepted; else want=rejected; fi
  if [ $st -eq 0 ] && [ "$out" = "$want" ]; then
    pass=$((pass+1))
  else
    fail=$((fail+1)); echo "FAIL $file: expected $want, got '${out}' (exit $st)"
  fi
done < "$fx/e2e-expected.txt"
echo "pass=$pass fail=$fail skipped=$skip"
[ $fail -eq 0 ]
