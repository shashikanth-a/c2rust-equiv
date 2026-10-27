#!/bin/sh
# Model-check every spec configuration and compare with its expected result.
# usage: specs/check.sh path/to/tla2tools.jar
set -u
jar=${1:?path to tla2tools.jar}
cd "$(dirname "$0")"
status=0
for cfg in *.cfg; do
    spec=$(echo "$cfg" | sed -E 's/(NoGuard|Limits|Targeted)?\.cfg$//').tla
    if head -1 "$cfg" | grep -q "Must fail"; then want=fail; else want=pass; fi
    if java -XX:+UseParallelGC -cp "$jar" tlc2.TLC -config "$cfg" -workers auto -deadlock \
        -cleanup -metadir "${TMPDIR:-/tmp}/tlc-$$" "$spec" > "${TMPDIR:-/tmp}/tlc-$$.log" 2>&1; then
        got=pass
    else
        got=fail
    fi
    if [ "$got" = "$want" ]; then echo "ok   $cfg ($want)"; else echo "FAIL $cfg: expected $want, got $got"; status=1; fi
done
exit $status
