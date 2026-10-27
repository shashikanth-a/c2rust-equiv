#!/usr/bin/env python3
"""Run every command in an Alloy file and compare with its `expect`.

usage: check_alloy.py ALLOY_JAR FILE.als
Every command must have an `expect`. A check with `expect 0` must find no counterexample; `expect 1` must find one.
"""
import json, os, subprocess, sys, tempfile

jar, spec = sys.argv[1], sys.argv[2]
out = tempfile.mkdtemp()
subprocess.run(['java', '-jar', jar, 'exec', '-f', '-o', out, '-c', '*', spec],
               check=True, capture_output=True)
status = 0
for name, cmd in json.load(open(os.path.join(out, 'receipt.json')))['commands'].items():
    found = 1 if cmd.get('solution') else 0
    # The receipt omits `expects` when it is 0.
    expects = cmd.get('expects', 0)
    ok = expects == found
    print(f"{'ok  ' if ok else 'FAIL'} {name}: {'counterexample' if found else 'none'} (expect {expects})")
    status |= not ok
sys.exit(status)
