#!/usr/bin/env python3
"""Build both libraries, failing on errors and on every warning except `declaration uses sorry`.

Unlike `lake build --wfail`, this lets sorried blueprint nodes through. Warnings of modules
replayed from an earlier build are reported again by Lake, so they are caught too.
"""

import re
import subprocess
import sys

# Lean's messages, as Lake reports them: `warning: <file>.lean:<line>:<column>: <message>`.
WARNING = re.compile(r"^warning: \S+\.lean:\d+:\d+: (.*)")


def main():
    proc = subprocess.Popen(["lake", "build", "Coarse", "CoarseBlueprint"],
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    bad = []
    for line in proc.stdout:
        print(line, end="")
        m = WARNING.match(line)
        if m and m.group(1) != "declaration uses `sorry`":
            bad.append(line.rstrip())
    if proc.wait() != 0:
        sys.exit(proc.returncode)
    if bad:
        print("\nWarnings other than `declaration uses sorry`:", *bad, sep="\n")
        sys.exit(1)


if __name__ == "__main__":
    main()
