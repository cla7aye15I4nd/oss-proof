#!/usr/bin/env python3
"""Open defects in the differential test. Usage: expected_faults.py <name> <in> <c.out> <lean.out>.

expected-faults.txt lists, one per line, `<driver> <finding> <fault message> | <input line>`: an input on which the
verified C source has undefined behaviour that no patch fixes yet (see the findings page), so the translation must
raise `Fault.ub` with that message there while the C, which has no checks, prints a result. For each listed input
of this driver, the Lean output line must be exactly `FAULT ub <message>`; the C output line is then replaced by
it (in place), so the byte-for-byte comparison that follows covers every other input unchanged. A listed input
that is missing from the generated inputs, or on which the translation does not fault with that message, fails
the run (exit 1): the entry is stale, or the defect no longer shows.
"""
import os
import sys

name, inp, cout, lout = sys.argv[1:5]
here = os.path.dirname(os.path.abspath(__file__))
entries = []
with open(os.path.join(here, "expected-faults.txt")) as f:
    for raw in f:
        line = raw.rstrip("\n")
        if not line.strip() or line.startswith("#"):
            continue
        head, _, input_line = line.partition(" | ")
        drv, finding, msg = head.split(" ", 2)
        if drv == name:
            entries.append((finding, msg, input_line))
if not entries:
    sys.exit(0)
ins = open(inp).read().split("\n")
cs = open(cout).read().split("\n")
ls = open(lout).read().split("\n")
ok = True
for finding, msg, input_line in entries:
    idx = [i for i, l in enumerate(ins) if l == input_line]
    if not idx:
        print("EXPECTED FAULT (%s): input not generated any more: %s" % (finding, input_line[:200]))
        ok = False
        continue
    for i in idx:
        want = "FAULT ub " + msg
        if ls[i] != want:
            print("EXPECTED FAULT (%s) at input line %d: Lean printed %s" % (finding, i + 1, ls[i][:200]))
            ok = False
        else:
            print("expected fault (%s) at input line %d: %s" % (finding, i + 1, want))
            cs[i] = want
open(cout, "w").write("\n".join(cs))
sys.exit(0 if ok else 1)
