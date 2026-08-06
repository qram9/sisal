#!/usr/bin/env python3
"""Cross-tabulate Sisal constructs against the LOOP FORM they appear in.

Why: `value of catenate` was rejected on a for-initial for a long time and
nobody noticed, because all 97 uses of catenate in the e2e corpus sat in a
FORALL and not one in a for-initial.  The gap was never worked around -- it was
never exercised.  A construct that is well covered in one loop form and absent
in the other is where the next such blocker hides, so it is worth being able to
ask the question directly.

    python3 test/e2e/audit_coverage.py [dir ...]     (default: test/e2e)

A "<-- NO sequential coverage" row is not a bug by itself.  It says only that
nothing tests that pairing, so whether it works is unknown until probed:
compile a minimal case and compare against OSC.  Some pairings are legitimately
absent -- argmax/argmin need a loop INDEX to report, which a sequential loop
does not have, and they are our APL extension rather than Sisal 1.2 (OSC does
not know the name at all).

The scan is deliberately crude -- a line-based tracker of `for` / `for initial`
/ `end for` nesting.  It is a signpost, not a parser.  Two mistakes it made
while being written, both of which produced CONFIDENT WRONG NUMBERS rather than
obvious breakage, are now guarded and worth knowing about if you extend it:

  * `\bfor\b` matches the `for` inside `end for`, so a closer pushed a frame and
    then popped the one it had just pushed.  The real loop was never closed and
    every attribution after it in the file was shifted.  Closers are stripped
    before openers are matched.  A file whose stack does not return to empty at
    EOF is the symptom.
  * Attribution must happen BEFORE closers are processed.  A clause written on
    one line -- `returns value of product i end for` -- would otherwise be
    credited to the enclosing scope, inventing a gap where the coverage exists.
    That single bug reported product/least/greatest as having no sequential
    coverage when forinit_reduce_dv had covered them all along.
"""
import re, sys, pathlib, collections

CONSTRUCTS = [
    ("value of sum",      r'\bvalue\s+of\s+sum\b'),
    ("value of product",  r'\bvalue\s+of\s+product\b'),
    ("value of least",    r'\bvalue\s+of\s+least\b'),
    ("value of greatest", r'\bvalue\s+of\s+greatest\b'),
    ("value of catenate", r'\bvalue\s+of\s+catenate\b'),
    ("value of argmax",   r'\bvalue\s+of\s+argmax\b'),
    ("value of argmin",   r'\bvalue\s+of\s+argmin\b'),
    ("array_dv of",       r'\barray_dv\s+of\b'),
    ("array of",          r'\barray\s+of\b'),
    ("stream of",         r'\bstream\s+of\b'),
    ("value of <plain>",  r'\bvalue\s+of\s+(?!sum|product|least|greatest|catenate|argmax|argmin)\S'),
    ("when mask",         r'\bwhen\b'),
    ("unless mask",       r'\bunless\b'),
]

# Generator syntax: only meaningful in a forall's range clause.  A for-initial
# has no generator, so a zero in that column is structural, not a gap -- they
# are tallied for context but never flagged.
GENERATOR_ONLY = [
    ("cross",             r'\bcross\b'),
    ("dot",               r'\bdot\b'),
    ("at (scatter idx)",  r'\bat\s+\w'),
]
ALL = CONSTRUCTS + GENERATOR_ONLY

def scan(dirs):
    tally = collections.defaultdict(collections.Counter)
    for d in dirs:
        for f in sorted(pathlib.Path(d).glob("*.sis")):
            stack = []   # reset per file; residue must not cross files
            for line in f.read_text(errors="replace").splitlines():
                code = line.split('%')[0]          # strip Sisal comments
                # `end for` must be removed BEFORE looking for openers: \bfor\b
                # matches the `for` inside `end for`, so a closer would push a
                # frame and then pop the one it just pushed, leaving the real
                # loop unclosed and skewing everything after it in the file.
                openers = re.sub(r'\bend\s+for\b', ' ', code, flags=re.I)
                for m in re.finditer(r'\bfor\b(\s+initial\b)?', openers, re.I):
                    stack.append('for-initial' if m.group(1) else 'forall')
                # Attribute BEFORE closing: `returns value of product i end for`
                # puts the whole clause and its `end for` on one line, so popping
                # first would credit the construct to the ENCLOSING scope (or to
                # nothing at all) and report a false gap.
                if stack:
                    kind = stack[-1]                # innermost enclosing loop
                    for name, pat in ALL:
                        if re.search(pat, code, re.I):
                            tally[name][kind] += 1
                for _ in re.finditer(r'\bend\s+for\b', code, re.I):
                    if stack: stack.pop()
    return tally

def main():
    dirs = sys.argv[1:] or ["test/e2e"]
    t = scan(dirs)
    print(f"{'construct':22} {'forall':>7} {'for-initial':>12}   note")
    print("-" * 60)
    for name, _ in CONSTRUCTS:
        fa, fi = t[name]['forall'], t[name]['for-initial']
        note = ""
        if fa and not fi:   note = "<-- NO sequential coverage"
        elif fi and not fa: note = "<-- no forall coverage"
        elif not fa and not fi: note = "<-- absent entirely"
        print(f"{name:22} {fa:>7} {fi:>12}   {note}")
    print()
    print("generator-only (a for-initial has no range clause; 0 is structural):")
    for name, _ in GENERATOR_ONLY:
        fa, fi = t[name]['forall'], t[name]['for-initial']
        print(f"{name:22} {fa:>7} {fi:>12}")

if __name__ == "__main__":
    main()
