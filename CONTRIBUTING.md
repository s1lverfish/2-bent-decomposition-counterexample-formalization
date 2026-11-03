# Checking changes

Preserve the pinned toolchain and dependencies unless intentionally updating both together. Before proposing a change, run:

```sh
lake build
python3 scripts/check_axioms.py
```

Do not replace proofs by admissions, add mathematical axioms, weaken the theorem's quantifiers, restrict the bent summands, or replace the infinite family by bounded checks. Changes to definitions or theorem statements require mathematical specification review as well as a successful Lean build. Keep downloaded packages and `.lake/` build products out of Git.
