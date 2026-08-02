# crash_course

Lean 4 / mathlib4 companion package for the "Lean at MC2020" course notes in `../src`.

- `CrashCourse/Solutions/` — worked solutions ported from the old Lean 3 answer key.
- `CrashCourse/Examples/` — Lean snippets extracted from the course's `.rst` files, compiled here
  by Sphinx's custom `leantest` builder (see `../src/lean_sphinx.py`) as the correctness check for
  every exercise shown on the site.

To build: `lake exe cache get && lake build`.
