# lean4-crash-course

Source for "Lean at MC2020", a Lean 4 crash course, published at
https://apurvanakade.github.io/lean4-crash-course/.

## Layout

- `src/source/*.rst` — the course notes (Sphinx/reStructuredText). Lean code embedded in
  `.. code-block:: lean4` directives gets a "try it!" link to
  [live.lean-lang.org](https://live.lean-lang.org/) and is compile-checked against mathlib4 (see
  `src/lean_sphinx.py`).
- `lean/` — a Lake package depending on mathlib4. `lean/CrashCourse/Solutions/` holds the worked
  solutions; `lean/CrashCourse/Examples/` is generated from the course notes for compile-checking.
- `slides/` — two reveal.js slide decks (days 1 and 2).

## Building

```
cd lean && lake exe cache get && lake build   # compile-check all Lean code
cd src && make install-deps                   # first time only
cd src && make html                           # build the HTML site into src/build/html
cd src && make leantest                       # run the Lean compile-check via Sphinx
```

Pushes to `master` build and publish automatically to `gh-pages` via
`.github/workflows/publish.yml`.
