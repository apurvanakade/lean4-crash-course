# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

**Keep this file up to date.** Whenever a change alters something this file describes (build/deploy process,
repo layout, tooling, conventions), update the relevant section in the same commit rather than letting it go
stale.

## Repository overview

This repo (despite its name) contains **"Lean at MC2020"**, a Lean 3 (not Lean 4) crash course written for
Mathcamp 2020. Source lives on the `master` branch as reStructuredText (`.rst`) files that Sphinx compiles into a
static HTML site published on the `gh-pages` branch.

- `master` — the actual source: Lean exercises embedded in `.rst` course notes, plus the Sphinx build tooling.
- `gh-pages` — build output only (generated HTML, `slides/`, `static/`, `_static`). Do not hand-edit generated
  files here; regenerate them from `master` instead.

## Repo layout (master branch)

- `src/source/*.rst` — the course content, one file per day (`day1.rst` … `day5.rst`) plus standalone
  `introduction.rst`, `symbols.rst`, `tactics.rst`, and per-exercise `hint_*.rst` files.
- `src/source/solutions/*.lean` — worked solutions referenced from the hint files.
- `src/source/conf.py` — Sphinx config; registers the custom `lean_sphinx` extension.
- `src/lean_sphinx.py` — custom Sphinx extension/builder for this project (see below).
- `src/Makefile`, `src/html-make.sh` — build entry points.
- `leanpkg.toml` / `leanpkg.path` / `src/leanpkg.toml` — Lean package manifests pinning
  `leanprover-community/lean:3.15.0` and a specific `mathlib` commit.
- `game_config.toml` — config for an (apparently unfinished/experimental) "Lean game" world/level structure;
  not wired into the Sphinx build.

## Building the docs

From `src/`:

```sh
make clean html      # build HTML into src/build/html
```

or, per `html-make.sh`:

```sh
make clean html
open build/html/index.html
```

First-time Python environment setup (creates a `.venv` and installs Sphinx + a Pygments build with Lean syntax
highlighting):

```sh
make install-deps
```

Publishing to `gh-pages` is automated via [.github/workflows/publish.yml](.github/workflows/publish.yml): on every
push to `master`, CI runs `leantest`, builds the HTML site (and a PDF, best-effort), assembles it with `slides/`
into `_site/`, and deploys that to the `gh-pages` branch using `peaceiris/actions-gh-pages`. No manual copy step
is needed.

There are two extra custom Sphinx builders defined in `lean_sphinx.py`, invoked the same way as `html`:

- `make examples` — extracts every `code-block:: lean` into a standalone `.lean` file under `build/examples/`,
  mirroring the doc/name structure (used for the "try it!" links and for compiling examples independently).
- `make leantest` — extracts the same code blocks and runs `lean --make` over them, failing the build if any
  Lean snippet has a compile error. Use this to validate that exercise code (not just prose) is well-formed
  Lean 3.

## The `lean_sphinx` extension (`src/lean_sphinx.py`)

This is the key piece of non-obvious architecture: it's what turns plain `.. code-block:: lean` directives into
interactive, testable exercises.

- Every `code-block:: lean` gets wrapped with a **"try it!" link** to the Lean Web Editor
  (`leanprover-community.github.io/lean-web-editor`), URL-encoding the full snippet.
- A code block can be named via the `:name:` option (e.g. `:name: exact_intros_examples`); this name becomes
  the filename when extracted by the `examples`/`leantest` builders. Unnamed blocks get a name derived from
  their line number.
- **`--BEGIN--` / `--END--` markers** inside a Lean code block let you show setup code (imports, `noncomputable
  theory`, etc.) in the raw source used for testing/try-it, while only rendering the code between the markers
  in the actual HTML output. When editing exercises, keep this convention: boilerplate outside `--BEGIN--`/
  `--END--`, the exercise itself inside.
- Exercises are written with `sorry,` placeholders; the `leantest` builder will NOT fail on `sorry` (it's a
  valid — if incomplete — proof), so it only catches genuine syntax/type errors, not "exercise not yet solved."

## Content conventions

- All Lean code in this repo is **Lean 3 syntax** (`begin...end,` tactic blocks, commas after every tactic,
  `import tactic`, `open_locale classical`), not Lean 4. Do not "modernize" snippets to Lean 4 syntax.
- Course notes are pedagogical prose aimed at students learning type theory for the first time — matching tone
  (informal, second-person, worked examples before exercises) matters more than terseness when editing `.rst`
  files.
- Hint files (`hint_1_*.rst`, `hint_2_*.rst`, `hint_3_*.rst`) are progressive: hint 1 is a nudge, later hints
  give away more, and the corresponding file in `src/source/solutions/` has the full solution. Keep this
  escalation structure when adding new hints.
