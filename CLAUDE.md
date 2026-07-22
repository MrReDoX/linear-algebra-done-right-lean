# CLAUDE.md

Autoformalization of *Linear Algebra Done Right* (4e, Axler) in Lean 4 / mathlib.

## Review patterns

When reviewing a section, or when asked to "apply review patterns to Section X",
**read [`REVIEW_PATTERNS.md`](REVIEW_PATTERNS.md) first** and run each pattern's
detector over the section file. That file is the catalog of recurring
autoformalization issues (over-specialized statements, ad-hoc statements that
should use mathlib idioms, unformalized examples, mis-stated/missing exercises,
etc.) with detectors and standard fixes. Keep it up to date as new patterns appear.

## Layout

- `LinearAlgebraDoneRightLean/Section_*.lean` — one file per book section.
- `LADR4e.pdf` — the source text; check exercise/example statements against it.
- `README.md` — per-section progress table.
- `formalization.yaml` — mathlib-initiative self-reporting metadata.
