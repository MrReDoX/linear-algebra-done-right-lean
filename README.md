# Lean Companion to Axler's *Linear Algebra Done Right* (4e)

A Lean 4 companion to Sheldon Axler's [*Linear Algebra Done Right*](https://linear.axler.net/) (4th edition; freely available as a [PDF](https://linear.axler.net/LADR4e.pdf)).

## What is a companion?

A Lean project that mirrors a specific math textbook: a Lean translation of all
definitions, proofs, examples, and exercises (without solutions). It contains
**no narrative** — that stays in the original text — and is meant to be:

1. read concurrently with the text;
2. cloned and worked through, replacing each `sorry` with a real proof.

The canonical existing example is Tao's *Real Analysis I* companion
([blog post](https://terrytao.wordpress.com/2025/05/31/a-lean-companion-to-analysis-i/),
[repo](https://github.com/teorth/analysis)). This project plays the same role
for Axler.

## Who is it for?

Lean familiarity is the prerequisite. Beyond that:

1. If you already know linear algebra, you're here to practice Lean and pick
   up the parts of mathlib that cover linear algebra.
2. If you don't, you learn the math alongside by reading the book.

**This companion will not teach you Lean.** Lean basics are out of scope —
if you're new to Lean, work through one of the standard introductions first:

- [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/) (chapters 1–7 are enough; later chapters go beyond what this companion needs)
- [Theorem Proving in Lean 4](https://leanprover.github.io/theorem_proving_in_lean4/)
- [Natural Number Game](https://adam.math.hhu.de/)

## Conventions

Authored under the conventions in
[companion-helper](https://github.com/rkirov/companion-helper):

- **Use mathlib directly.** Where Axler introduces a concept already in
  mathlib (`Field`, `Module`, `Submodule`, …), the companion uses the mathlib
  definition rather than redefining it. `recall` bridges Axler's axioms to
  mathlib's typeclass methods.
- **`@[avoiding …]`** from `companion-helper` marks exercises whose one-line
  mathlib solution would defeat the pedagogical point.
- No cross-imports between companions; mathlib is the only shared layer.

## On AI usage

AI generates the initial draft of each chapter from the freely available
PDF. Every draft is then reviewed and revised line-by-line by a human (with
AI assistance) — roughly 1–2 hours of focused review per subsection. More
on the human-vs-AI split as we accumulate playthroughs.

## Status

A row is *drafted* once the section's `.lean` file exists with all numbered
Axler results stated and proved and all exercises stated as `sorry`. It is
*reviewed* once a human has read it line-by-line and revised problems they
found. *Playtested* means someone (other than the author) has worked through
the section's exercises.

| Section | Drafted | Reviewed | Playtested |
|---|---|---|---|
| 1A. ℝⁿ and ℂⁿ | ✓ | ✓ | — |
| 1B. Definition of vector space | ✓ | ✓ | — |
| 1C. Subspaces | ✓ | ✓ | — |
| 2A. Span and Linear Independence | ✓ | ✓ | — |
| 2B. Bases | ✓ | ✓ | — |
| 2C. Dimension | ✓ | ✓ | — |
| 3A. Vector Space of Linear Maps | ✓ | ✓ | — |
| 3B. Null Spaces and Ranges | ✓ | ✓ | — |
| 3C. Matrices | ✓ | ✓ | — |
| 3D. Invertibility and Isomorphisms | ✓ | ✓ | — |
| 3E. Products and Quotients of Vector Spaces | ✓ | ✓ | — |
| 3F. Duality | ✓ | ✓ | — |
| 4. Polynomials | ✓ | ✓ | — |
| 5A. Invariant Subspaces | ✓ | ✓ | — |
| 5B. The Minimal Polynomial | ✓ | ✓ | — |
| 5C. Upper-Triangular Matrices | ✓ | ✓ | — |
| 5D. Diagonalizable Operators | ✓ | — | — |
| 5E. Commuting Operators | ✓ | — | — |
| 6A. Inner Products and Norms | ✓ | — | — |
| 6B. Orthonormal Bases | ✓ | — | — |
| 6C. Orthogonal Complements and Minimization Problems | ✓ | — | — |
| 7A. Self-Adjoint and Normal Operators | ✓ | — | — |
| 7B. Spectral Theorem | ✓ | — | — |
| 7C. Positive Operators | ✓ | — | — |
| 7D. Isometries, Unitary Operators, and Matrix Factorization | ✓* | — | — |
| 7E. Singular Value Decomposition | ✓* | — | — |
| 7F. Consequences of Singular Value Decomposition | ✓* | — | — |
| 8A. Generalized Eigenvectors and Nilpotent Operators | ✓* | — | — |
| 8B. Generalized Eigenspace Decomposition | ✓* | — | — |
| 8C. Consequences of Generalized Eigenspace Decomposition | ✓* | — | — |
| 8D. Trace | ✓ | — | — |
| 9A. Bilinear Forms and Quadratic Forms | ✓ | — | — |
| 9B. Alternating Multilinear Forms | ✓ | — | — |
| 9C. Determinants | ✓* | — | — |
| 9D. Tensor Products | ✓* | — | — |

The whole book (Chapters 1–9) is now drafted. In every section, exercises
remain as `sorry` and each numbered Axler result is either stated and proved or,
where it needs machinery genuinely absent from the pinned mathlib, stated with
an explicit prose note explaining the deferral — there are no silent `sorry`s on
numbered results.

\* A `✓*` marks a section that prose-defers one or more numbered results. These
deferrals cluster around a few missing pieces: the *matrix-of-a-basis normal-form
theory* (strictly-upper-triangular nilpotents, block-diagonal and Jordan forms —
8A 8.18(c), 8B 8.31/8.35–8.38, 8C 8.41/8.44–8.46); *matrix factorizations* (QR
and Cholesky in 7D, the matrix SVD `A = B D C*` and pseudoinverse SVD in 7E, best
rank-`k` approximation and the operator-norm ↔ largest-singular-value bridge in
7F); *inner products on tensor products* and the dimension theory of
`PiTensorProduct` (9D 9.80–9.83, 9.87/9.89/9.90); *measure-theoretic volume*
(7F 7.108–7.111, and the volume/determinant results in 9C 9.58–9.61); and a
handful of purely numeric worked examples. The Chapters 1–7C sections carry no
`✓*` — every numbered result there is fully proved.

## Building

```bash
lake update mathlib && lake exe cache get   # first time only
lake build
```
Toolchain: `leanprover/lean4:v4.30.0-rc2`. Mathlib is pinned at `v4.30.0-rc2`.

## Contributing

PRs fixing typos or improving comments are welcome. Please **don't** send PRs
to `main` filling in the `sorry`s — they're the exercises. Solutions in your
own fork (or a separate branch here) are fine; they just shouldn't land on
`main`.

## License

Apache-2.0.
