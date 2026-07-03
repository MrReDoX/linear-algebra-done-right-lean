import LinearAlgebraDoneRightLean.Section_1A
import LinearAlgebraDoneRightLean.Section_1B
import LinearAlgebraDoneRightLean.Section_1C
import LinearAlgebraDoneRightLean.Section_2A
import LinearAlgebraDoneRightLean.Section_2B
import LinearAlgebraDoneRightLean.Section_2C
import LinearAlgebraDoneRightLean.Section_3A
import LinearAlgebraDoneRightLean.Section_3B
import LinearAlgebraDoneRightLean.Section_3C
import LinearAlgebraDoneRightLean.Section_3D
import LinearAlgebraDoneRightLean.Section_3E
import LinearAlgebraDoneRightLean.Section_3F
import LinearAlgebraDoneRightLean.Chapter_4
import LinearAlgebraDoneRightLean.Section_5A
import LinearAlgebraDoneRightLean.Section_5B
import LinearAlgebraDoneRightLean.Section_5C
import LinearAlgebraDoneRightLean.Section_5D
import LinearAlgebraDoneRightLean.Section_5E
import LinearAlgebraDoneRightLean.Section_6A
import LinearAlgebraDoneRightLean.Section_6B
import LinearAlgebraDoneRightLean.Section_6C
import LinearAlgebraDoneRightLean.Section_7A
import LinearAlgebraDoneRightLean.Section_7B
import LinearAlgebraDoneRightLean.Section_7C
import LinearAlgebraDoneRightLean.Section_7D
import LinearAlgebraDoneRightLean.Section_8A
import LinearAlgebraDoneRightLean.Section_8D
import LinearAlgebraDoneRightLean.Section_9B
import LinearAlgebraDoneRightLean.Section_9C

/-!
# Lean Companion to Axler's *Linear Algebra Done Right* (4e)

A Lean 4 companion to Sheldon Axler's
[*Linear Algebra Done Right*](https://linear.axler.net/) (4th edition;
freely available as a [PDF](https://linear.axler.net/LADR4e.pdf)).

The companion mirrors the textbook section by section: definitions and proven
theorems are translated into Lean, and exercises are stated as theorems with
{lit}`sorry`. Where a one-line mathlib lemma would defeat the pedagogical
point of an exercise, the exercise is marked with {lit}`@[avoiding …]` from
[companion-helper](https://github.com/rkirov/companion-helper).

## Modules

- {module}`LinearAlgebraDoneRightLean.Section_1A` — ℝⁿ and ℂⁿ
- {module}`LinearAlgebraDoneRightLean.Section_1B` — Definition of vector space
- {module}`LinearAlgebraDoneRightLean.Section_1C` — Subspaces
- {module}`LinearAlgebraDoneRightLean.Section_2A` — Span and Linear Independence
- {module}`LinearAlgebraDoneRightLean.Section_2B` — Bases
- {module}`LinearAlgebraDoneRightLean.Section_2C` — Dimension
- {module}`LinearAlgebraDoneRightLean.Section_3A` — Vector Space of Linear Maps
- {module}`LinearAlgebraDoneRightLean.Section_3B` — Null Spaces and Ranges
- {module}`LinearAlgebraDoneRightLean.Section_3C` — Matrices
- {module}`LinearAlgebraDoneRightLean.Section_3D` — Invertibility and Isomorphisms
- {module}`LinearAlgebraDoneRightLean.Section_3E` — Products and Quotients of Vector Spaces
- {module}`LinearAlgebraDoneRightLean.Section_3F` — Duality
- {module}`LinearAlgebraDoneRightLean.Chapter_4` — Polynomials
- {module}`LinearAlgebraDoneRightLean.Section_5A` — Invariant Subspaces
- {module}`LinearAlgebraDoneRightLean.Section_5B` — The Minimal Polynomial
- {module}`LinearAlgebraDoneRightLean.Section_5C` — Upper-Triangular Matrices
- {module}`LinearAlgebraDoneRightLean.Section_5D` — Diagonalizable Operators
- {module}`LinearAlgebraDoneRightLean.Section_5E` — Commuting Operators
- {module}`LinearAlgebraDoneRightLean.Section_6A` — Inner Products and Norms
- {module}`LinearAlgebraDoneRightLean.Section_6B` — Orthonormal Bases
- {module}`LinearAlgebraDoneRightLean.Section_6C` — Orthogonal Complements and Minimization Problems
- {module}`LinearAlgebraDoneRightLean.Section_7A` — Self-Adjoint and Normal Operators
- {module}`LinearAlgebraDoneRightLean.Section_7B` — Spectral Theorem
- {module}`LinearAlgebraDoneRightLean.Section_7C` — Positive Operators
-/
