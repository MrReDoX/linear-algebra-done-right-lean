import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Linter.Style
import CompanionHelper

/-!
# Axler, *Linear Algebra Done Right* (4e) — Section 7B: Spectral Theorem
-/

namespace LADR.Section_7B

open scoped InnerProductSpace RealInnerProductSpace ComplexConjugate
open Module (finrank)
open Module.End (HasEigenvalue HasEigenvector)

variable {𝕜 : Type*} [RCLike 𝕜]
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [FiniteDimensional 𝕜 V]

/-! # Real Spectral Theorem -/

/-! 7.26 Invertible quadratic expressions

If {lit}`T ∈ ℒ(V)` is self-adjoint and {lit}`b, c ∈ ℝ` satisfy {lit}`b² < 4c`,
then {lit}`T² + bT + cI` is invertible. (We record the key step: it is injective,
since {lit}`⟨(T² + bT + cI)v, v⟩ > 0` for {lit}`v ≠ 0`.) -/

theorem quadratic_pos (T : V →ₗ[𝕜] V) (hT : LinearMap.IsSymmetric T) (b c : ℝ)
    (hbc : b ^ 2 < 4 * c) (v : V) (hv : v ≠ 0) :
    0 < RCLike.re ⟪(T ∘ₗ T + (b : 𝕜) • T + (c : 𝕜) • (LinearMap.id : V →ₗ[𝕜] V)) v,
      v⟫_𝕜 := by
  sorry

/-! 7.27 The minimal polynomial of a self-adjoint operator is a product of the
linear factors {lit}`(z − λ₁) ⋯ (z − λₘ)` with each {lit}`λⱼ ∈ ℝ`. This is used
to prove the real spectral theorem below; its formalization here is deferred. -/

/-! 7.29 Real spectral theorem

For {lit}`𝔽 = ℝ`, an operator {lit}`T` is self-adjoint if and only if {lit}`V`
has an orthonormal basis consisting of eigenvectors of {lit}`T` (equivalently,
{lit}`T` has a diagonal matrix with respect to some orthonormal basis).

The substantive direction — every self-adjoint operator is orthonormally
diagonalizable — is mathlib's spectral theorem, available uniformly over
{lit}`ℝ` and {lit}`ℂ` (over {lit}`ℂ` it is the self-adjoint case of the complex
spectral theorem). mathlib packages the eigenbasis as
{name}`LinearMap.IsSymmetric.eigenvectorBasis`. -/

theorem spectral_orthonormal_eigenbasis (T : V →ₗ[𝕜] V)
    (hT : LinearMap.IsSymmetric T) :
    ∃ b : OrthonormalBasis (Fin (finrank 𝕜 V)) 𝕜 V, ∀ i, ∃ μ : 𝕜, T (b i) = μ • b i :=
  ⟨hT.eigenvectorBasis rfl,
    fun i => ⟨(hT.eigenvalues rfl i : 𝕜), hT.apply_eigenvectorBasis rfl i⟩⟩

/-- The eigenvalues in the spectral decomposition are real, as expected for a
self-adjoint operator (7.12). -/
theorem spectral_eigenvalues_real (T : V →ₗ[𝕜] V) (hT : LinearMap.IsSymmetric T)
    (i : Fin (finrank 𝕜 V)) :
    T (hT.eigenvectorBasis rfl i) =
      ((hT.eigenvalues rfl i : ℝ) : 𝕜) • hT.eigenvectorBasis rfl i :=
  hT.apply_eigenvectorBasis rfl i

/-! # Complex Spectral Theorem -/

/-! 7.31 Complex spectral theorem

For {lit}`𝔽 = ℂ`, an operator {lit}`T` is normal if and only if {lit}`V` has an
orthonormal basis consisting of eigenvectors of {lit}`T`. Axler's proof runs
through Schur's theorem (6.38), which is deferred (see
{module -checked}`LinearAlgebraDoneRightLean.Section_6B`); this result is
therefore also deferred here. -/

/-! # Exercises 7B -/

/-- 7B.5 If {lit}`T` is self-adjoint (here for any {lit}`𝕜`; the real spectral
theorem is the {lit}`ℝ` case) then {lit}`T` is orthonormally diagonalizable — a
restatement of {lit}`spectral_orthonormal_eigenbasis` asked of the reader in
various concrete forms. As an exercise, show the eigenvalues are real. -/
theorem exercise_7B_eigenvalues_real (T : V →ₗ[𝕜] V)
    (hT : LinearMap.IsSymmetric T) {μ : 𝕜} (hμ : HasEigenvalue T μ) :
    conj μ = μ := by
  sorry

/-- 7B.7 If {lit}`T` is self-adjoint and {lit}`⟨Tv, v⟩ ≥ 0` structure holds, one
studies positive operators (Section 7C). Here: a self-adjoint operator with all
eigenvalues zero is the zero operator. -/
theorem exercise_7B_zero_of_eigenvalues_zero (T : V →ₗ[𝕜] V)
    (hT : LinearMap.IsSymmetric T)
    (h : ∀ i : Fin (finrank 𝕜 V), hT.eigenvalues rfl i = 0) :
    T = 0 := by
  sorry

end LADR.Section_7B
