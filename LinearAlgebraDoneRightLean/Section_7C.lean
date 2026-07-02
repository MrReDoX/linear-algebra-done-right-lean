import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Tactic.Linter.Style
import CompanionHelper

/-!
# Axler, *Linear Algebra Done Right* (4e) — Section 7C: Positive Operators
-/

namespace LADR.Section_7C

open scoped InnerProductSpace RealInnerProductSpace ComplexConjugate
open Module.End (HasEigenvalue)

variable {𝕜 : Type*} [RCLike 𝕜]
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [FiniteDimensional 𝕜 V]

/-! 7.34 Definition: positive operator

An operator {lit}`T ∈ ℒ(V)` is *positive* if it is self-adjoint and
{lit}`⟨Tv, v⟩ ≥ 0` for all {lit}`v`. This is mathlib's {name}`LinearMap.IsPositive`
(over a complex space the self-adjointness is automatic — 7.14). -/

omit [FiniteDimensional 𝕜 V] in
theorem isPositive_iff_symmetric_nonneg (T : V →ₗ[𝕜] V) :
    T.IsPositive ↔ LinearMap.IsSymmetric T ∧ ∀ v, 0 ≤ RCLike.re ⟪T v, v⟫_𝕜 :=
  ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩

/-! 7.36 Definition: square root

{lit}`R` is a *square root* of {lit}`T` if {lit}`R² = T`. -/

def IsSquareRoot (R T : V →ₗ[𝕜] V) : Prop := R ∘ₗ R = T

/-! 7.38 Characterizations of positive operators

Among the equivalent conditions, the direction {lit}`T = R* R ⟹ T` positive
(f ⟹ a) has a short direct proof, which we give. -/

/-- {lit}`R* R` is always a positive operator (7.38 (f) ⟹ (a)). -/
theorem adjoint_comp_self_isPositive (R : V →ₗ[𝕜] V) :
    (LinearMap.adjoint R ∘ₗ R).IsPositive := by
  constructor
  · intro x y
    simp only [LinearMap.comp_apply]
    rw [LinearMap.adjoint_inner_left, ← LinearMap.adjoint_inner_right]
  · intro x
    simp only [LinearMap.comp_apply, LinearMap.adjoint_inner_left]
    rw [inner_self_eq_norm_sq_to_K]
    simp

/-- (a) ⟹ (b): every eigenvalue of a positive operator is a nonnegative real. -/
theorem eigenvalue_nonneg {T : V →ₗ[𝕜] V} (hT : T.IsPositive) {μ : 𝕜}
    (hμ : HasEigenvalue T μ) : 0 ≤ RCLike.re μ ∧ conj μ = μ := by
  sorry

/-! 7.39 Each positive operator has a unique positive square root.

The existence of the positive square root (7.38 (d)) and its uniqueness (7.39)
run through the spectral theorem applied to {lit}`R`; in this pin the cleanest
route uses the continuous functional calculus, and their formalization here is
deferred. -/

/-! # Exercises 7C -/

/-- 7C (orthogonal projections are positive; a special case of {lit}`R* R`).
For an orthogonal projection {lit}`P` (self-adjoint idempotent), {lit}`P` is
positive. -/
theorem exercise_projection_isPositive (P : V →ₗ[𝕜] V)
    (hsa : LinearMap.adjoint P = P) (hidem : P ∘ₗ P = P) : P.IsPositive := by
  sorry

omit [FiniteDimensional 𝕜 V] in
/-- 7C.1-style: a positive operator {lit}`T` satisfies {lit}`⟨Tv, v⟩ = 0 ⟹ Tv = 0`
(via its positive square root); here the weaker fact that {lit}`T` is
self-adjoint. -/
theorem exercise_isPositive_isSymmetric {T : V →ₗ[𝕜] V} (hT : T.IsPositive) :
    LinearMap.IsSymmetric T :=
  hT.isSymmetric

end LADR.Section_7C
