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
  refine ⟨?_, hT.isSymmetric.conj_eigenvalue_eq_self hμ⟩
  obtain ⟨v, hTv, hv⟩ := hμ.exists_hasEigenvector
  have hmem : T v = μ • v := Module.End.mem_eigenspace_iff.mp hTv
  have hpos : 0 ≤ RCLike.re ⟪T v, v⟫_𝕜 := hT.2 v
  rw [hmem, inner_smul_left, inner_self_eq_norm_sq_to_K,
    hT.isSymmetric.conj_eigenvalue_eq_self hμ, ← RCLike.ofReal_pow, mul_comm,
    RCLike.re_ofReal_mul] at hpos
  have hvnorm : 0 < ‖v‖ ^ 2 := by positivity
  exact (mul_nonneg_iff_of_pos_left hvnorm).mp hpos

/-! 7.38 (b) ⟹ (d) Every positive operator has a positive square root.

We build {lit}`R` acting as {lit}`√λ` on each {lit}`T`-eigenvector (from the
spectral theorem's orthonormal eigenbasis), and check {lit}`R` is positive and
{lit}`R² = T`. -/

theorem exists_positive_sqrt {T : V →ₗ[𝕜] V} (hT : T.IsPositive) :
    ∃ R : V →ₗ[𝕜] V, R.IsPositive ∧ R ∘ₗ R = T := by
  set n := Module.finrank 𝕜 V
  set hs := hT.isSymmetric
  set b := hs.eigenvectorBasis (rfl : Module.finrank 𝕜 V = n) with hb
  set μ := hs.eigenvalues (rfl : Module.finrank 𝕜 V = n) with hμ
  have hμnn : ∀ i, 0 ≤ μ i := by
    intro i
    have hev : HasEigenvalue T ((μ i : ℝ) : 𝕜) :=
      hs.hasEigenvalue_eigenvalues (rfl : Module.finrank 𝕜 V = n) i
    have := (eigenvalue_nonneg hT hev).1
    rwa [RCLike.ofReal_re] at this
  set R := b.toBasis.constr 𝕜 (fun i => (Real.sqrt (μ i) : 𝕜) • b i) with hR
  have hRb : ∀ i, R (b i) = (Real.sqrt (μ i) : 𝕜) • b i := by
    intro i
    have h1 : R (b.toBasis i) = (Real.sqrt (μ i) : 𝕜) • b i := by
      rw [hR]; simp only [Module.Basis.constr_basis]
    rwa [OrthonormalBasis.coe_toBasis] at h1
  have hRsym : LinearMap.IsSymmetric R := by
    rw [LinearMap.isSymmetric_iff_isSelfAdjoint, isSelfAdjoint_iff, LinearMap.star_eq_adjoint,
      eq_comm, LinearMap.eq_adjoint_iff_basis b.toBasis b.toBasis]
    intro i j
    simp only [OrthonormalBasis.coe_toBasis, hRb, inner_smul_left, inner_smul_right,
      RCLike.conj_ofReal]
    rcases eq_or_ne i j with h | h
    · subst h; rfl
    · rw [b.orthonormal.2 h]; ring
  refine ⟨R, ⟨hRsym, ?_⟩, ?_⟩
  · intro x
    have hRx : R x = ∑ i, (⟪b i, x⟫_𝕜 * (Real.sqrt (μ i) : 𝕜)) • b i := by
      conv_lhs => rw [← b.sum_repr' x]
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, hRb, smul_smul]
    rw [hRx, sum_inner, map_sum]
    refine Finset.sum_nonneg fun i _ => ?_
    have hterm : ⟪(⟪b i, x⟫_𝕜 * (Real.sqrt (μ i) : 𝕜)) • b i, x⟫_𝕜
        = ((Real.sqrt (μ i) * ‖⟪b i, x⟫_𝕜‖ ^ 2 : ℝ) : 𝕜) := by
      rw [inner_smul_left,
        show conj (⟪b i, x⟫_𝕜 * (Real.sqrt (μ i) : 𝕜)) = conj ⟪b i, x⟫_𝕜 * (Real.sqrt (μ i) : 𝕜) by
          rw [map_mul, RCLike.conj_ofReal],
        mul_right_comm, RCLike.conj_mul]
      push_cast; ring
    rw [hterm, RCLike.ofReal_re]
    positivity
  · apply b.toBasis.ext
    intro i
    simp only [LinearMap.comp_apply, OrthonormalBasis.coe_toBasis]
    rw [hRb, map_smul, hRb, smul_smul]
    rw [show (Real.sqrt (μ i) : 𝕜) * (Real.sqrt (μ i) : 𝕜) = ((μ i : ℝ) : 𝕜) by
      rw [← RCLike.ofReal_mul, Real.mul_self_sqrt (hμnn i)]]
    rw [← hs.apply_eigenvectorBasis (rfl : Module.finrank 𝕜 V = n) i]

/-! 7.39 The positive square root is unique. Its formalization (Axler's argument
via the spectral decomposition of the square root) is deferred. -/

/-! # Exercises 7C -/

/-- 7C (orthogonal projections are positive; a special case of {lit}`R* R`).
For an orthogonal projection {lit}`P` (self-adjoint idempotent), {lit}`P` is
positive. -/
theorem exercise_projection_isPositive (P : V →ₗ[𝕜] V)
    (hsa : LinearMap.adjoint P = P) (hidem : P ∘ₗ P = P) : P.IsPositive := by
  have h : LinearMap.adjoint P ∘ₗ P = P := by rw [hsa, hidem]
  rw [← h]; exact adjoint_comp_self_isPositive P

omit [FiniteDimensional 𝕜 V] in
/-- 7C.1-style: a positive operator {lit}`T` satisfies {lit}`⟨Tv, v⟩ = 0 ⟹ Tv = 0`
(via its positive square root); here the weaker fact that {lit}`T` is
self-adjoint. -/
theorem exercise_isPositive_isSymmetric {T : V →ₗ[𝕜] V} (hT : T.IsPositive) :
    LinearMap.IsSymmetric T :=
  hT.isSymmetric

end LADR.Section_7C
