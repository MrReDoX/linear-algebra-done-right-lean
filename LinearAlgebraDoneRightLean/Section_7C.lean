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

/-! 7.39 Each positive operator has a *unique* positive square root.

Key step: a positive square root {lit}`S` of {lit}`T` sends each
{lit}`c`-eigenvector {lit}`w` of {lit}`T` to {lit}`√c · w`, because writing
{lit}`w` in {lit}`S`'s orthonormal eigenbasis forces every contributing
{lit}`S`-eigenvalue {lit}`σ` to satisfy {lit}`σ² = c`. -/

theorem sqrt_eigenvector {S : V →ₗ[𝕜] V} (hS : S.IsPositive) {w : V} {c : ℝ} (_hc : 0 ≤ c)
    (hw : (S ∘ₗ S) w = (c : 𝕜) • w) : S w = (Real.sqrt c : 𝕜) • w := by
  set n := Module.finrank 𝕜 V
  set hSs := hS.isSymmetric
  set e := hSs.eigenvectorBasis (rfl : Module.finrank 𝕜 V = n) with he
  set σ := hSs.eigenvalues (rfl : Module.finrank 𝕜 V = n) with hσ
  have hσnn : ∀ i, 0 ≤ σ i := by
    intro i
    have hev : HasEigenvalue S ((σ i : ℝ) : 𝕜) :=
      hSs.hasEigenvalue_eigenvalues (rfl : Module.finrank 𝕜 V = n) i
    have := (eigenvalue_nonneg hS hev).1
    rwa [RCLike.ofReal_re] at this
  have hSe : ∀ i, S (e i) = (σ i : 𝕜) • e i :=
    fun i => hSs.apply_eigenvectorBasis (rfl : Module.finrank 𝕜 V = n) i
  apply e.repr.injective
  ext i
  rw [OrthonormalBasis.repr_apply_apply, OrthonormalBasis.repr_apply_apply]
  have hSw : ⟪e i, S w⟫_𝕜 = (σ i : 𝕜) * ⟪e i, w⟫_𝕜 := by
    rw [← hSs (e i) w, hSe, inner_smul_left, RCLike.conj_ofReal]
  have hSSw : (σ i : 𝕜) ^ 2 * ⟪e i, w⟫_𝕜 = (c : 𝕜) * ⟪e i, w⟫_𝕜 := by
    have h1 : ⟪e i, (S ∘ₗ S) w⟫_𝕜 = (σ i : 𝕜) ^ 2 * ⟪e i, w⟫_𝕜 := by
      rw [LinearMap.comp_apply, ← hSs (e i) (S w), hSe, inner_smul_left, RCLike.conj_ofReal, hSw]
      ring
    rw [hw, inner_smul_right] at h1
    linear_combination -h1
  have hcoef : (σ i : 𝕜) * ⟪e i, w⟫_𝕜 = (Real.sqrt c : 𝕜) * ⟪e i, w⟫_𝕜 := by
    rcases eq_or_ne (⟪e i, w⟫_𝕜) 0 with h0 | h0
    · rw [h0, mul_zero, mul_zero]
    · have hsq : (σ i) ^ 2 = c := by
        have hz : ((σ i : 𝕜) ^ 2 - (c : 𝕜)) * ⟪e i, w⟫_𝕜 = 0 := by
          rw [sub_mul]; linear_combination hSSw
        rcases mul_eq_zero.mp hz with h | h
        · have : ((σ i) ^ 2 : 𝕜) = (c : 𝕜) := by linear_combination h
          exact_mod_cast this
        · exact absurd h h0
      rw [show Real.sqrt c = σ i by rw [← hsq, Real.sqrt_sq (hσnn i)]]
  rw [hSw, inner_smul_right, hcoef]

theorem positive_sqrt_unique {T R S : V →ₗ[𝕜] V} (hR : R.IsPositive) (hRT : R ∘ₗ R = T)
    (hS : S.IsPositive) (hST : S ∘ₗ S = T) : R = S := by
  have hTs : T.IsSymmetric := by
    rw [← hRT]; intro x y
    simp only [LinearMap.comp_apply]
    rw [hR.isSymmetric, hR.isSymmetric]
  have hTpos : T.IsPositive := by
    rw [← hRT]
    refine ⟨?_, fun x => ?_⟩
    · intro x y; simp only [LinearMap.comp_apply]; rw [hR.isSymmetric, hR.isSymmetric]
    · simp only [LinearMap.comp_apply]
      rw [hR.isSymmetric (R x) x, inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow, RCLike.ofReal_re]
      positivity
  set n := Module.finrank 𝕜 V
  set b := hTs.eigenvectorBasis (rfl : Module.finrank 𝕜 V = n) with hb
  set μ := hTs.eigenvalues (rfl : Module.finrank 𝕜 V = n) with hμ
  have hμnn : ∀ i, 0 ≤ μ i := by
    intro i
    have hev : HasEigenvalue T ((μ i : ℝ) : 𝕜) :=
      hTs.hasEigenvalue_eigenvalues (rfl : Module.finrank 𝕜 V = n) i
    have := (eigenvalue_nonneg hTpos hev).1
    rwa [RCLike.ofReal_re] at this
  apply b.toBasis.ext
  intro i
  simp only [OrthonormalBasis.coe_toBasis]
  have hwR : (R ∘ₗ R) (b i) = ((μ i : ℝ) : 𝕜) • b i := by
    rw [hRT]; exact hTs.apply_eigenvectorBasis (rfl : Module.finrank 𝕜 V = n) i
  have hwS : (S ∘ₗ S) (b i) = ((μ i : ℝ) : 𝕜) • b i := by
    rw [hST]; exact hTs.apply_eigenvectorBasis (rfl : Module.finrank 𝕜 V = n) i
  rw [sqrt_eigenvector hR (hμnn i) hwR, sqrt_eigenvector hS (hμnn i) hwS]

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
