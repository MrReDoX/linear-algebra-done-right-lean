import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Symmetric
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.Algebra.Polynomial.Splits
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
  have hinner : ⟪(T ∘ₗ T + (b : 𝕜) • T + (c : 𝕜) • (LinearMap.id : V →ₗ[𝕜] V)) v, v⟫_𝕜
      = ((‖T v‖ ^ 2 : ℝ) : 𝕜) + (b : 𝕜) * ⟪T v, v⟫_𝕜 + ((c * ‖v‖ ^ 2 : ℝ) : 𝕜) := by
    rw [LinearMap.add_apply, LinearMap.add_apply, inner_add_left, inner_add_left,
      LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.id_apply,
      inner_smul_left, inner_smul_left, hT (T v) v, inner_self_eq_norm_sq_to_K,
      inner_self_eq_norm_sq_to_K, RCLike.conj_ofReal, RCLike.conj_ofReal]
    push_cast
    ring
  rw [hinner, map_add, map_add, RCLike.ofReal_re, RCLike.re_ofReal_mul, RCLike.ofReal_re]
  have hcs : RCLike.re ⟪T v, v⟫_𝕜 ^ 2 ≤ ‖T v‖ ^ 2 * ‖v‖ ^ 2 := by
    have h1 : ‖⟪T v, v⟫_𝕜‖ ≤ ‖T v‖ * ‖v‖ := norm_inner_le_norm (T v) v
    have h2 : |RCLike.re ⟪T v, v⟫_𝕜| ≤ ‖T v‖ * ‖v‖ :=
      le_trans (RCLike.abs_re_le_norm _) h1
    nlinarith [sq_abs (RCLike.re ⟪T v, v⟫_𝕜), norm_nonneg (T v), norm_nonneg v,
      abs_nonneg (RCLike.re ⟪T v, v⟫_𝕜)]
  have hs : 0 < ‖v‖ ^ 2 := by positivity
  nlinarith [hcs, hbc, hs, sq_nonneg (‖v‖ ^ 2 * b + 2 * RCLike.re ⟪T v, v⟫_𝕜),
    mul_pos hs hs]

/-! 7.27 The minimal polynomial of a self-adjoint operator (over {lit}`ℝ`) is a
product of the linear factors {lit}`(z − λ₁) ⋯ (z − λₘ)` — i.e. it splits over
{lit}`ℝ`. -/

open Polynomial in
theorem minpoly_symmetric_splits {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] (T : V →ₗ[ℝ] V)
    (hT : T.IsSymmetric) :
    (minpoly ℝ T).Splits := by
  set b := hT.eigenvectorBasis (rfl : Module.finrank ℝ V = Module.finrank ℝ V) with hb
  set μ := hT.eigenvalues (rfl : Module.finrank ℝ V = Module.finrank ℝ V) with hμ
  set S := Finset.image μ Finset.univ with hS
  set p := ∏ lam ∈ S, (X - C lam) with hp
  have hp0 : p ≠ 0 := by
    rw [hp]; exact Finset.prod_ne_zero_iff.mpr fun lam _ => X_sub_C_ne_zero lam
  have hpsplit : p.Splits :=
    Polynomial.Splits.prod (fun lam _ => Polynomial.Splits.X_sub_C lam)
  have haeval : (aeval T) p = 0 := by
    apply b.toBasis.ext
    intro i
    simp only [LinearMap.zero_apply]
    have hiS : μ i ∈ S := Finset.mem_image_of_mem μ (Finset.mem_univ i)
    rw [hp, ← Finset.prod_erase_mul S _ hiS, map_mul, Module.End.mul_apply]
    have hkill : (aeval T) (X - C (μ i)) (b.toBasis i) = 0 := by
      simp only [OrthonormalBasis.coe_toBasis]
      simp only [map_sub, aeval_X, aeval_C, LinearMap.sub_apply,
        Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply, Module.End.one_apply]
      rw [hT.apply_eigenvectorBasis (rfl : Module.finrank ℝ V = Module.finrank ℝ V) i]
      simp [hb, hμ]
    rw [hkill, map_zero]
  exact Polynomial.Splits.of_dvd hpsplit hp0 (minpoly.dvd ℝ T haeval)

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
