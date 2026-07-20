import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Symmetric
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.Algebra.Polynomial.Splits
import LinearAlgebraDoneRightLean.Section_7A
import LinearAlgebraDoneRightLean.Section_6B
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
through Schur's theorem (6.38, from
{module -checked}`LinearAlgebraDoneRightLean.Section_6B`): a normal operator that
is upper-triangular with respect to an orthonormal basis is in fact diagonal. -/

/-- A normal operator that is upper-triangular with respect to an orthonormal
basis {lit}`e` is diagonal: each {lit}`eₖ` is an eigenvector. The proof compares
{lit}`‖T eₖ‖² = ∑ᵢ ‖⟨eᵢ, T eₖ⟩‖²` (column {lit}`k`) with
{lit}`‖T* eₖ‖² = ∑ᵢ ‖⟨eₖ, T eᵢ⟩‖²` (row {lit}`k`); equality (7.20) plus an
induction from the top row forces every strictly-upper entry to vanish. -/
theorem normal_ut_diagonal {n : ℕ} (T : V →ₗ[𝕜] V) (hN : IsStarNormal T)
    (e : OrthonormalBasis (Fin n) 𝕜 V)
    (hUT : ∀ k, T (e k) ∈ Submodule.span 𝕜 (e '' {i | i ≤ k})) :
    ∀ k, T (e k) = ⟪e k, T (e k)⟫_𝕜 • e k := by
  set a : Fin n → Fin n → 𝕜 := fun i j => ⟪e i, T (e j)⟫_𝕜 with ha
  have hUTz : ∀ i j : Fin n, j < i → a i j = 0 := by
    intro i j hji
    have hmem : T (e j) ∈ Submodule.span 𝕜 (e '' {l | l ≤ j}) := hUT j
    have horth : e i ∈ (Submodule.span 𝕜 (e '' {l | l ≤ j}))ᗮ := by
      rw [Submodule.mem_orthogonal']
      intro y hy
      have hle : Submodule.span 𝕜 (e '' {l | l ≤ j}) ≤ (𝕜 ∙ e i)ᗮ := by
        rw [Submodule.span_le]
        rintro _ ⟨l, hlj, rfl⟩
        rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_left]
        exact e.orthonormal.2 (fun h => absurd (h ▸ hlj) (not_le.mpr hji))
      have hyi := hle hy
      rw [Submodule.mem_orthogonal_singleton_iff_inner_right] at hyi
      exact hyi
    simp only [ha]
    exact inner_eq_zero_symm.mpr (Submodule.inner_right_of_mem_orthogonal hmem horth)
  have hParsT : ∀ k, ‖T (e k)‖ ^ 2 = ∑ i, ‖a i k‖ ^ 2 := by
    intro k
    simp only [ha]
    exact (OrthonormalBasis.sum_sq_norm_inner_right e (T (e k))).symm
  have hParsA : ∀ k, ‖LinearMap.adjoint T (e k)‖ ^ 2 = ∑ i, ‖a k i‖ ^ 2 := by
    intro k
    rw [← OrthonormalBasis.sum_sq_norm_inner_right e (LinearMap.adjoint T (e k))]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [ha]
    rw [LinearMap.adjoint_inner_right]
    congr 1
    exact norm_inner_symm (T (e i)) (e k)
  have hN2 : ∀ v, ‖T v‖ = ‖LinearMap.adjoint T v‖ := (LADR.Section_7A.normal_iff_norm T).mp hN
  have hQaux : ∀ m : ℕ, ∀ k : Fin n, k.val = m → ∀ j : Fin n, k < j → a k j = 0 := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m IH =>
      intro k hk j hkj
      have IHk : ∀ i : Fin n, i < k → a i k = 0 := fun i hik =>
        IH i.val (by rw [← hk]; exact Fin.lt_def.mp hik) i rfl k hik
      have hcol : ∑ i, ‖a i k‖ ^ 2 = ‖a k k‖ ^ 2 := by
        rw [Finset.sum_eq_single k]
        · intro i _ hik
          rcases lt_or_gt_of_ne hik with h | h
          · rw [IHk i h, norm_zero]; ring
          · rw [hUTz i k h, norm_zero]; ring
        · intro h; exact absurd (Finset.mem_univ k) h
      have hnorm_eq : ∑ i, ‖a i k‖ ^ 2 = ∑ i, ‖a k i‖ ^ 2 := by
        rw [← hParsT k, ← hParsA k, hN2 (e k)]
      have hsum_eq : ∑ i, ‖a k i‖ ^ 2 = ‖a k k‖ ^ 2 := by rw [← hnorm_eq, hcol]
      have hzero : ∑ i ∈ Finset.univ.erase k, ‖a k i‖ ^ 2 = 0 := by
        have hae := Finset.add_sum_erase Finset.univ (fun i => ‖a k i‖ ^ 2) (Finset.mem_univ k)
        rw [hsum_eq] at hae
        linarith
      have hjmem : j ∈ Finset.univ.erase k :=
        Finset.mem_erase.mpr ⟨(ne_of_lt hkj).symm, Finset.mem_univ j⟩
      have hj0 : ‖a k j‖ ^ 2 = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => by positivity)).mp hzero j hjmem
      have hjn : ‖a k j‖ = 0 := by nlinarith [norm_nonneg (a k j)]
      rwa [norm_eq_zero] at hjn
  have hQ : ∀ k : Fin n, ∀ j : Fin n, k < j → a k j = 0 := fun k => hQaux k.val k rfl
  intro k
  have hexp : T (e k) = ∑ i, a i k • e i := by
    simp only [ha]
    exact (e.sum_repr' (T (e k))).symm
  conv_lhs => rw [hexp]
  rw [Finset.sum_eq_single k (fun i _ hik => by
        rcases lt_or_gt_of_ne hik with h | h
        · rw [hQ i k h, zero_smul]
        · rw [hUTz i k h, zero_smul])
      (fun h => absurd (Finset.mem_univ k) h)]

/-- 7.31 (Complex spectral theorem) Every normal operator on a finite-dimensional
complex inner product space has an orthonormal basis of eigenvectors. -/
theorem complex_spectral {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    [FiniteDimensional ℂ W] (T : W →ₗ[ℂ] W) (hN : IsStarNormal T) :
    ∃ (n : ℕ) (e : OrthonormalBasis (Fin n) ℂ W),
      ∀ k, T (e k) = ⟪e k, T (e k)⟫_ℂ • e k := by
  obtain ⟨n, e, he, hUT⟩ := LADR.Section_6B.exists_orthonormal_upperTriangular_complex T
  have hflag : ∀ k, T (e k) ∈ Submodule.span ℂ (e '' {i | i ≤ k}) :=
    ((LADR.Section_5C.tfae_upperTriangular he T).out 0 2).mp hUT
  exact ⟨n, e, normal_ut_diagonal T hN e hflag⟩

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
