import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Real.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Ring
import Mathlib.Tactic.TFAE
import LinearAlgebraDoneRightLean.Section_2A
import LinearAlgebraDoneRightLean.Section_2B
import LinearAlgebraDoneRightLean.Section_3B
import LinearAlgebraDoneRightLean.Section_3C
import LinearAlgebraDoneRightLean.Section_3D
import LinearAlgebraDoneRightLean.Section_5A
import LinearAlgebraDoneRightLean.Section_5B
import CompanionHelper

/-!
# Axler, *Linear Algebra Done Right* (4e) — Section 5C: Upper-Triangular Matrices
-/

namespace LADR.Section_5C

open LADR.Section_2A (Spans)
open LADR.Section_2B (IsBasis isBasis_stdBasis isBasis_stdBasis_repr)
open LADR.Section_3C (matrixOf matrixOf_apply matrixOf_spec)
open LADR.Section_3D (IsInvertible)
open LADR.Section_5A (InvariantUnder IsEigenvalue aeval_mul_eq_comp
  range_aeval_invariant exercise_5A_38_quotient_op)
open LADR.Section_5B (aeval_eq_zero_iff_minpoly_dvd isEigenvalue_iff_isRoot
  aeval_restrict_coe)
open LinearMap (ker range)
open Module (Finite finrank)
open Polynomial (aeval)

universe u

variable {F : Type*} [Field F]
  {V : Type*} [AddCommGroup V] [Module F V]

/-! 5.35 Definition: matrix of an operator, {lit}`ℳ(T)`.

An operator {lit}`T ∈ ℒ(V)` gets a *square* matrix with respect to a single
basis {lit}`v₁, …, vₙ` of {lit}`V`: this is Section 3C's
{name}`LADR.Section_3C.matrixOf` with the same basis used twice,
{lit}`matrixOf hv hv T`. -/

noncomputable example {n : ℕ} {v : Fin n → V} (hv : IsBasis F v)
    (T : V →ₗ[F] V) : Matrix (Fin n) (Fin n) F :=
  matrixOf hv hv T

/-! 5.36 Example: {lit}`T(x, y, z) = (2x + y, 5y + 3z, 8z)` has matrix
{lit}`[[2,1,0],[0,5,3],[0,0,8]]` with respect to the standard basis. -/

noncomputable def T_5_36 : (Fin 3 → F) →ₗ[F] (Fin 3 → F) where
  toFun x := ![2 * x 0 + x 1, 5 * x 1 + 3 * x 2, 8 * x 2]
  map_add' x y := by
    funext i
    fin_cases i <;> simp <;> ring
  map_smul' c x := by
    funext i
    fin_cases i <;> simp <;> ring

theorem matrixOf_T_5_36 :
    matrixOf (isBasis_stdBasis (F := F) 3) (isBasis_stdBasis (F := F) 3)
      T_5_36 = !![2, 1, 0; 0, 5, 3; 0, 0, 8] := by
  ext j k
  rw [matrixOf_apply, isBasis_stdBasis_repr]
  fin_cases j <;> fin_cases k <;> simp [T_5_36]

/-! 5.37 Definition: diagonal of a square matrix — mathlib's
{name}`Matrix.diag`. -/

example {n : ℕ} (A : Matrix (Fin n) (Fin n) F) (k : Fin n) :
    A.diag k = A k k := rfl

/-! 5.38 Definition: upper-triangular matrix -/

/-- A square matrix is *upper triangular* if all entries below the diagonal
are {lit}`0`. (mathlib's general notion is {name}`Matrix.BlockTriangular`
with respect to {lit}`id`.) -/
def IsUpperTriangular {n : ℕ} (A : Matrix (Fin n) (Fin n) F) : Prop :=
  ∀ j k, k < j → A j k = 0

example {n : ℕ} (A : Matrix (Fin n) (Fin n) F) :
    IsUpperTriangular A ↔ A.BlockTriangular id :=
  ⟨fun h _i _j hij => h _ _ hij, fun h _i _j hij => h hij⟩

/-! 5.39 Conditions for upper-triangular matrix.

For a basis {lit}`v₁, …, vₙ` of {lit}`V`, the matrix of {lit}`T` is upper
triangular iff {lit}`span(v₁, …, vₖ)` is invariant under {lit}`T` for each
{lit}`k`, iff {lit}`T vₖ ∈ span(v₁, …, vₖ)` for each {lit}`k`. -/

theorem tfae_upperTriangular {n : ℕ} {v : Fin n → V} (hv : IsBasis F v)
    (T : V →ₗ[F] V) :
    [IsUpperTriangular (matrixOf hv hv T),
      ∀ k : Fin n, InvariantUnder T (Submodule.span F (v '' {i | i ≤ k})),
      ∀ k : Fin n, T (v k) ∈ Submodule.span F (v '' {i | i ≤ k})].TFAE := by
  tfae_have 1 → 2 := by
    intro hA k x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j, hj, rfl⟩ := hy
      -- {lit}`T vⱼ = ∑ᵢ A_{i,j} vᵢ`, and the entries with {lit}`i > j`
      -- vanish, so {lit}`T vⱼ ∈ span(v₁, …, vⱼ) ⊆ span(v₁, …, vₖ)`.
      rw [matrixOf_spec hv hv T j]
      apply Submodule.sum_mem
      intro i _
      by_cases hij : i ≤ j
      · exact Submodule.smul_mem _ _
          (Submodule.subset_span ⟨i, le_trans hij hj, rfl⟩)
      · rw [hA i j (lt_of_not_ge hij), zero_smul]
        exact Submodule.zero_mem _
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
    | smul a y _ hy => rw [map_smul]; exact Submodule.smul_mem _ a hy
  tfae_have 2 → 3 := fun h k =>
    h k (v k) (Submodule.subset_span ⟨k, le_refl k, rfl⟩)
  tfae_have 3 → 1 := by
    intro h j k hkj
    -- The coefficients of {lit}`T vₖ` are supported on {lit}`{i : i ≤ k}`.
    rw [matrixOf_apply]
    have himg : v '' {i | i ≤ k} = ⇑hv.toModuleBasis '' {i | i ≤ k} :=
      Set.image_congr fun i _ => (hv.toModuleBasis_apply i).symm
    have hmem := h k
    rw [himg] at hmem
    have hsupp := (Module.Basis.mem_span_image hv.toModuleBasis).mp hmem
    by_contra hne
    exact absurd (hsupp (Finsupp.mem_support_iff.mpr hne)) (not_le.mpr hkj)
  tfae_finish

/-! 5.40 Equation satisfied by an operator with an upper-triangular matrix:
if {lit}`ℳ(T)` is upper triangular with diagonal entries
{lit}`λ₁, …, λₙ`, then {lit}`(T − λ₁I)⋯(T − λₙI) = 0`. We state this in the
polynomial form {lit}`q(T) = 0` for {lit}`q(z) = (z − λ₁)⋯(z − λₙ)`. -/

/-- The key step in 5.40 and 5.41: {lit}`T − λₖI` maps
{lit}`span(v₁, …, vₖ)` into {lit}`span(v₁, …, v_{k−1})`. -/
private lemma sub_diag_maps_into {n : ℕ} {v : Fin n → V} (hv : IsBasis F v)
    (T : V →ₗ[F] V) (hA : IsUpperTriangular (matrixOf hv hv T)) (k : Fin n) :
    ∀ x ∈ Submodule.span F (v '' {i | i ≤ k}),
      (T - matrixOf hv hv T k k • (LinearMap.id : V →ₗ[F] V)) x ∈
        Submodule.span F (v '' {i | i < k}) := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨j, hj, rfl⟩ := hy
    have hj' : j ≤ k := hj
    rw [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply]
    rcases eq_or_lt_of_le hj' with rfl | hjk
    · -- {lit}`(T − λⱼI)vⱼ = ∑_{i<j} A_{i,j} vᵢ`: the diagonal cancels.
      rw [matrixOf_spec hv hv T j]
      have hsplit : (∑ i, matrixOf hv hv T i j • v i) =
          matrixOf hv hv T j j • v j +
            ∑ i ∈ Finset.univ.erase j, matrixOf hv hv T i j • v i :=
        (Finset.add_sum_erase _ _ (Finset.mem_univ j)).symm
      rw [hsplit, add_sub_cancel_left]
      apply Submodule.sum_mem
      intro i hi
      rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase hi) with hlt | hgt
      · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hlt, rfl⟩)
      · rw [hA i j hgt, zero_smul]
        exact Submodule.zero_mem _
    · -- For {lit}`j < k` both terms already lie in
      -- {lit}`span(v₁, …, v_{k−1})`.
      apply Submodule.sub_mem
      · have h3 := (tfae_upperTriangular hv T).out 0 2
        have hTj := h3.mp hA j
        refine Submodule.span_mono ?_ hTj
        rintro y ⟨i, hi, rfl⟩
        exact ⟨i, lt_of_le_of_lt hi hjk, rfl⟩
      · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hjk, rfl⟩)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
  | smul a y _ hy => rw [map_smul]; exact Submodule.smul_mem _ a hy

private lemma aeval_X_sub_C_apply (T : V →ₗ[F] V) (a : F) (x : V) :
    aeval T (Polynomial.X - Polynomial.C a) x =
      (T - a • (LinearMap.id : V →ₗ[F] V)) x := by
  rw [map_sub, Polynomial.aeval_X, Polynomial.aeval_C, LinearMap.sub_apply,
    LinearMap.sub_apply, Module.algebraMap_end_apply, LinearMap.smul_apply,
    LinearMap.id_apply]

theorem aeval_prod_diag_eq_zero {n : ℕ} {v : Fin n → V} (hv : IsBasis F v)
    (T : V →ₗ[F] V) (hA : IsUpperTriangular (matrixOf hv hv T)) :
    aeval T (∏ k, (Polynomial.X -
      Polynomial.C (matrixOf hv hv T k k))) = 0 := by
  -- Main claim: the partial products annihilate the partial spans.
  have hmain : ∀ m : ℕ, ∀ k : Fin n, (k : ℕ) + 1 ≤ m →
      ∀ x ∈ Submodule.span F (v '' {i | i ≤ k}),
        aeval T (∏ i ∈ Finset.univ.filter (· ≤ k),
          (Polynomial.X - Polynomial.C (matrixOf hv hv T i i))) x = 0 := by
    intro m
    induction m with
    | zero => intro k hk; omega
    | succ m ih =>
      intro k hk x hx
      -- Pull out the factor {lit}`(z − λₖ)` from the product.
      have hk_mem : k ∈ Finset.univ.filter (· ≤ k) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ k, le_refl k⟩
      have hsplit : (∏ i ∈ Finset.univ.filter (· ≤ k),
          (Polynomial.X - Polynomial.C (matrixOf hv hv T i i))) =
          (∏ i ∈ (Finset.univ.filter (· ≤ k)).erase k,
            (Polynomial.X - Polynomial.C (matrixOf hv hv T i i))) *
            (Polynomial.X - Polynomial.C (matrixOf hv hv T k k)) :=
        (Finset.prod_erase_mul _ _ hk_mem).symm
      rw [hsplit, aeval_mul_eq_comp, LinearMap.comp_apply,
        aeval_X_sub_C_apply]
      have hstep := sub_diag_maps_into hv T hA k x hx
      -- The image lands in {lit}`span(v₁, …, v_{k−1})`.
      rcases Nat.eq_zero_or_pos (k : ℕ) with hk0 | hkpos
      · -- {lit}`k = 0`: the image is in {lit}`span ∅ = {0}`.
        have hempty : {i : Fin n | i < k} = ∅ := by
          ext i
          simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false,
            not_lt, Fin.le_def]
          omega
        rw [hempty, Set.image_empty, Submodule.span_empty,
          Submodule.mem_bot] at hstep
        rw [hstep, map_zero]
      · -- {lit}`k > 0`: erase {lit}`k` to get the predecessor's product.
        set k' : Fin n := ⟨(k : ℕ) - 1, by omega⟩ with hk'_def
        have hlt_iff : ∀ i : Fin n, i < k ↔ i ≤ k' := by
          intro i
          rw [Fin.lt_def, Fin.le_def]
          simp only [hk'_def]
          omega
        have hset : {i : Fin n | i < k} = {i | i ≤ k'} := by
          ext i
          exact hlt_iff i
        have hfilter : (Finset.univ.filter (· ≤ k)).erase k =
            Finset.univ.filter (· ≤ k') := by
          ext i
          simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ,
            true_and]
          constructor
          · rintro ⟨hne, hle⟩
            exact (hlt_iff i).mp (lt_of_le_of_ne hle hne)
          · intro hle
            have := (hlt_iff i).mpr hle
            exact ⟨ne_of_lt this, le_of_lt this⟩
        rw [hset] at hstep
        rw [hfilter]
        exact ih k' (by simp only [hk'_def]; omega) _ hstep
  -- Now apply the claim to all of {lit}`V`.
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · -- {lit}`n = 0`: the basis is empty, so {lit}`V = {0}`.
    subst hn0
    apply LinearMap.ext
    intro x
    have hx : x ∈ Submodule.span F (Set.range v) := by
      rw [hv.2]
      exact Submodule.mem_top
    rw [Set.range_eq_empty v, Submodule.span_empty, Submodule.mem_bot] at hx
    rw [hx, map_zero, LinearMap.zero_apply]
  · apply LinearMap.ext
    intro x
    set klast : Fin n := ⟨n - 1, by omega⟩ with hklast_def
    have huniv : Finset.univ.filter (· ≤ klast) = Finset.univ := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      rw [Fin.le_def]
      simp only [hklast_def]
      omega
    have hx : x ∈ Submodule.span F (v '' {i | i ≤ klast}) := by
      have hall : {i : Fin n | i ≤ klast} = Set.univ := by
        ext i
        simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
        rw [Fin.le_def]
        simp only [hklast_def]
        omega
      rw [hall, Set.image_univ, hv.2]
      exact Submodule.mem_top
    have := hmain n klast (by simp only [hklast_def]; omega) x hx
    rw [huniv] at this
    rw [this, LinearMap.zero_apply]

/-! 5.41 Determination of eigenvalues from an upper-triangular matrix: the
eigenvalues of {lit}`T` are precisely the diagonal entries. -/

theorem isEigenvalue_iff_diag [Finite F V] {n : ℕ} {v : Fin n → V}
    (hv : IsBasis F v) (T : V →ₗ[F] V)
    (hA : IsUpperTriangular (matrixOf hv hv T)) (lam : F) :
    IsEigenvalue T lam ↔ ∃ k, matrixOf hv hv T k k = lam := by
  constructor
  · -- An eigenvalue is a zero of the minimal polynomial (5.27), which
    -- divides {lit}`∏ (z − λₖ)` (5.40 + 5.29), so it equals some {lit}`λₖ`.
    intro hlam
    have hroot := (isEigenvalue_iff_isRoot T lam).mp hlam
    have hdvd : minpoly F T ∣ ∏ k, (Polynomial.X -
        Polynomial.C (matrixOf hv hv T k k)) :=
      (aeval_eq_zero_iff_minpoly_dvd T _).mp (aeval_prod_diag_eq_zero hv T hA)
    have hroot' : (∏ k, (Polynomial.X -
        Polynomial.C (matrixOf hv hv T k k))).IsRoot lam :=
      hroot.dvd hdvd
    rw [Polynomial.IsRoot.def, Polynomial.eval_prod] at hroot'
    obtain ⟨k, -, hk⟩ := Finset.prod_eq_zero_iff.mp hroot'
    refine ⟨k, ?_⟩
    rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
      sub_eq_zero] at hk
    exact hk.symm
  · -- A diagonal entry {lit}`λₖ` is an eigenvalue: {lit}`T − λₖI` maps the
    -- {lit}`(k+1)`-dimensional {lit}`span(v₁, …, vₖ)` into the
    -- {lit}`k`-dimensional {lit}`span(v₁, …, v_{k−1})`, so it is not
    -- injective there (3.22).
    rintro ⟨k, rfl⟩
    set Uk := Submodule.span F (v '' {i | i ≤ k}) with hUk_def
    set Uk' := Submodule.span F (v '' {i | i < k}) with hUk'_def
    -- Dimensions: spans of {lit}`k+1` resp. {lit}`k` linearly independent
    -- vectors.
    have himg_le : v '' {i | i ≤ k} =
        Set.range (v ∘ Fin.castLE (show (k : ℕ) + 1 ≤ n by omega)) := by
      ext x
      constructor
      · rintro ⟨j, hj, rfl⟩
        exact ⟨⟨(j : ℕ), by have := Fin.le_def.mp hj; omega⟩, rfl⟩
      · rintro ⟨i, rfl⟩
        refine ⟨Fin.castLE _ i, ?_, rfl⟩
        rw [Set.mem_setOf_eq, Fin.le_def]
        simp only [Fin.val_castLE]
        omega
    have himg_lt : v '' {i | i < k} =
        Set.range (v ∘ Fin.castLE (show (k : ℕ) ≤ n by omega)) := by
      ext x
      constructor
      · rintro ⟨j, hj, rfl⟩
        exact ⟨⟨(j : ℕ), Fin.lt_def.mp hj⟩, rfl⟩
      · rintro ⟨i, rfl⟩
        refine ⟨Fin.castLE _ i, ?_, rfl⟩
        rw [Set.mem_setOf_eq, Fin.lt_def]
        simp only [Fin.val_castLE]
        omega
    have hli := hv.1
    have hrank_le : finrank F Uk = (k : ℕ) + 1 := by
      rw [hUk_def, himg_le, finrank_span_eq_card
        (hli.comp _ (Fin.castLE_injective _)), Fintype.card_fin]
    have hrank_lt : finrank F Uk' = (k : ℕ) := by
      rw [hUk'_def, himg_lt, finrank_span_eq_card
        (hli.comp _ (Fin.castLE_injective _)), Fintype.card_fin]
    -- The restricted map {lit}`Uk → Uk'` is not injective.
    set f := T - matrixOf hv hv T k k • (LinearMap.id : V →ₗ[F] V) with hf_def
    have hmaps := sub_diag_maps_into hv T hA k
    set g : Uk →ₗ[F] Uk' := LinearMap.codRestrict Uk' (f.domRestrict Uk)
      (fun x => hmaps (x : V) x.2) with hg_def
    have hginj : ¬ Function.Injective g := by
      apply LADR.Section_3B.not_injective_of_finrank_lt
      rw [hrank_le, hrank_lt]
      omega
    rw [LADR.Section_3B.injective_iff_ker_eq_bot] at hginj
    obtain ⟨x, hx_mem, hx_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hginj
    rw [LinearMap.mem_ker] at hx_mem
    have hfx : f (x : V) = 0 := by
      have := congrArg Subtype.val hx_mem
      exact this
    refine ⟨(x : V), fun h => hx_ne (Subtype.ext h), ?_⟩
    rw [hf_def] at hfx
    rw [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
      sub_eq_zero] at hfx
    exact hfx

/-! 5.42 Example: the eigenvalues of the operator of 5.36 are exactly the
diagonal entries {lit}`2, 5, 8` of its upper-triangular matrix. -/

example : ∀ lam : F, IsEigenvalue (T_5_36 (F := F)) lam ↔
    lam = 2 ∨ lam = 5 ∨ lam = 8 := by
  intro lam
  have hA : IsUpperTriangular
      (matrixOf (isBasis_stdBasis (F := F) 3) (isBasis_stdBasis 3) T_5_36) := by
    rw [matrixOf_T_5_36]
    intro j k hkj
    fin_cases j <;> fin_cases k <;> simp_all [Fin.lt_def]
  rw [isEigenvalue_iff_diag (isBasis_stdBasis 3) T_5_36 hA lam,
    matrixOf_T_5_36]
  constructor
  · rintro ⟨k, hk⟩
    fin_cases k <;> simp_all
  · rintro (rfl | rfl | rfl)
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩
    · exact ⟨2, by simp⟩

/-! 5.43 Example (not formalized): whether {lit}`T` has an upper-triangular
matrix can depend on {lit}`F` — the operator on {lit}`F⁴` with matrix
{lit}`[[0,−1,0,0],[1,0,0,0],[2,0,3,0],[0,0,1,3]]` has minimal polynomial
{lit}`(z² + 1)(z − 3)²`, which factors into linear factors over {lit}`ℂ` but
not over {lit}`ℝ`; by 5.44 it is upper-triangularizable over {lit}`ℂ` only.
(The minimal-polynomial computation is omitted here.) -/

/-! 5.44 Necessary and sufficient condition to have an upper-triangular
matrix: {lit}`T` has an upper-triangular matrix with respect to some basis
of {lit}`V` iff the minimal polynomial of {lit}`T` equals
{lit}`(z − λ₁)⋯(z − λₘ)` for some {lit}`λ₁, …, λₘ ∈ F`. -/

/-- A monic polynomial that splits is the (finite, indexed) product of its
linear factors. -/
private lemma monic_splits_eq_prod_fin {p : Polynomial F} (hmonic : p.Monic)
    (hsplits : p.Splits) :
    ∃ (m : ℕ) (lam : Fin m → F),
      p = ∏ k, (Polynomial.X - Polynomial.C (lam k)) ∧ m = p.natDegree := by
  have h := Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C
    (p := p) (Polynomial.splits_iff_card_roots.mp hsplits)
  rw [hmonic.leadingCoeff, Polynomial.C_1, one_mul] at h
  refine ⟨p.roots.toList.length, fun k => p.roots.toList.get k, ?_, ?_⟩
  · conv_lhs => rw [← h]
    conv_lhs => rw [show p.roots = ↑p.roots.toList from
      (Multiset.coe_toList p.roots).symm]
    rw [Multiset.map_coe, Multiset.prod_coe]
    rw [show p.roots.toList.map (fun a => Polynomial.X - Polynomial.C a) =
      List.ofFn ((fun a => Polynomial.X - Polynomial.C a) ∘
        p.roots.toList.get) by
        rw [← List.map_ofFn, List.ofFn_get]]
    rw [List.prod_ofFn]
    rfl
  · rw [Multiset.length_toList]
    exact (Polynomial.splits_iff_card_roots.mp hsplits)

/-- The inductive heart of 5.44: if the minimal polynomial of {lit}`T` is a
product of {lit}`m` monic linear factors, then {lit}`V` has a basis with
respect to which {lit}`T` is upper triangular. Strong induction on
{lit}`m`, restricting to {lit}`U = range(T − λₘI)`. -/
private lemma exists_upperTriangular_of_minpoly_prod :
    ∀ (m : ℕ) (W : Type u) (_ : AddCommGroup W),
      ∀ (_ : Module F W) (_ : Module.Finite F W) (T : W →ₗ[F] W)
        (lam : Fin m → F),
        minpoly F T = (∏ k, (Polynomial.X - Polynomial.C (lam k))) →
        ∃ (n : ℕ) (w : Fin n → W) (hw : IsBasis F w),
          IsUpperTriangular (matrixOf hw hw T) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro W _ _ _ T lam hfact
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · -- Base case: the minimal polynomial is the empty product {lit}`1`,
      -- which forces {lit}`W = {0}`; the empty basis works.
      simp only [Finset.univ_eq_empty, Finset.prod_empty] at hfact
      have hid : (1 : W →ₗ[F] W) = 0 := by
        have h1 := minpoly.aeval F T
        rwa [hfact, map_one] at h1
      have hsub : Subsingleton W := by
        constructor
        intro a b
        have ha := LinearMap.congr_fun hid a
        have hb := LinearMap.congr_fun hid b
        rw [Module.End.one_apply, LinearMap.zero_apply] at ha hb
        rw [ha, hb]
      refine ⟨0, Fin.elim0, ⟨linearIndependent_empty_type, ?_⟩, ?_⟩
      · show Submodule.span F (Set.range Fin.elim0) = ⊤
        rw [Set.range_eq_empty, Submodule.span_empty, eq_top_iff]
        intro x _
        rw [Subsingleton.elim x 0]
        exact Submodule.zero_mem _
      · intro j _ _
        exact j.elim0
    · -- Inductive step: peel off the last factor {lit}`z − λₘ`.
      set mlast : Fin m := ⟨m - 1, by omega⟩ with hmlast_def
      set lamm : F := lam mlast with hlamm_def
      set f : W →ₗ[F] W := T - lamm • LinearMap.id with hf_def
      have hf_aeval : f = aeval T (Polynomial.X - Polynomial.C lamm) :=
        LinearMap.ext fun x => (aeval_X_sub_C_apply T lamm x).symm
      set U : Submodule F W := range f with hU_def
      have hU_inv : InvariantUnder T U := by
        rw [hU_def, hf_aeval]
        exact range_aeval_invariant T _
      -- The product of the remaining factors annihilates {lit}`T|_U`:
      -- every {lit}`u ∈ U` is {lit}`(T − λₘI)x`, and applying the remaining
      -- factors gives {lit}`p(T)x = 0`.
      have hprod_split : (∏ k ∈ Finset.univ.erase mlast,
          (Polynomial.X - Polynomial.C (lam k))) *
            (Polynomial.X - Polynomial.C lamm) = minpoly F T := by
        rw [hfact, hlamm_def]
        exact Finset.prod_erase_mul _ _ (Finset.mem_univ mlast)
      have hdvd : minpoly F hU_inv.restrict ∣
          ∏ k ∈ Finset.univ.erase mlast,
            (Polynomial.X - Polynomial.C (lam k)) := by
        rw [← aeval_eq_zero_iff_minpoly_dvd]
        apply LinearMap.ext
        intro u
        apply Subtype.ext
        rw [aeval_restrict_coe hU_inv _ u]
        obtain ⟨x, hx⟩ := LinearMap.mem_range.mp u.2
        rw [← hx, hf_aeval, ← LinearMap.comp_apply, ← aeval_mul_eq_comp,
          hprod_split, minpoly.aeval, LinearMap.zero_apply,
          LinearMap.zero_apply, ZeroMemClass.coe_zero]
      have hprod_ne : (∏ k ∈ Finset.univ.erase mlast,
          (Polynomial.X - Polynomial.C (lam k))) ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr fun k _ => Polynomial.X_sub_C_ne_zero _
      -- The minimal polynomial of {lit}`T|_U` is a product of fewer than
      -- {lit}`m` monic linear factors.
      have hsplits : (minpoly F hU_inv.restrict).Splits :=
        Polynomial.Splits.of_dvd
          (Polynomial.Splits.prod fun k _ => Polynomial.Splits.X_sub_C _)
          hprod_ne hdvd
      obtain ⟨m', lam', hfact', hm'_deg⟩ := monic_splits_eq_prod_fin
        (minpoly.monic (Algebra.IsIntegral.isIntegral hU_inv.restrict))
        hsplits
      have hm'_lt : m' < m := by
        have hle := Polynomial.natDegree_le_of_dvd hdvd hprod_ne
        have hdeg_prod : (∏ k ∈ Finset.univ.erase mlast,
            (Polynomial.X - Polynomial.C (lam k))).natDegree = m - 1 := by
          rw [Polynomial.natDegree_prod _ _
            (fun k _ => Polynomial.X_sub_C_ne_zero (lam k))]
          simp [Finset.card_erase_of_mem]
        omega
      -- Induction: an upper-triangular basis {lit}`u₁, …, u_M` for
      -- {lit}`T|_U`…
      obtain ⟨M, u', hu', hA'⟩ := ih m' hm'_lt U inferInstance inferInstance
        inferInstance hU_inv.restrict lam' hfact'
      -- …whose image in {lit}`W` we extend to a basis of {lit}`W`.
      set uW : Fin M → W := fun i => (u' i : W) with huW_def
      have huW_li : LinearIndependent F uW :=
        hu'.1.map' U.subtype (Submodule.ker_subtype U)
      obtain ⟨n, w, hMn, hw, hpre⟩ :=
        LADR.Section_2B.exists_basis_extending uW huW_li
      refine ⟨n, w, hw, ?_⟩
      -- It remains to verify 5.39(c) for the extended basis.
      have h31 := (tfae_upperTriangular hw T).out 2 0
      apply h31.mp
      have hT_decomp : ∀ x : W, T x = f x + lamm • x := by
        intro x
        rw [hf_def, LinearMap.sub_apply, LinearMap.smul_apply,
          LinearMap.id_apply, sub_add_cancel]
      have hU_le : U ≤ Submodule.span F (w '' {i : Fin n | (i : ℕ) < M}) := by
        have hU_span : U = Submodule.span F (Set.range uW) := by
          have h1 : Submodule.map U.subtype ⊤ = U := Submodule.map_subtype_top U
          have h2 : Submodule.span F (Set.range u') = ⊤ := hu'.2
          rw [← h1, ← h2, Submodule.map_span, ← Set.range_comp]
          rfl
        rw [hU_span]
        apply Submodule.span_le.mpr
        rintro x ⟨i, rfl⟩
        apply Submodule.subset_span
        exact ⟨Fin.castLE hMn i, by
          simp only [Set.mem_setOf_eq, Fin.val_castLE]
          exact i.isLt, hpre i⟩
      intro k
      by_cases hkM : (k : ℕ) < M
      · -- {lit}`wₖ` lies in {lit}`U`; use the upper-triangular structure of
        -- {lit}`T|_U`.
        set k' : Fin M := ⟨(k : ℕ), hkM⟩ with hk'_def
        have hwk : w k = uW k' := by
          have h := hpre k'
          rwa [show Fin.castLE hMn k' = k from Fin.ext rfl] at h
        have h302 := (tfae_upperTriangular hu' hU_inv.restrict).out 0 2
        have hres := h302.mp hA' k'
        have hTwk : T (w k) = ((hU_inv.restrict (u' k') : U) : W) := by
          rw [hwk]
          exact (hU_inv.restrict_apply (u' k')).symm
        rw [hTwk]
        have hcoe : ((hU_inv.restrict (u' k') : U) : W) ∈
            Submodule.span F (⇑U.subtype '' (u' '' {i | i ≤ k'})) := by
          rw [← Submodule.map_span]
          exact Submodule.mem_map_of_mem hres
        refine Submodule.span_mono ?_ hcoe
        rintro x ⟨y, ⟨i, hi, rfl⟩, rfl⟩
        refine ⟨Fin.castLE hMn i, ?_, (hpre i).symm ▸ rfl⟩
        rw [Set.mem_setOf_eq, Fin.le_def]
        simp only [Fin.val_castLE]
        exact Fin.le_def.mp hi
      · -- {lit}`k ≥ M`: write {lit}`Twₖ = (T − λₘI)wₖ + λₘwₖ`, with the
        -- first summand in {lit}`U ⊆ span(w₁, …, w_M)`.
        rw [hT_decomp (w k)]
        apply Submodule.add_mem
        · refine Submodule.span_mono ?_
            (hU_le (LinearMap.mem_range_self f (w k)))
          rintro x ⟨i, hi, rfl⟩
          refine ⟨i, ?_, rfl⟩
          rw [Set.mem_setOf_eq, Fin.le_def]
          rw [Set.mem_setOf_eq] at hi
          omega
        · exact Submodule.smul_mem _ _
            (Submodule.subset_span ⟨k, le_refl k, rfl⟩)

theorem exists_upperTriangular_iff_minpoly_eq_prod [Finite F V]
    (T : V →ₗ[F] V) :
    (∃ (n : ℕ) (v : Fin n → V) (hv : IsBasis F v),
      IsUpperTriangular (matrixOf hv hv T)) ↔
    ∃ (m : ℕ) (lam : Fin m → F),
      minpoly F T = ∏ k, (Polynomial.X - Polynomial.C (lam k)) := by
  constructor
  · -- 5.40 gives {lit}`q(T) = 0` for the product of diagonal factors; thus
    -- the minimal polynomial divides a split polynomial, hence splits.
    rintro ⟨n, v, hv, hA⟩
    have hdvd : minpoly F T ∣ ∏ k, (Polynomial.X -
        Polynomial.C (matrixOf hv hv T k k)) :=
      (aeval_eq_zero_iff_minpoly_dvd T _).mp (aeval_prod_diag_eq_zero hv T hA)
    have hprod_ne : (∏ k, (Polynomial.X -
        Polynomial.C (matrixOf hv hv T k k))) ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro k _
      exact Polynomial.X_sub_C_ne_zero _
    have hsplits : (minpoly F T).Splits :=
      Polynomial.Splits.of_dvd
        (Polynomial.Splits.prod fun k _ => Polynomial.Splits.X_sub_C _)
        hprod_ne hdvd
    obtain ⟨m, lam, hfact, -⟩ := monic_splits_eq_prod_fin
      (minpoly.monic (Algebra.IsIntegral.isIntegral T)) hsplits
    exact ⟨m, lam, hfact⟩
  · rintro ⟨m, lam, hfact⟩
    exact exists_upperTriangular_of_minpoly_prod m V inferInstance
      inferInstance inferInstance T lam hfact

/-! 5.47 If {lit}`F = ℂ`, then every operator on {lit}`V` has an
upper-triangular matrix with respect to some basis of {lit}`V` (5.44 plus
the fundamental theorem of algebra). -/

theorem exists_upperTriangular_complex {V : Type u} [AddCommGroup V]
    [Module ℂ V] [Finite ℂ V] (T : V →ₗ[ℂ] V) :
    ∃ (n : ℕ) (v : Fin n → V) (hv : IsBasis ℂ v),
      IsUpperTriangular (matrixOf hv hv T) := by
  rw [exists_upperTriangular_iff_minpoly_eq_prod]
  obtain ⟨m, lam, hfact, -⟩ := monic_splits_eq_prod_fin
    (minpoly.monic (Algebra.IsIntegral.isIntegral T))
    (IsAlgClosed.splits (k := ℂ) _)
  exact ⟨m, lam, hfact⟩

/-! # Exercises -/

/-- 5C.1 Prove or give a counterexample: if {lit}`T²` has an upper-triangular
matrix with respect to some basis, then so does {lit}`T`.
(Stated on {lit}`ℝ²`.) -/
def exercise_5C_1 :
    Decidable (∀ T : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ),
      (∃ (v : Fin 2 → (Fin 2 → ℝ)) (hv : IsBasis ℝ v),
        IsUpperTriangular (matrixOf hv hv (T ∘ₗ T))) →
      ∃ (v : Fin 2 → (Fin 2 → ℝ)) (hv : IsBasis ℝ v),
        IsUpperTriangular (matrixOf hv hv T)) := by
  -- first line should be `apply isTrue` or `apply isFalse`
  sorry

/-- 5C.2 (a) -/
theorem exercise_5C_2a {n : ℕ} (A B : Matrix (Fin n) (Fin n) F)
    (hA : IsUpperTriangular A) (hB : IsUpperTriangular B) :
    IsUpperTriangular (A + B) ∧ ∀ k, (A + B) k k = A k k + B k k := by
  sorry

/-- 5C.2 (b) -/
theorem exercise_5C_2b {n : ℕ} (A B : Matrix (Fin n) (Fin n) F)
    (hA : IsUpperTriangular A) (hB : IsUpperTriangular B) :
    IsUpperTriangular (A * B) ∧ ∀ k, (A * B) k k = A k k * B k k := by
  sorry

/-- 5C.3 -/
theorem exercise_5C_3 [Finite F V] {n : ℕ} {v : Fin n → V}
    (hv : IsBasis F v) (T : V →ₗ[F] V) (hT : IsInvertible T)
    (hA : IsUpperTriangular (matrixOf hv hv T)) :
    IsUpperTriangular (matrixOf hv hv hT.inv) ∧
      ∀ k, matrixOf hv hv hT.inv k k = (matrixOf hv hv T k k)⁻¹ := by
  sorry

/-- 5C.4 -/
theorem exercise_5C_4 :
    ∃ T : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ),
      (∃ (v : Fin 2 → (Fin 2 → ℝ)) (hv : IsBasis ℝ v),
        ∀ k, matrixOf hv hv T k k = 0) ∧ IsInvertible T := by
  sorry

/-- 5C.5 -/
theorem exercise_5C_5 :
    ∃ T : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ),
      (∃ (v : Fin 2 → (Fin 2 → ℝ)) (hv : IsBasis ℝ v),
        ∀ k, matrixOf hv hv T k k ≠ 0) ∧ ¬ IsInvertible T := by
  sorry

/-- 5C.6 For {lit}`F = ℂ`: invariant subspaces of every dimension
{lit}`k ≤ dim V` exist. -/
theorem exercise_5C_6 {V : Type*} [AddCommGroup V] [Module ℂ V]
    [Finite ℂ V] (T : V →ₗ[ℂ] V) (k : ℕ) (hk : k ≤ finrank ℂ V) :
    ∃ U : Submodule ℂ V, InvariantUnder T U ∧ finrank ℂ U = k := by
  sorry

/-- 5C.7 (a) For each {lit}`v ∈ V` there is a unique monic polynomial
{lit}`p_v` of smallest degree with {lit}`p_v(T)v = 0`. -/
theorem exercise_5C_7a [Finite F V] (T : V →ₗ[F] V) (v : V) :
    ∃! p : Polynomial F, p.Monic ∧ aeval T p v = 0 ∧
      ∀ q : Polynomial F, q.Monic → aeval T q v = 0 →
        p.degree ≤ q.degree := by
  sorry

/-- 5C.7 (b) The minimal polynomial of {lit}`T` is a polynomial multiple of
each {lit}`p_v`. -/
theorem exercise_5C_7b [Finite F V] (T : V →ₗ[F] V) (v : V)
    (p : Polynomial F) (hp : p.Monic) (hpv : aeval T p v = 0)
    (hmin : ∀ q : Polynomial F, q.Monic → aeval T q v = 0 →
      p.degree ≤ q.degree) :
    p ∣ minpoly F T := by
  sorry

/-- 5C.8 (a) If {lit}`F = ℝ` and {lit}`T²v + 2Tv = −2v` for some
{lit}`v ≠ 0`, then {lit}`T` has no upper-triangular matrix with respect to
any basis. -/
theorem exercise_5C_8a {V : Type*} [AddCommGroup V] [Module ℝ V]
    [Finite ℝ V] (T : V →ₗ[ℝ] V) (v : V) (hv : v ≠ 0)
    (h : T (T v) + 2 • T v = -(2 • v)) :
    ¬ ∃ (n : ℕ) (w : Fin n → V) (hw : IsBasis ℝ w),
      IsUpperTriangular (matrixOf hw hw T) := by
  sorry

/-- 5C.8 (b) If {lit}`F = ℂ` and the same relation holds, then every
upper-triangular matrix of {lit}`T` has {lit}`−1 + i` or {lit}`−1 − i` on
its diagonal. -/
theorem exercise_5C_8b {V : Type*} [AddCommGroup V] [Module ℂ V]
    [Finite ℂ V] (T : V →ₗ[ℂ] V) (v : V) (hv : v ≠ 0)
    (h : T (T v) + 2 • T v = -(2 • v))
    {n : ℕ} {w : Fin n → V} (hw : IsBasis ℂ w)
    (hA : IsUpperTriangular (matrixOf hw hw T)) :
    ∃ k, matrixOf hw hw T k k = -1 + Complex.I ∨
      matrixOf hw hw T k k = -1 - Complex.I := by
  sorry

/-- 5C.9 Every square matrix with complex entries is similar to an
upper-triangular matrix. -/
theorem exercise_5C_9 {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ) :
    ∃ A : Matrix (Fin n) (Fin n) ℂ, IsUnit A ∧
      IsUpperTriangular (A⁻¹ * B * A) := by
  sorry

/-- A square matrix is *lower triangular* if all entries above the diagonal
are {lit}`0`. -/
def IsLowerTriangular {n : ℕ} (A : Matrix (Fin n) (Fin n) F) : Prop :=
  ∀ j k, j < k → A j k = 0

/-- 5C.10 The lower-triangular analogue of 5.39. -/
theorem exercise_5C_10 {n : ℕ} {v : Fin n → V} (hv : IsBasis F v)
    (T : V →ₗ[F] V) :
    [IsLowerTriangular (matrixOf hv hv T),
      ∀ k : Fin n, InvariantUnder T (Submodule.span F (v '' {i | k ≤ i})),
      ∀ k : Fin n, T (v k) ∈ Submodule.span F (v '' {i | k ≤ i})].TFAE := by
  sorry

/-- 5C.11 For {lit}`F = ℂ`: every operator has a lower-triangular matrix
with respect to some basis. -/
theorem exercise_5C_11 {V : Type*} [AddCommGroup V] [Module ℂ V]
    [Finite ℂ V] (T : V →ₗ[ℂ] V) :
    ∃ (n : ℕ) (v : Fin n → V) (hv : IsBasis ℂ v),
      IsLowerTriangular (matrixOf hv hv T) := by
  sorry

/-- 5C.12 (a) If {lit}`T` has an upper-triangular matrix with respect to some
basis of {lit}`V` and {lit}`U` is invariant, then {lit}`T|_U` has an
upper-triangular matrix with respect to some basis of {lit}`U`. -/
theorem exercise_5C_12a [Finite F V] (T : V →ₗ[F] V)
    (h : ∃ (n : ℕ) (v : Fin n → V) (hv : IsBasis F v),
      IsUpperTriangular (matrixOf hv hv T))
    (U : Submodule F V) (hU : InvariantUnder T U) :
    ∃ (n : ℕ) (u : Fin n → U) (hu : IsBasis F u),
      IsUpperTriangular (matrixOf hu hu hU.restrict) := by
  sorry

/-- 5C.12 (b) Under the same hypotheses, the quotient operator {lit}`T/U`
has an upper-triangular matrix with respect to some basis of {lit}`V/U`. -/
theorem exercise_5C_12b [Finite F V] (T : V →ₗ[F] V)
    (h : ∃ (n : ℕ) (v : Fin n → V) (hv : IsBasis F v),
      IsUpperTriangular (matrixOf hv hv T))
    (U : Submodule F V) (hU : InvariantUnder T U) :
    ∃ (n : ℕ) (w : Fin n → V ⧸ U) (hw : IsBasis F w),
      IsUpperTriangular (matrixOf hw hw
        (exercise_5A_38_quotient_op T U hU)) := by
  sorry

/-- 5C.13 Conversely: if {lit}`T|_U` and {lit}`T/U` both have
upper-triangular matrices, then so does {lit}`T`. -/
theorem exercise_5C_13 [Finite F V] (T : V →ₗ[F] V) (U : Submodule F V)
    (hU : InvariantUnder T U)
    (h1 : ∃ (n : ℕ) (u : Fin n → U) (hu : IsBasis F u),
      IsUpperTriangular (matrixOf hu hu hU.restrict))
    (h2 : ∃ (n : ℕ) (w : Fin n → V ⧸ U) (hw : IsBasis F w),
      IsUpperTriangular (matrixOf hw hw
        (exercise_5A_38_quotient_op T U hU))) :
    ∃ (n : ℕ) (v : Fin n → V) (hv : IsBasis F v),
      IsUpperTriangular (matrixOf hv hv T) := by
  sorry

/-- 5C.14 {lit}`T` has an upper-triangular matrix with respect to some basis
of {lit}`V` iff the dual operator {lit}`T′` has an upper-triangular matrix
with respect to some basis of {lit}`V′`. -/
theorem exercise_5C_14 [Finite F V] (T : V →ₗ[F] V) :
    (∃ (n : ℕ) (v : Fin n → V) (hv : IsBasis F v),
      IsUpperTriangular (matrixOf hv hv T)) ↔
    ∃ (n : ℕ) (φ : Fin n → Module.Dual F V) (hφ : IsBasis F φ),
      IsUpperTriangular (matrixOf hφ hφ T.dualMap) := by
  sorry

end LADR.Section_5C
