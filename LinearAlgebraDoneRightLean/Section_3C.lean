import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Ring
import LinearAlgebraDoneRightLean.Section_2A
import LinearAlgebraDoneRightLean.Section_2B
import LinearAlgebraDoneRightLean.Section_2C
import LinearAlgebraDoneRightLean.Section_3A
import LinearAlgebraDoneRightLean.Section_3B
import CompanionHelper

/-!
# Axler, *Linear Algebra Done Right* (4e) — Section 3C: Matrices
-/

namespace LADR.Section_3C

open LADR.Section_2A (Spans)
open LADR.Section_2B (IsBasis)
open Module (Finite finrank)

variable {F : Type*} [Field F]
  {U V W : Type*} [AddCommGroup U] [Module F U]
    [AddCommGroup V] [Module F V]
    [AddCommGroup W] [Module F W]

/-! 3.29 Definition: matrix, {lit}`A_{j,k}`

An {lit}`m`-by-{lit}`n` matrix with entries in {lit}`F` is encoded in mathlib
as {lit}`Matrix (Fin m) (Fin n) F`, which unfolds to {lit}`Fin m → Fin n → F`.
The notation {lit}`A j k` denotes the entry in row {lit}`j`, column {lit}`k`. -/

example (m n : ℕ) : Type _ := Matrix (Fin m) (Fin n) F

example (m n : ℕ) (A : Matrix (Fin m) (Fin n) F) (j : Fin m) (k : Fin n) : F :=
  A j k

/-! 3.30 Example: {lit}`A_{j,k}` equals entry in row {lit}`j`, column {lit}`k` -/

example : (!![8, 4, (5 - 3 * Complex.I : ℂ); 1, 9, 7] : Matrix (Fin 2) (Fin 3) ℂ)
    1 2 = 7 := by
  rfl

/-! 3.31 Definition: matrix of a linear map, {lit}`ℳ(T)`

Given bases {lit}`v₁, …, vₙ` of {lit}`V` and {lit}`w₁, …, wₘ` of {lit}`W`, the
matrix {lit}`ℳ(T)` is the {lit}`m`-by-{lit}`n` matrix with entries
{lit}`A_{j,k}` defined by {lit}`T vₖ = ∑ⱼ A_{j,k} wⱼ`.

In mathlib this is {name}`LinearMap.toMatrix`, which we wrap to use this
project's {name}`LADR.Section_2B.IsBasis`. -/

noncomputable def matrixOf {m n : ℕ}
    (v : Fin n → V) (w : Fin m → W)
    (hv : IsBasis F v) (hw : IsBasis F w)
    (T : V →ₗ[F] W) : Matrix (Fin m) (Fin n) F :=
  LinearMap.toMatrix hv.toModuleBasis hw.toModuleBasis T

/-- The defining property of {lit}`ℳ(T)`: column {lit}`k` of the matrix gives
the coefficients of {lit}`T vₖ` in basis {lit}`w`. -/
theorem matrixOf_apply {m n : ℕ}
    (v : Fin n → V) (w : Fin m → W)
    (hv : IsBasis F v) (hw : IsBasis F w)
    (T : V →ₗ[F] W) (j : Fin m) (k : Fin n) :
    matrixOf v w hv hw T j k = hw.toModuleBasis.repr (T (v k)) j := by
  simp [matrixOf, LinearMap.toMatrix_apply]

/-- Equivalently: {lit}`T vₖ = ∑ⱼ A_{j,k} wⱼ` (Axler's defining equation). -/
theorem matrixOf_spec {m n : ℕ}
    (v : Fin n → V) (w : Fin m → W)
    (hv : IsBasis F v) (hw : IsBasis F w)
    (T : V →ₗ[F] W) (k : Fin n) :
    T (v k) = ∑ j, matrixOf v w hv hw T j k • w j := by
  have h : ∀ j, hw.toModuleBasis j = w j := IsBasis.toModuleBasis_apply hw
  have hsum : T (v k) = ∑ j, hw.toModuleBasis.repr (T (v k)) j • w j := by
    have hb := hw.toModuleBasis.sum_repr (T (v k))
    conv_lhs => rw [← hb]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [h]
  rw [hsum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [matrixOf_apply]

/-! 3.32 Example: matrix of a linear map from {lit}`F²` to {lit}`F³`

For {lit}`T(x, y) = (x + 3y, 2x + 5y, 7x + 9y)` with standard bases,
{lit}`ℳ(T) = [[1, 3], [2, 5], [7, 9]]`. -/

/-- The standard basis of {lit}`Fⁿ` packaged as an {name}`IsBasis`. -/
theorem isBasis_stdBasis (n : ℕ) :
    IsBasis F (fun k : Fin n => (Pi.single k 1 : Fin n → F)) := by
  constructor
  · rw [Fintype.linearIndependent_iff]
    intro a ha j
    have hj := congrFun ha j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Pi.single_apply, Pi.zero_apply] at hj
    rw [Finset.sum_eq_single j] at hj
    · simpa using hj
    · intros i _ hij
      rw [if_neg (fun h => hij h.symm)]; ring
    · intro h; exact absurd (Finset.mem_univ j) h
  · rw [Spans, eq_top_iff]
    intro v _
    rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨v, ?_⟩
    funext j
    rw [Finset.sum_apply, Finset.sum_eq_single j]
    · simp
    · intros i _ hij
      show v i • (Pi.single i (1 : F) : Fin n → F) j = 0
      simp [hij.symm]
    · intro h; exact absurd (Finset.mem_univ j) h

/-! 3.33 Example: matrix of the differentiation map from {lit}`𝒫₃(ℝ)` to
{lit}`𝒫₂(ℝ)`.

With the standard bases {lit}`1, x, x², x³` and {lit}`1, x, x²`, the matrix
of {lit}`D` is the 3-by-4 matrix
{lit}`[[0,1,0,0],[0,0,2,0],[0,0,0,3]]`. (Stated as an exercise.) -/

/-! 3.34 Definition: matrix addition (mathlib provides this pointwise on
{lit}`Matrix`). -/

example {m n : ℕ} (A C : Matrix (Fin m) (Fin n) F) (j : Fin m) (k : Fin n) :
    (A + C) j k = A j k + C j k := by simp

/-! 3.35 Matrix of the sum of linear maps -/

theorem matrixOf_add {m n : ℕ}
    (v : Fin n → V) (w : Fin m → W)
    (hv : IsBasis F v) (hw : IsBasis F w)
    (S T : V →ₗ[F] W) :
    matrixOf v w hv hw (S + T) = matrixOf v w hv hw S + matrixOf v w hv hw T :=
  (LinearMap.toMatrix hv.toModuleBasis hw.toModuleBasis).map_add S T

/-! 3.36 Definition: scalar multiplication of a matrix (mathlib pointwise). -/

example {m n : ℕ} (lam : F) (A : Matrix (Fin m) (Fin n) F)
    (j : Fin m) (k : Fin n) : (lam • A) j k = lam • A j k := rfl

/-! 3.37 Example: matrix arithmetic -/

example : ((2 : ℝ) • (!![3, 1, 4; -1, 5, 9] : Matrix (Fin 2) (Fin 3) ℝ) +
    !![2, 6, 2; 10, 1, 6])
    = !![8, 8, 10; 8, 11, 24] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> ring

/-! 3.38 Matrix of a scalar times a linear map -/

theorem matrixOf_smul {m n : ℕ}
    (v : Fin n → V) (w : Fin m → W)
    (hv : IsBasis F v) (hw : IsBasis F w)
    (lam : F) (T : V →ₗ[F] W) :
    matrixOf v w hv hw (lam • T) = lam • matrixOf v w hv hw T :=
  (LinearMap.toMatrix hv.toModuleBasis hw.toModuleBasis).map_smul lam T

/-! 3.39 Notation: {lit}`F^{m,n}` is {lit}`Matrix (Fin m) (Fin n) F`. -/

example (m n : ℕ) : Type _ := Matrix (Fin m) (Fin n) F

/-! 3.40 {lit}`dim F^{m,n} = mn` -/

@[avoiding Module.finrank_matrix]
theorem finrank_matrix (m n : ℕ) :
    finrank F (Matrix (Fin m) (Fin n) F) = m * n := by
  show finrank F (Fin m → Fin n → F) = m * n
  rw [Module.finrank_pi_fintype (R := F)]
  simp

/-! 3.41 Definition: matrix multiplication

In mathlib, this is the {lit}`*` operation on {lit}`Matrix`, where
{lit}`(A * B) j k = ∑ r, A j r * B r k`. -/

example {m n p : ℕ} (A : Matrix (Fin m) (Fin n) F) (B : Matrix (Fin n) (Fin p) F)
    (j : Fin m) (k : Fin p) : (A * B) j k = ∑ r, A j r * B r k := by
  simp [Matrix.mul_apply]

/-! 3.42 Example: matrix multiplication -/

example :
    ((!![1, 2; 3, 4; 5, 6] : Matrix (Fin 3) (Fin 2) ℝ) *
      (!![6, 5, 4, 3; 2, 1, 0, -1] : Matrix (Fin 2) (Fin 4) ℝ)) =
    !![10, 7, 4, 1; 26, 19, 12, 5; 42, 31, 20, 9] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply] <;> ring

/-! 3.43 Matrix of product of linear maps -/

theorem matrixOf_comp {p m n : ℕ}
    (u : Fin p → U) (v : Fin n → V) (w : Fin m → W)
    (hu : IsBasis F u) (hv : IsBasis F v) (hw : IsBasis F w)
    (S : V →ₗ[F] W) (T : U →ₗ[F] V) :
    matrixOf u w hu hw (S ∘ₗ T) = matrixOf v w hv hw S * matrixOf u v hu hv T := by
  classical
  simp [matrixOf, LinearMap.toMatrix_comp hu.toModuleBasis hv.toModuleBasis
    hw.toModuleBasis S T]

/-! 3.44 Notation: {lit}`A_{j,·}` and {lit}`A_{·,k}` (rows and columns).
Encoded by partial application: row {lit}`j` is {lit}`A j`, column {lit}`k`
is {lit}`fun j => A j k`. -/

example {m n : ℕ} (A : Matrix (Fin m) (Fin n) F) (j : Fin m) : Fin n → F := A j
example {m n : ℕ} (A : Matrix (Fin m) (Fin n) F) (k : Fin n) : Fin m → F :=
  fun j => A j k

/-! 3.45 Example: row and column -/

example :
    ((!![8, 4, 5; 1, 9, 7] : Matrix (Fin 2) (Fin 3) F) 1) = ![1, 9, 7] := by
  ext j; fin_cases j <;> rfl

example :
    (fun j => (!![8, 4, 5; 1, 9, 7] : Matrix (Fin 2) (Fin 3) F) j 1) = ![4, 9] := by
  ext j; fin_cases j <;> rfl

/-! 3.46 Entry of matrix product equals row times column

{lit}`(A * B) j k = ∑ r, (A j) r * B r k`, which is the dot product of
{lit}`row j of A` with {lit}`column k of B`. -/

theorem matrix_mul_entry {m n p : ℕ}
    (A : Matrix (Fin m) (Fin n) F) (B : Matrix (Fin n) (Fin p) F)
    (j : Fin m) (k : Fin p) :
    (A * B) j k = ∑ r, A j r * B r k := by
  simp [Matrix.mul_apply]

/-! 3.48 Column of matrix product equals matrix times column -/

theorem matrix_mul_col {m n p : ℕ}
    (A : Matrix (Fin m) (Fin n) F) (B : Matrix (Fin n) (Fin p) F) (k : Fin p) :
    (fun j => (A * B) j k) = fun j => ∑ r, A j r * B r k := by
  funext j; rw [matrix_mul_entry]

/-! 3.50 Linear combination of columns

{lit}`A b = ∑ k, b k • (column k of A)`. -/

theorem matrix_mul_eq_sum_columns {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) F) (b : Fin n → F) :
    (fun j => ∑ k, A j k * b k) =
      ∑ k, b k • (fun j => A j k) := by
  funext j
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  ring

/-! 3.51 Matrix multiplication as linear combinations of columns or rows -/

/-- (a) Column {lit}`k` of {lit}`C * R` is a linear combination of columns of
{lit}`C`, with coefficients from column {lit}`k` of {lit}`R`. -/
theorem mul_column_eq_linear_combination_columns {m c n : ℕ}
    (C : Matrix (Fin m) (Fin c) F) (R : Matrix (Fin c) (Fin n) F) (k : Fin n) :
    (fun j => (C * R) j k) = ∑ r, R r k • (fun j => C j r) := by
  rw [matrix_mul_col]
  exact matrix_mul_eq_sum_columns C (fun r => R r k)

/-- (b) Row {lit}`j` of {lit}`C * R` is a linear combination of rows of
{lit}`R`, with coefficients from row {lit}`j` of {lit}`C`. -/
theorem mul_row_eq_linear_combination_rows {m c n : ℕ}
    (C : Matrix (Fin m) (Fin c) F) (R : Matrix (Fin c) (Fin n) F) (j : Fin m) :
    (C * R) j = ∑ r, C j r • R r := by
  funext k
  rw [matrix_mul_entry]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

/-! 3.52 Definition: column rank, row rank -/

/-- Column rank: dimension of the span of the columns of {lit}`A` in
{lit}`Fin m → F`. -/
noncomputable def columnRank {m n : ℕ} (A : Matrix (Fin m) (Fin n) F) : ℕ :=
  finrank F (Submodule.span F (Set.range (fun k : Fin n => (fun j => A j k))))

/-- Row rank: dimension of the span of the rows of {lit}`A` in
{lit}`Fin n → F`. -/
noncomputable def rowRank {m n : ℕ} (A : Matrix (Fin m) (Fin n) F) : ℕ :=
  finrank F (Submodule.span F (Set.range (fun j : Fin m => A j)))

/-! 3.54 Definition: transpose, {lit}`Aᵀ`

In mathlib this is {name}`Matrix.transpose`. -/

example {m n : ℕ} (A : Matrix (Fin m) (Fin n) F) : Matrix (Fin n) (Fin m) F :=
  A.transpose

example {m n : ℕ} (A : Matrix (Fin m) (Fin n) F) (j : Fin m) (k : Fin n) :
    A.transpose k j = A j k := rfl

/-! 3.55 Example: transpose -/
example :
    (!![5, -7; 3, 8; -4, 2] : Matrix (Fin 3) (Fin 2) ℝ).transpose =
      !![5, 3, -4; -7, 8, 2] := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

/-! 3.56 Column–row factorization

If {lit}`A` is {lit}`m`-by-{lit}`n` with column rank {lit}`c ≥ 1`, then there
exist {lit}`C` ({lit}`m`-by-{lit}`c`) and {lit}`R` ({lit}`c`-by-{lit}`n`)
with {lit}`A = C * R`. -/

theorem column_row_factorization {m n : ℕ} (A : Matrix (Fin m) (Fin n) F)
    (_hc : 1 ≤ columnRank A) :
    ∃ (c : ℕ) (C : Matrix (Fin m) (Fin c) F) (R : Matrix (Fin c) (Fin n) F),
      c = columnRank A ∧ A = C * R := by
  classical
  -- The columns of A and their span U.
  let cols : Fin n → (Fin m → F) := fun k j => A j k
  let U : Submodule F (Fin m → F) := Submodule.span F (Set.range cols)
  haveI : Module.Finite F U :=
    Module.Finite.of_injective U.subtype Subtype.val_injective
  -- A basis b of U.
  obtain ⟨c, b, hb_basis⟩ :=
    LADR.Section_2B.exists_basis (F := F) (V := U)
  have hc_eq : c = columnRank A :=
    LADR.Section_2C.isBasis_card_eq_finrank b hb_basis
  -- Each column of A lives in U.
  have h_cols_in : ∀ k, cols k ∈ U :=
    fun k => Submodule.subset_span ⟨k, rfl⟩
  -- C: each column of C is a basis vector (lifted to {lit}`Fin m → F`).
  let C : Matrix (Fin m) (Fin c) F := fun j k => (b k : Fin m → F) j
  -- R: column k of R holds the coordinates of {lit}`cols k` in basis b.
  let R : Matrix (Fin c) (Fin n) F := fun r k =>
    hb_basis.toModuleBasis.repr ⟨cols k, h_cols_in k⟩ r
  refine ⟨c, C, R, hc_eq, ?_⟩
  ext j k
  show A j k = ∑ r, C j r * R r k
  -- Lift the basis representation back to {lit}`Fin m → F`.
  have hb_eq : ∀ r, hb_basis.toModuleBasis r = b r :=
    IsBasis.toModuleBasis_apply hb_basis
  have hsr := hb_basis.toModuleBasis.sum_repr ⟨cols k, h_cols_in k⟩
  have hsr_lift :
      (∑ r, hb_basis.toModuleBasis.repr ⟨cols k, h_cols_in k⟩ r •
          (b r : Fin m → F))
        = cols k := by
    have h := congrArg Subtype.val hsr
    rw [Submodule.coe_sum] at h
    simp_rw [Submodule.coe_smul_of_tower, hb_eq] at h
    exact h
  -- Evaluate at j and rearrange.
  have hj := congrFun hsr_lift j
  rw [Finset.sum_apply] at hj
  simp_rw [Pi.smul_apply, smul_eq_mul] at hj
  -- hj : ∑ r, b.repr ⟨cols k, ·⟩ r * (b r) j = (cols k) j
  have hAj : A j k = (cols k) j := rfl
  rw [hAj, ← hj]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  show hb_basis.toModuleBasis.repr ⟨cols k, h_cols_in k⟩ r *
      (b r : Fin m → F) j =
    (b r : Fin m → F) j *
      hb_basis.toModuleBasis.repr ⟨cols k, h_cols_in k⟩ r
  ring

/-! 3.57 Column rank equals row rank -/

/-- Helper: row {lit}`j` of {lit}`C * R` lies in the span of the rows of
{lit}`R`. -/
private theorem mul_row_in_row_span {m c n : ℕ}
    (C : Matrix (Fin m) (Fin c) F) (R : Matrix (Fin c) (Fin n) F) (j : Fin m) :
    (C * R) j ∈ Submodule.span F (Set.range (fun r : Fin c => R r)) := by
  rw [mul_row_eq_linear_combination_rows]
  apply Submodule.sum_mem
  intro r _
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨r, rfl⟩)

/-- Helper: {lit}`columnRank A = 0` implies {lit}`A = 0`. -/
private theorem columnRank_zero_iff_eq_zero {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) F) : columnRank A = 0 ↔ A = 0 := by
  classical
  haveI : Module.Finite F
      (Submodule.span F
        (Set.range (fun k : Fin n => fun j : Fin m => A j k))) := by
    apply Module.Finite.of_injective
      (Submodule.span F (Set.range
        (fun k : Fin n => fun j : Fin m => A j k))).subtype
    exact Subtype.val_injective
  constructor
  · intro hc
    have hspan_bot : Submodule.span F
        (Set.range (fun k : Fin n => fun j : Fin m => A j k)) = ⊥ := by
      rw [← Submodule.finrank_eq_zero]
      exact hc
    rw [Submodule.span_eq_bot] at hspan_bot
    ext j k
    have hcolk : (fun j' : Fin m => A j' k) = 0 := hspan_bot _ ⟨k, rfl⟩
    have hjk := congrFun hcolk j
    show A j k = (0 : Matrix (Fin m) (Fin n) F) j k
    simp [hjk]
  · intro hA
    subst hA
    show finrank F (Submodule.span F
      (Set.range (fun k : Fin n => fun j : Fin m =>
        (0 : Matrix (Fin m) (Fin n) F) j k))) = 0
    have hbot : Submodule.span F (Set.range
        (fun k : Fin n => fun j : Fin m =>
          (0 : Matrix (Fin m) (Fin n) F) j k)) = ⊥ := by
      rw [Submodule.span_eq_bot]
      rintro x ⟨k, rfl⟩; funext j; rfl
    rw [hbot]
    simp

/-- Helper inequality: row rank is at most column rank, valid for any
matrix. -/
private theorem rowRank_le_columnRank {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) F) : rowRank A ≤ columnRank A := by
  by_cases hc1 : 1 ≤ columnRank A
  · -- Use the column-row factorization {lit}`A = C * R`.
    obtain ⟨c, C, R, hc_eq, hA⟩ := column_row_factorization A hc1
    -- Every row of A lies in the span of the rows of R.
    have h_sub : Submodule.span F (Set.range (fun j : Fin m => A j)) ≤
        Submodule.span F (Set.range (fun r : Fin c => R r)) := by
      rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      rw [hA]; exact mul_row_in_row_span C R j
    -- Span of the rows of R has dimension ≤ c.
    have h_R_le : finrank F (Submodule.span F
        (Set.range (fun r : Fin c => R r))) ≤ c := by
      have := finrank_range_le_card (R := F) (fun r : Fin c => R r)
      simpa using this
    calc rowRank A
        ≤ finrank F (Submodule.span F
            (Set.range (fun r : Fin c => R r))) :=
          Submodule.finrank_mono h_sub
      _ ≤ c := h_R_le
      _ = columnRank A := hc_eq
  · -- {lit}`columnRank A = 0` forces {lit}`A = 0`, hence {lit}`rowRank A = 0`.
    have hc0 : columnRank A = 0 := by omega
    have hAzero : A = 0 := (columnRank_zero_iff_eq_zero A).mp hc0
    have hr0 : rowRank A = 0 := by
      rw [hAzero]
      show finrank F (Submodule.span F (Set.range
        (fun j : Fin m => (0 : Matrix (Fin m) (Fin n) F) j))) = 0
      have hbot : Submodule.span F (Set.range
          (fun j : Fin m => (0 : Matrix (Fin m) (Fin n) F) j)) = ⊥ := by
        rw [Submodule.span_eq_bot]
        rintro x ⟨j, rfl⟩; rfl
      rw [hbot]; simp
    omega

/-- Rows of {lit}`Aᵀ` equal columns of {lit}`A` (and vice versa), so the
ranks swap. -/
private theorem rowRank_transpose {m n : ℕ} (A : Matrix (Fin m) (Fin n) F) :
    rowRank A.transpose = columnRank A := by
  show finrank F (Submodule.span F (Set.range
    (fun k : Fin n => A.transpose k))) =
      finrank F (Submodule.span F (Set.range
        (fun k : Fin n => fun j : Fin m => A j k)))
  rfl

private theorem columnRank_transpose {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) F) :
    columnRank A.transpose = rowRank A := by
  show finrank F (Submodule.span F (Set.range
    (fun j : Fin m => fun k : Fin n => A.transpose k j))) =
      finrank F (Submodule.span F (Set.range (fun j : Fin m => A j)))
  rfl

theorem columnRank_eq_rowRank {m n : ℕ} (A : Matrix (Fin m) (Fin n) F) :
    columnRank A = rowRank A := by
  have h1 : rowRank A ≤ columnRank A := rowRank_le_columnRank A
  have h2 : rowRank A.transpose ≤ columnRank A.transpose :=
    rowRank_le_columnRank A.transpose
  rw [rowRank_transpose, columnRank_transpose] at h2
  omega

/-! 3.58 Definition: rank -/

noncomputable def rank {m n : ℕ} (A : Matrix (Fin m) (Fin n) F) : ℕ :=
  columnRank A

/-! # Exercises -/

/-- 3C.1 -/
theorem exercise_3C_1 [Finite F V] [Finite F W] {m n : ℕ}
    (v : Fin n → V) (w : Fin m → W) (hv : IsBasis F v) (hw : IsBasis F w)
    (T : V →ₗ[F] W) :
    finrank F (LinearMap.range T) ≤
      Nat.card {p : Fin m × Fin n // matrixOf v w hv hw T p.1 p.2 ≠ 0} := by
  sorry

/-- 3C.2 -/
theorem exercise_3C_2 [Finite F V] [Finite F W]
    (hV : 0 < finrank F V) (hW : 0 < finrank F W) (T : V →ₗ[F] W) :
    finrank F (LinearMap.range T) = 1 ↔
      ∃ (m n : ℕ) (v : Fin n → V) (w : Fin m → W)
        (hv : IsBasis F v) (hw : IsBasis F w),
        ∀ j k, matrixOf v w hv hw T j k = 1 := by
  sorry

/-- 3C.3 (a) {lit}`ℳ(S + T) = ℳ(S) + ℳ(T)` -/
theorem exercise_3C_3a {m n : ℕ}
    (v : Fin n → V) (w : Fin m → W) (hv : IsBasis F v) (hw : IsBasis F w)
    (S T : V →ₗ[F] W) :
    matrixOf v w hv hw (S + T) = matrixOf v w hv hw S + matrixOf v w hv hw T :=
  matrixOf_add v w hv hw S T

/-- 3C.3 (b) {lit}`ℳ(λT) = λ ℳ(T)` -/
theorem exercise_3C_3b {m n : ℕ}
    (v : Fin n → V) (w : Fin m → W) (hv : IsBasis F v) (hw : IsBasis F w)
    (lam : F) (T : V →ₗ[F] W) :
    matrixOf v w hv hw (lam • T) = lam • matrixOf v w hv hw T :=
  matrixOf_smul v w hv hw lam T

/-- 3C.4 Find bases of {lit}`𝒫₃(ℝ)` and {lit}`𝒫₂(ℝ)` for which the matrix of
the differentiation map is {lit}`[[1,0,0,0],[0,1,0,0],[0,0,1,0]]`. -/
theorem exercise_3C_4 :
    ∃ (v : Fin 4 → Polynomial.degreeLT ℝ 4) (w : Fin 3 → Polynomial.degreeLT ℝ 3)
      (hv : IsBasis ℝ v) (hw : IsBasis ℝ w),
      ∃ (D : Polynomial.degreeLT ℝ 4 →ₗ[ℝ] Polynomial.degreeLT ℝ 3),
        (∀ p, (D p : Polynomial ℝ) = (p : Polynomial ℝ).derivative) ∧
        matrixOf v w hv hw D = !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0] := by
  sorry

/-- 3C.5 -/
theorem exercise_3C_5 [Finite F V] [Finite F W] (T : V →ₗ[F] W) :
    ∃ (m n : ℕ) (v : Fin n → V) (w : Fin m → W)
      (hv : IsBasis F v) (hw : IsBasis F w),
      ∀ j k, matrixOf v w hv hw T j k =
        if (j : ℕ) = k ∧ (j : ℕ) < finrank F (LinearMap.range T) then 1 else 0 := by
  sorry

/-- 3C.6 -/
theorem exercise_3C_6 [Finite F W] {m : ℕ} (hm : 1 ≤ m)
    (v : Fin m → V) (hv : IsBasis F v) (T : V →ₗ[F] W) :
    ∃ (n : ℕ) (w : Fin n → W) (hw : IsBasis F w) (hn : 1 ≤ n) (a : F),
      ∀ j : Fin n,
        matrixOf v w hv hw T j ⟨0, hm⟩ = if (j : ℕ) = 0 then a else 0 := by
  sorry

/-- 3C.7 -/
theorem exercise_3C_7 [Finite F V] {n : ℕ} (hn : 1 ≤ n)
    (w : Fin n → W) (hw : IsBasis F w) (T : V →ₗ[F] W) :
    ∃ (m : ℕ) (v : Fin m → V) (hv : IsBasis F v) (hm : 1 ≤ m) (a : F),
      ∀ k : Fin m,
        matrixOf v w hv hw T ⟨0, hn⟩ k = if (k : ℕ) = 0 then a else 0 := by
  sorry

/-- 3C.8 Row version of 3.48 -/
theorem exercise_3C_8 {m n p : ℕ}
    (A : Matrix (Fin m) (Fin n) F) (B : Matrix (Fin n) (Fin p) F) (j : Fin m) :
    (A * B) j = fun k => ∑ r, A j r * B r k := by
  sorry

/-- 3C.9 Row version of 3.50 -/
theorem exercise_3C_9 {n p : ℕ} (a : Fin n → F) (B : Matrix (Fin n) (Fin p) F) :
    (fun k => ∑ r, a r * B r k) = ∑ r, a r • B r := by
  sorry

/-- 3C.10 -/
theorem exercise_3C_10 :
    ∃ A B : Matrix (Fin 2) (Fin 2) ℝ, A * B ≠ B * A := by
  sorry

/-- 3C.11 Distributive properties (mathlib's {name}`Matrix` already has
these). -/
example {m n p : ℕ} (A : Matrix (Fin m) (Fin n) F)
    (B C : Matrix (Fin n) (Fin p) F) :
    A * (B + C) = A * B + A * C := Matrix.mul_add A B C
example {m n p : ℕ} (D E : Matrix (Fin m) (Fin n) F)
    (F' : Matrix (Fin n) (Fin p) F) :
    (D + E) * F' = D * F' + E * F' := Matrix.add_mul D E F'

/-- 3C.12 Associativity (mathlib's {name}`Matrix` already has it). -/
example {m n p q : ℕ}
    (A : Matrix (Fin m) (Fin n) F) (B : Matrix (Fin n) (Fin p) F)
    (C : Matrix (Fin p) (Fin q) F) :
    (A * B) * C = A * (B * C) := Matrix.mul_assoc A B C

/-- 3C.13 Entry of {lit}`A³` -/
theorem exercise_3C_13 {n : ℕ} (A : Matrix (Fin n) (Fin n) F) (j k : Fin n) :
    (A * A * A) j k = ∑ p, ∑ r, A j p * A p r * A r k := by
  sorry

/-- 3C.14 Transposition is a linear map. -/
def exercise_3C_14 (m n : ℕ) :
    Matrix (Fin m) (Fin n) F →ₗ[F] Matrix (Fin n) (Fin m) F where
  toFun A := A.transpose
  map_add' := by intros; ext i j; simp [Matrix.transpose]
  map_smul' := by intros; ext i j; simp [Matrix.transpose]

/-- 3C.15 {lit}`(A * C)ᵀ = Cᵀ * Aᵀ` -/
theorem exercise_3C_15 {m n p : ℕ}
    (A : Matrix (Fin m) (Fin n) F) (C : Matrix (Fin n) (Fin p) F) :
    (A * C).transpose = C.transpose * A.transpose := by
  sorry

/-- 3C.16 -/
theorem exercise_3C_16 {m n : ℕ} (A : Matrix (Fin m) (Fin n) F) (hA : A ≠ 0) :
    rank A = 1 ↔
      ∃ (c : Fin m → F) (d : Fin n → F), ∀ j k, A j k = c j * d k := by
  sorry

/-- 3C.17 -/
theorem exercise_3C_17 {n : ℕ} (T : V →ₗ[F] V)
    (u v : Fin n → V) (hu : IsBasis F u) (hv : IsBasis F v) :
    [Function.Injective T,
     LinearIndependent F (fun k : Fin n => (fun j => matrixOf u v hu hv T j k)),
     Spans F (fun k : Fin n => (fun j => matrixOf u v hu hv T j k)),
     Spans F (fun j : Fin n => matrixOf u v hu hv T j),
     LinearIndependent F (fun j : Fin n => matrixOf u v hu hv T j)
    ].Pairwise (fun a b => a ↔ b) := by
  sorry

end LADR.Section_3C
