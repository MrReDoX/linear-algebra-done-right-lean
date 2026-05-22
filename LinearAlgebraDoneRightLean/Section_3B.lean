import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Ring
import LinearAlgebraDoneRightLean.Section_1C
import LinearAlgebraDoneRightLean.Section_2A
import LinearAlgebraDoneRightLean.Section_2B
import LinearAlgebraDoneRightLean.Section_2C
import LinearAlgebraDoneRightLean.Section_3A
import CompanionHelper

/-!
# Axler, *Linear Algebra Done Right* (4e) — Section 3B: Null Spaces and Ranges
-/

namespace LADR.Section_3B

open LADR.Section_2A (Spans)
open LADR.Section_2B (IsBasis)
open LADR.Section_1C (IsDirectSum)
open Module (Finite finrank)

variable {F : Type*} [Field F]
  {U V W : Type*} [AddCommGroup U] [Module F U]
    [AddCommGroup V] [Module F V]
    [AddCommGroup W] [Module F W]

/-! 3.11 Definition: null space, {lit}`null T`

For {lit}`T ∈ ℒ(V, W)`, the null space is {lit}`{v ∈ V : T v = 0}`. In
mathlib this is {name}`LinearMap.ker`, which is a {name}`Submodule`. -/

example (T : V →ₗ[F] W) : Submodule F V := LinearMap.ker T

example (T : V →ₗ[F] W) (v : V) : v ∈ LinearMap.ker T ↔ T v = 0 :=
  LinearMap.mem_ker

/-! 3.12 Example: null space -/

/-! (a) For the zero map {lit}`V → W`, {lit}`null 0 = V`. -/
example : LinearMap.ker (0 : V →ₗ[F] W) = ⊤ := LinearMap.ker_zero

/-- (b) {lit}`φ ∈ ℒ(ℂ³, ℂ)` with {lit}`φ(z₁, z₂, z₃) = z₁ + 2z₂ + 3z₃`. -/
def phi_3_12 : (Fin 3 → ℂ) →ₗ[ℂ] ℂ where
  toFun z := z 0 + 2 * z 1 + 3 * z 2
  map_add' x y := by
    simp only [Pi.add_apply]; ring
  map_smul' a x := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

/-- The null space of {lit}`φ` consists of triples {lit}`(z₁, z₂, z₃)` with
{lit}`z₁ + 2z₂ + 3z₃ = 0`. -/
example (z : Fin 3 → ℂ) :
    z ∈ LinearMap.ker phi_3_12 ↔ z 0 + 2 * z 1 + 3 * z 2 = 0 :=
  LinearMap.mem_ker

/-! (c) {lit}`D ∈ ℒ(𝒫(ℝ))` differentiation. {lit}`null D` = constants. We
record this membership statement (the full {lit}`ker = degreeLT ℝ 1`
equality is an exercise). -/

example (c : ℝ) :
    (Polynomial.C c : Polynomial ℝ) ∈ LinearMap.ker
      (Polynomial.derivative : Polynomial ℝ →ₗ[ℝ] Polynomial ℝ) := by
  rw [LinearMap.mem_ker]; simp

/-! (d) Multiplication by {lit}`X²` has {lit}`null = {0}`. -/

example : LinearMap.ker LADR.Section_3A.multByXSq = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro p hp
  rw [LinearMap.mem_ker] at hp
  -- hp : multByXSq p = 0, i.e. X² * p = 0
  have hX2 : (Polynomial.X ^ 2 : Polynomial ℝ) * p = 0 := hp
  have hX : (Polynomial.X ^ 2 : Polynomial ℝ) ≠ 0 := by
    intro h
    have := congrArg (Polynomial.coeff · 2) h
    simp [Polynomial.coeff_X_pow] at this
  exact (mul_eq_zero.mp hX2).resolve_left hX

/-! (e) Backward shift on {lit}`F^∞ = ℕ → F`: {lit}`null T = {x : ∀ i ≥ 1, x i = 0}`. -/

example (x : ℕ → F) :
    x ∈ LinearMap.ker (LADR.Section_3A.backwardShift (F := F)) ↔
    ∀ i, 1 ≤ i → x i = 0 := by
  rw [LinearMap.mem_ker]
  constructor
  · intro h i hi
    have := congrFun h (i - 1)
    show x i = 0
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    exact this
  · intro h
    funext i
    show x (i + 1) = 0
    exact h (i + 1) (by omega)

/-! 3.13 The null space is a subspace

In mathlib, {name}`LinearMap.ker` already returns a {name}`Submodule`. -/

example (T : V →ₗ[F] W) : Submodule F V := LinearMap.ker T

/-! 3.14 Definition: injective -/

example (T : V → W) : Prop := Function.Injective T

/-! 3.15 {lit}`T` injective iff {lit}`null T = {0}` -/

@[avoiding LinearMap.ker_eq_bot]
theorem injective_iff_ker_eq_bot (T : V →ₗ[F] W) :
    Function.Injective T ↔ LinearMap.ker T = ⊥ := by
  constructor
  · intro hT
    rw [Submodule.eq_bot_iff]
    intro v hv
    rw [LinearMap.mem_ker] at hv
    have : T v = T 0 := by rw [hv, T.map_zero]
    exact hT this
  · intro hker u v huv
    have h : u - v ∈ LinearMap.ker T := by
      rw [LinearMap.mem_ker, T.map_sub, huv, sub_self]
    rw [hker, Submodule.mem_bot] at h
    exact sub_eq_zero.mp h

/-! 3.16 Definition: range, {lit}`range T` -/

example (T : V →ₗ[F] W) : Submodule F W := LinearMap.range T

example (T : V →ₗ[F] W) (w : W) :
    w ∈ LinearMap.range T ↔ ∃ v : V, T v = w := LinearMap.mem_range

/-! 3.17 Example: range -/

/-! (a) Range of zero map. -/
example : LinearMap.range (0 : V →ₗ[F] W) = ⊥ := LinearMap.range_zero

/-- (b) {lit}`T ∈ ℒ(ℝ², ℝ³)` with {lit}`T(x, y) = (2x, 5y, x + y)`. -/
def T_3_17 : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) where
  toFun v := ![2 * v 0, 5 * v 1, v 0 + v 1]
  map_add' x y := by
    funext i; fin_cases i <;>
      simp [Matrix.cons_val_zero, Matrix.cons_val_one] <;> ring
  map_smul' a x := by
    funext i; fin_cases i <;>
      simp [Matrix.cons_val_zero, Matrix.cons_val_one] <;> ring

/-! (c) Range of differentiation on {lit}`𝒫(ℝ)` is all of {lit}`𝒫(ℝ)`. -/

example : LinearMap.range
    (Polynomial.derivative : Polynomial ℝ →ₗ[ℝ] Polynomial ℝ) = ⊤ := by
  rw [LinearMap.range_eq_top]
  intro q
  -- The antiderivative ∑ q.coeff k / (k+1) * X^(k+1) works.
  exact ⟨q.sum (fun n a => Polynomial.C (a / (n + 1)) * Polynomial.X ^ (n + 1)), by
    sorry⟩

/-! 3.18 The range is a subspace (mathlib's {name}`LinearMap.range` is a
{name}`Submodule`). -/

example (T : V →ₗ[F] W) : Submodule F W := LinearMap.range T

/-! 3.19 Definition: surjective -/

example (T : V → W) : Prop := Function.Surjective T

@[avoiding LinearMap.range_eq_top]
theorem surjective_iff_range_eq_top (T : V →ₗ[F] W) :
    Function.Surjective T ↔ LinearMap.range T = ⊤ := by
  constructor
  · intro hT
    rw [eq_top_iff]
    intro w _
    obtain ⟨v, hv⟩ := hT w
    exact ⟨v, hv⟩
  · intro hT w
    have hw : w ∈ LinearMap.range T := by rw [hT]; exact Submodule.mem_top
    exact hw

/-! 3.20 Example: surjectivity depends on the target space (skipped — the
contrast in the textbook is between {lit}`D : 𝒫₅(ℝ) → 𝒫₅(ℝ)` and
{lit}`D : 𝒫₅(ℝ) → 𝒫₄(ℝ)`). -/

/-! 3.21 Fundamental theorem of linear maps

Axler's proof: pick a basis {lit}`u₁, …, u_m` of {lit}`null T`; extend it to
a basis {lit}`u₁, …, u_m, v₁, …, v_n` of {lit}`V`. Show {lit}`T v₁, …, T v_n`
is a basis of {lit}`range T`, so {lit}`dim V = m + n = dim null T + dim range T`. -/

@[avoiding LinearMap.finrank_range_add_finrank_ker]
theorem finrank_ker_add_finrank_range [Finite F V] (T : V →ₗ[F] W) :
    finrank F (LinearMap.ker T) + finrank F (LinearMap.range T) = finrank F V := by
  classical
  -- Basis u of null T.
  obtain ⟨m, u, hu_basis⟩ :=
    LADR.Section_2B.exists_basis (F := F) (V := LinearMap.ker T)
  have hm_ker : m = finrank F (LinearMap.ker T) :=
    LADR.Section_2C.isBasis_card_eq_finrank u hu_basis
  -- Lift u into V and extend to a basis of V.
  let uV : Fin m → V := fun i => (u i : V)
  have hu_li_V : LinearIndependent F uV :=
    hu_basis.1.map' (LinearMap.ker T).subtype
      (LinearMap.ker_eq_bot_of_injective Subtype.val_injective)
  obtain ⟨N, w, hmN, hw_basis, hw_prefix⟩ :=
    LADR.Section_2B.exists_basis_extending uV hu_li_V
  obtain ⟨n, rfl⟩ : ∃ n, N = m + n := ⟨N - m, by omega⟩
  have hmn_V : m + n = finrank F V :=
    LADR.Section_2C.isBasis_card_eq_finrank w hw_basis
  -- The extension piece v₁, …, v_n inside V.
  let vT : Fin n → V := fun j => w (Fin.natAdd m j)
  -- T v_j as an element of range T.
  let TvT : Fin n → LinearMap.range T :=
    fun j => ⟨T (vT j), LinearMap.mem_range_self T (vT j)⟩
  -- Prefix equality of w with uV.
  have hw_prefix_V : ∀ i : Fin m, (w (Fin.castAdd n i) : V) = uV i := by
    intro i
    have h := hw_prefix i
    have hfin : (Fin.castAdd n i : Fin (m + n)) = Fin.castLE hmN i := rfl
    rw [hfin, h]
  -- T u_i = 0 since u_i ∈ ker T.
  have hT_u : ∀ i, T (uV i) = 0 := by
    intro i
    have : uV i ∈ LinearMap.ker T := (u i).property
    rwa [LinearMap.mem_ker] at this
  -- (1) TvT spans range T.
  have hTvT_span : Spans F TvT := by
    rw [Spans, eq_top_iff]
    rintro ⟨y, hy⟩ _
    rw [LinearMap.mem_range] at hy
    obtain ⟨x, hxy⟩ := hy
    -- Expand x in basis w.
    have hx_in : x ∈ Submodule.span F (Set.range w) := by
      rw [(hw_basis.2 : _ = ⊤)]; exact Submodule.mem_top
    rw [Submodule.mem_span_range_iff_exists_fun] at hx_in
    obtain ⟨a, ha⟩ := hx_in
    -- Take aTail = a on the v-block.
    let aTail : Fin n → F := fun j => a (Fin.natAdd m j)
    rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨aTail, ?_⟩
    apply Subtype.ext
    show ((∑ j, aTail j • TvT j : LinearMap.range T) : W) = y
    rw [Submodule.coe_sum]
    show (∑ j, ((aTail j • TvT j : LinearMap.range T) : W)) = y
    have hcast : (∑ j, ((aTail j • TvT j : LinearMap.range T) : W)) =
        ∑ j, aTail j • T (vT j) :=
      Finset.sum_congr rfl (fun _ _ => rfl)
    rw [hcast, ← hxy, ← ha, map_sum]
    simp only [LinearMap.map_smul]
    rw [Fin.sum_univ_add (f := fun k => a k • T (w k))]
    -- u-block in T (a • w) sums to 0 because T u_i = 0.
    have h_uzero : ∑ i : Fin m,
        a (Fin.castAdd n i) • T (w (Fin.castAdd n i)) = (0 : W) := by
      apply Finset.sum_eq_zero
      intro i _
      rw [show (w (Fin.castAdd n i) : V) = uV i from hw_prefix_V i, hT_u i, smul_zero]
    rw [h_uzero, zero_add]
  -- (2) TvT is linearly independent.
  have hTvT_li : LinearIndependent F TvT := by
    rw [Fintype.linearIndependent_iff]
    intro c hc j
    -- Lift the vanishing combination from range T to W.
    have hc_W : ∑ j, c j • T (vT j) = (0 : W) := by
      have hcv := congrArg Subtype.val hc
      rw [Submodule.coe_sum] at hcv
      have hsum : ∑ j, ((c j • TvT j : LinearMap.range T) : W) =
          ∑ j, c j • T (vT j) := Finset.sum_congr rfl (fun _ _ => rfl)
      rw [hsum] at hcv
      exact hcv
    -- So ∑ c j • v_j ∈ ker T.
    have hker : ∑ j, c j • vT j ∈ LinearMap.ker T := by
      rw [LinearMap.mem_ker, map_sum]
      simp only [LinearMap.map_smul]
      exact hc_W
    -- Express it in basis u of ker T.
    have hu_span : Submodule.span F (Set.range u) = ⊤ := hu_basis.2
    have hmem : (⟨∑ j, c j • vT j, hker⟩ : LinearMap.ker T) ∈
        Submodule.span F (Set.range u) := by
      rw [hu_span]; exact Submodule.mem_top
    rw [Submodule.mem_span_range_iff_exists_fun] at hmem
    obtain ⟨d, hd⟩ := hmem
    -- Project hd into V.
    have hd_V : ∑ i, d i • uV i = ∑ j, c j • vT j := by
      have hd' := congrArg Subtype.val hd
      rw [Submodule.coe_sum] at hd'
      have hsum : ∑ i, ((d i • u i : LinearMap.ker T) : V) =
          ∑ i, d i • uV i := Finset.sum_congr rfl (fun _ _ => rfl)
      rw [hsum] at hd'
      exact hd'
    -- Build the combination cw of w which sums to 0.
    let cw : Fin (m + n) → F := Fin.append (-d) c
    have hcw_sum : ∑ k, cw k • w k = 0 := by
      rw [Fin.sum_univ_add (f := fun k => cw k • w k)]
      have hprefix : ∑ i : Fin m, cw (Fin.castAdd n i) • w (Fin.castAdd n i) =
          ∑ i, (-d i) • uV i := by
        apply Finset.sum_congr rfl
        intro i _
        rw [show cw (Fin.castAdd n i) = -d i from Fin.append_left _ _ _,
            show (w (Fin.castAdd n i) : V) = uV i from hw_prefix_V i]
      have htail : ∑ j : Fin n, cw (Fin.natAdd m j) • w (Fin.natAdd m j) =
          ∑ j, c j • vT j := by
        apply Finset.sum_congr rfl
        intro j _
        rw [show cw (Fin.natAdd m j) = c j from Fin.append_right _ _ _]
      rw [hprefix, htail]
      rw [show ∑ i, (-d i) • uV i = -∑ i, d i • uV i from by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl (fun _ _ => by rw [neg_smul])]
      rw [hd_V, neg_add_cancel]
    -- LI of w kills all coefficients of cw.
    have hcw_zero := (Fintype.linearIndependent_iff.mp hw_basis.1) cw hcw_sum
    have hcw_j : c j = cw (Fin.natAdd m j) := (Fin.append_right (-d) c j).symm
    rw [hcw_j]
    exact hcw_zero _
  -- Conclude.
  have hn_range : n = finrank F (LinearMap.range T) :=
    LADR.Section_2C.isBasis_card_eq_finrank TvT ⟨hTvT_li, hTvT_span⟩
  omega

/-! 3.22 Linear map to a lower-dimensional space is not injective -/

@[avoiding LinearMap.exists_ne_zero_of_finrank_lt_of_finrank_lt]
theorem not_injective_of_finrank_lt [Finite F V] [Finite F W]
    (hWV : finrank F W < finrank F V) (T : V →ₗ[F] W) :
    ¬ Function.Injective T := by
  intro hinj
  rw [injective_iff_ker_eq_bot] at hinj
  have hker : finrank F (LinearMap.ker T) = 0 := by rw [hinj]; simp
  have hrange_le : finrank F (LinearMap.range T) ≤ finrank F W :=
    LADR.Section_2C.finrank_submodule_le (LinearMap.range T)
  have := finrank_ker_add_finrank_range T
  omega

/-! 3.23 Example: a linear map {lit}`F⁴ → F³` is not injective. -/

example (T : (Fin 4 → F) →ₗ[F] (Fin 3 → F)) : ¬ Function.Injective T :=
  not_injective_of_finrank_lt (by simp) T

/-! 3.24 Linear map to a higher-dimensional space is not surjective -/

theorem not_surjective_of_finrank_lt [Finite F V] [Finite F W]
    (hVW : finrank F V < finrank F W) (T : V →ₗ[F] W) :
    ¬ Function.Surjective T := by
  intro hsurj
  rw [surjective_iff_range_eq_top] at hsurj
  have hrange : finrank F (LinearMap.range T) = finrank F W := by
    rw [hsurj]
    exact Submodule.topEquiv.finrank_eq
  have hker_le : 0 ≤ finrank F (LinearMap.ker T) := Nat.zero_le _
  have := finrank_ker_add_finrank_range T
  omega

/-! 3.25/3.26 Homogeneous system of linear equations with more variables than
equations has nonzero solutions. -/

theorem homogeneous_system_nonzero_solution {m n : ℕ} (hmn : m < n)
    (A : Fin m → Fin n → F) :
    ∃ x : Fin n → F, x ≠ 0 ∧ ∀ j : Fin m, ∑ k, A j k * x k = 0 := by
  let T : (Fin n → F) →ₗ[F] (Fin m → F) := LADR.Section_3A.fromFnToFm A
  have hT : ¬ Function.Injective T :=
    not_injective_of_finrank_lt (by simpa using hmn) T
  rw [injective_iff_ker_eq_bot] at hT
  have hne : LinearMap.ker T ≠ ⊥ := hT
  obtain ⟨x, hx_ker, hx_ne⟩ := (Submodule.ne_bot_iff _).mp hne
  refine ⟨x, hx_ne, ?_⟩
  intro j
  have hTx : T x = 0 := hx_ker
  have := congrFun hTx j
  show ∑ k, A j k * x k = 0
  exact this

/-! 3.27/3.28 A system of linear equations with more equations than variables
has no solution for some choice of constant terms. -/

theorem more_equations_no_solution {m n : ℕ} (hmn : n < m) (A : Fin m → Fin n → F) :
    ∃ c : Fin m → F, ¬ ∃ x : Fin n → F, ∀ j : Fin m, ∑ k, A j k * x k = c j := by
  let T : (Fin n → F) →ₗ[F] (Fin m → F) := LADR.Section_3A.fromFnToFm A
  have hT : ¬ Function.Surjective T :=
    not_surjective_of_finrank_lt (by simpa using hmn) T
  rw [Function.Surjective] at hT
  push Not at hT
  obtain ⟨c, hc⟩ := hT
  refine ⟨c, ?_⟩
  rintro ⟨x, hx⟩
  exact hc x (funext hx)

/-! # Exercises -/

/-- 3B.1 -/
theorem exercise_3B_1 :
    ∃ (V W : Type) (_ : AddCommGroup V) (_ : Module ℝ V)
      (_ : AddCommGroup W) (_ : Module ℝ W) (T : V →ₗ[ℝ] W),
      finrank ℝ (LinearMap.ker T) = 3 ∧ finrank ℝ (LinearMap.range T) = 2 := by
  sorry

/-- 3B.2 -/
theorem exercise_3B_2 (S T : V →ₗ[F] V)
    (h : LinearMap.range S ≤ LinearMap.ker T) :
    (T ∘ₗ S) ∘ₗ (T ∘ₗ S) = 0 := by
  sorry

/-- 3B.3 The linear map {lit}`T(z₁, …, zₘ) = z₁ v₁ + ⋯ + zₘ vₘ`. -/
def exercise_3B_3_T {m : ℕ} (v : Fin m → V) : (Fin m → F) →ₗ[F] V where
  toFun z := ∑ i, z i • v i
  map_add' x y := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun _ _ => by rw [Pi.add_apply, add_smul])
  map_smul' a x := by
    show ∑ i, (a • x) i • v i = a • ∑ i, x i • v i
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Pi.smul_apply, smul_eq_mul, mul_smul]

/-- 3B.3 (a) {lit}`v` spans {lit}`V` iff the corresponding {lit}`T` is
surjective. -/
theorem exercise_3B_3a {m : ℕ} (v : Fin m → V) :
    Spans F v ↔ Function.Surjective (exercise_3B_3_T (F := F) v) := by
  sorry

/-- 3B.3 (b) {lit}`v` is linearly independent iff the corresponding {lit}`T`
is injective. -/
theorem exercise_3B_3b {m : ℕ} (v : Fin m → V) :
    LinearIndependent F v ↔ Function.Injective (exercise_3B_3_T (F := F) v) := by
  sorry

/-- 3B.4 -/
theorem exercise_3B_4 :
    ¬ ∃ (U : Submodule ℝ ((Fin 5 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ))),
      ∀ T : (Fin 5 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ),
        T ∈ U ↔ 2 < finrank ℝ (LinearMap.ker T) := by
  sorry

/-- 3B.5 -/
theorem exercise_3B_5 :
    ∃ T : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ), LinearMap.range T = LinearMap.ker T := by
  sorry

/-- 3B.6 -/
theorem exercise_3B_6 :
    ¬ ∃ T : (Fin 5 → ℝ) →ₗ[ℝ] (Fin 5 → ℝ), LinearMap.range T = LinearMap.ker T := by
  sorry

/-- 3B.7 -/
theorem exercise_3B_7 [Finite F V] [Finite F W]
    (hVW : 2 ≤ finrank F V) (hWV : finrank F V ≤ finrank F W) :
    ¬ ∃ (U : Submodule F (V →ₗ[F] W)),
      ∀ T : V →ₗ[F] W, T ∈ U ↔ ¬ Function.Injective T := by
  sorry

/-- 3B.8 -/
theorem exercise_3B_8 [Finite F V] [Finite F W]
    (hVW : finrank F V ≥ finrank F W) (hW : 2 ≤ finrank F W) :
    ¬ ∃ (U : Submodule F (V →ₗ[F] W)),
      ∀ T : V →ₗ[F] W, T ∈ U ↔ ¬ Function.Surjective T := by
  sorry

/-- 3B.9 -/
theorem exercise_3B_9 (T : V →ₗ[F] W) (hT : Function.Injective T)
    {n : ℕ} (v : Fin n → V) (hv : LinearIndependent F v) :
    LinearIndependent F (fun i => T (v i)) := by
  sorry

/-- 3B.10 -/
theorem exercise_3B_10 {n : ℕ} (v : Fin n → V) (hv : Spans F v)
    (T : V →ₗ[F] W) :
    Submodule.span F (Set.range (fun i => T (v i))) = LinearMap.range T := by
  sorry

/-- 3B.11 -/
theorem exercise_3B_11 [Finite F V] (T : V →ₗ[F] W) :
    ∃ U : Submodule F V, U ⊓ LinearMap.ker T = ⊥ ∧
      LinearMap.range T = Submodule.map T U := by
  sorry

/-- 3B.12 -/
theorem exercise_3B_12 (T : (Fin 4 → F) →ₗ[F] (Fin 2 → F))
    (h : ∀ x : Fin 4 → F,
      x ∈ LinearMap.ker T ↔ x 0 = 5 * x 1 ∧ x 2 = 7 * x 3) :
    Function.Surjective T := by
  sorry

/-- 3B.13 -/
theorem exercise_3B_13 (U : Submodule ℝ (Fin 8 → ℝ)) (hU : finrank ℝ U = 3)
    (T : (Fin 8 → ℝ) →ₗ[ℝ] (Fin 5 → ℝ)) (hker : LinearMap.ker T = U) :
    Function.Surjective T := by
  sorry

/-- 3B.14 -/
theorem exercise_3B_14 :
    ¬ ∃ T : (Fin 5 → F) →ₗ[F] (Fin 2 → F), ∀ x : Fin 5 → F,
      x ∈ LinearMap.ker T ↔ x 0 = 3 * x 1 ∧ x 2 = x 3 ∧ x 3 = x 4 := by
  sorry

/-- 3B.15 -/
theorem exercise_3B_15 (T : V →ₗ[F] V)
    (hker : Finite F (LinearMap.ker T)) (hrange : Finite F (LinearMap.range T)) :
    Finite F V := by
  sorry

/-- 3B.16 -/
theorem exercise_3B_16 [Finite F V] [Finite F W] :
    (∃ T : V →ₗ[F] W, Function.Injective T) ↔ finrank F V ≤ finrank F W := by
  sorry

/-- 3B.17 -/
theorem exercise_3B_17 [Finite F V] [Finite F W] :
    (∃ T : V →ₗ[F] W, Function.Surjective T) ↔ finrank F V ≥ finrank F W := by
  sorry

/-- 3B.18 -/
theorem exercise_3B_18 [Finite F V] [Finite F W] (U : Submodule F V) :
    (∃ T : V →ₗ[F] W, LinearMap.ker T = U) ↔
      finrank F V - finrank F W ≤ finrank F U := by
  sorry

/-- 3B.19 -/
theorem exercise_3B_19 [Finite F W] (T : V →ₗ[F] W) :
    Function.Injective T ↔
      ∃ S : W →ₗ[F] V, S ∘ₗ T = LinearMap.id := by
  sorry

/-- 3B.20 -/
theorem exercise_3B_20 [Finite F W] (T : V →ₗ[F] W) :
    Function.Surjective T ↔
      ∃ S : W →ₗ[F] V, T ∘ₗ S = LinearMap.id := by
  sorry

/-- 3B.21 -/
theorem exercise_3B_21 [Finite F V] (T : V →ₗ[F] W) (Usub : Submodule F W) :
    finrank F (Submodule.comap T Usub) =
      finrank F (LinearMap.ker T) +
        finrank F ((Usub ⊓ LinearMap.range T : Submodule F W)) := by
  sorry

/-- 3B.22 -/
theorem exercise_3B_22 [Finite F U] [Finite F V]
    (S : V →ₗ[F] W) (T : U →ₗ[F] V) :
    finrank F (LinearMap.ker (S ∘ₗ T)) ≤
      finrank F (LinearMap.ker S) + finrank F (LinearMap.ker T) := by
  sorry

/-- 3B.23 -/
theorem exercise_3B_23 [Finite F U] [Finite F V]
    (S : V →ₗ[F] W) (T : U →ₗ[F] V) :
    finrank F (LinearMap.range (S ∘ₗ T)) ≤ finrank F (LinearMap.range S) ∧
    finrank F (LinearMap.range (S ∘ₗ T)) ≤ finrank F (LinearMap.range T) := by
  sorry

/-- 3B.24 (a) -/
theorem exercise_3B_24a [Finite F V] (hV : finrank F V = 5)
    (S T : V →ₗ[F] V) (hST : S ∘ₗ T = 0) :
    finrank F (LinearMap.range (T ∘ₗ S)) ≤ 2 := by
  sorry

/-- 3B.24 (b) -/
theorem exercise_3B_24b :
    ∃ S T : (Fin 5 → F) →ₗ[F] (Fin 5 → F),
      S ∘ₗ T = 0 ∧ finrank F (LinearMap.range (T ∘ₗ S)) = 2 := by
  sorry

/-- 3B.25 -/
theorem exercise_3B_25 [Finite F W] (S T : V →ₗ[F] W) :
    LinearMap.ker S ≤ LinearMap.ker T ↔
      ∃ E : W →ₗ[F] W, T = E ∘ₗ S := by
  sorry

/-- 3B.26 -/
theorem exercise_3B_26 [Finite F V] (S T : V →ₗ[F] W) :
    LinearMap.range S ≤ LinearMap.range T ↔
      ∃ E : V →ₗ[F] V, S = T ∘ₗ E := by
  sorry

/-- 3B.27 -/
theorem exercise_3B_27 (P : V →ₗ[F] V) (hP : P ∘ₗ P = P) :
    IsCompl (LinearMap.ker P) (LinearMap.range P) := by
  sorry

/-- 3B.28 — Axler's "nonconstant" condition is rephrased as
{lit}`1 ≤ p.natDegree`, and {lit}`deg (D p) = deg p - 1` is rephrased on
natural-number degrees. -/
theorem exercise_3B_28 (D : Polynomial ℝ →ₗ[ℝ] Polynomial ℝ)
    (hD : ∀ p : Polynomial ℝ, 1 ≤ p.natDegree →
      (D p).natDegree = p.natDegree - 1) :
    Function.Surjective D := by
  sorry

/-- 3B.29 -/
theorem exercise_3B_29 (p : Polynomial ℝ) :
    ∃ q : Polynomial ℝ,
      (5 : ℝ) • q.derivative.derivative + (3 : ℝ) • q.derivative = p := by
  sorry

/-- 3B.30 -/
theorem exercise_3B_30 (phi : V →ₗ[F] F) (hphi : phi ≠ 0) (u : V)
    (hu : phi u ≠ 0) :
    IsCompl (LinearMap.ker phi)
      (Submodule.span F ({u} : Set V)) := by
  sorry

/-- 3B.31 -/
theorem exercise_3B_31 [Finite F V] (X : Submodule F V) (Y : Submodule F W)
    [Finite F Y] :
    (∃ T : V →ₗ[F] W,
      LinearMap.ker T = X ∧ LinearMap.range T = Y) ↔
    finrank F X + finrank F Y = finrank F V := by
  sorry

/-- 3B.32 -/
theorem exercise_3B_32 [Finite F V] (hV : 1 < finrank F V)
    (phi : (V →ₗ[F] V) →ₗ[F] F)
    (hphi : ∀ S T : V →ₗ[F] V, phi (S ∘ₗ T) = phi S * phi T) :
    phi = 0 := by
  sorry

open LADR.Section_1B (Complexification exercise_1B_8) in
/-- 3B.33 (complexification of a real linear map). Uses the complex scalar
multiplication on {lit}`Complexification V` defined in
{name}`LADR.Section_1B.exercise_1B_8`. -/
theorem exercise_3B_33 {V W : Type*} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] (T : V →ₗ[ℝ] W) :
    letI : Module ℂ (Complexification V) := exercise_1B_8 V
    letI : Module ℂ (Complexification W) := exercise_1B_8 W
    ∃ TC : Complexification V →ₗ[ℂ] Complexification W,
      (∀ u v : V, TC (u, v) = (T u, T v)) ∧
      (Function.Injective TC ↔ Function.Injective T) ∧
      (Function.Surjective TC ↔ Function.Surjective T) := by
  sorry

end LADR.Section_3B
