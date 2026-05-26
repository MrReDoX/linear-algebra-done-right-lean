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
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.Matrix.ToLin
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
import LinearAlgebraDoneRightLean.Section_3C
import CompanionHelper

/-!
# Axler, *Linear Algebra Done Right* (4e) — Section 3D: Invertibility and Isomorphisms
-/

namespace LADR.Section_3D

open LADR.Section_2A (Spans)
open LADR.Section_2B (IsBasis)
open LADR.Section_3C (matrixOf matrixOf_apply matrixOf_spec matrixOf_comp
  columnRank column row)
open Module (Finite finrank)

variable {F : Type*} [Field F]
  {U V W : Type*} [AddCommGroup U] [Module F U]
    [AddCommGroup V] [Module F V]
    [AddCommGroup W] [Module F W]

/-! 3.59 Definition: invertible, inverse

A linear map {lit}`T : V → W` is *invertible* if there exists
{lit}`S : W → V` linear with {lit}`S ∘ T = id_V` and {lit}`T ∘ S = id_W`.
-/

def IsInvertible (T : V →ₗ[F] W) : Prop :=
  ∃ S : W →ₗ[F] V,
    S ∘ₗ T = LinearMap.id ∧ T ∘ₗ S = LinearMap.id

/-! 3.60 Inverse is unique -/

theorem inv_unique (T : V →ₗ[F] W)
    {S₁ S₂ : W →ₗ[F] V}
    (h₁ : S₁ ∘ₗ T = LinearMap.id ∧ T ∘ₗ S₁ = LinearMap.id)
    (h₂ : S₂ ∘ₗ T = LinearMap.id ∧ T ∘ₗ S₂ = LinearMap.id) :
    S₁ = S₂ := by
  -- {lit}`S₁ = S₁ ∘ I = S₁ ∘ T ∘ S₂ = I ∘ S₂ = S₂`
  have : S₁ ∘ₗ (T ∘ₗ S₂) = S₁ ∘ₗ LinearMap.id := by rw [h₂.2]
  calc S₁ = S₁ ∘ₗ LinearMap.id := by ext; rfl
    _ = S₁ ∘ₗ (T ∘ₗ S₂) := by rw [h₂.2]
    _ = (S₁ ∘ₗ T) ∘ₗ S₂ := rfl
    _ = LinearMap.id ∘ₗ S₂ := by rw [h₁.1]
    _ = S₂ := by ext; rfl

/-! 3.61 Notation: {lit}`T⁻¹`. We use {name}`Classical.choose` to extract
the inverse from the existential. -/

noncomputable def IsInvertible.inv {T : V →ₗ[F] W} (h : IsInvertible T) :
    W →ₗ[F] V := Classical.choose h

theorem IsInvertible.inv_comp {T : V →ₗ[F] W} (h : IsInvertible T) :
    h.inv ∘ₗ T = LinearMap.id := (Classical.choose_spec h).1

theorem IsInvertible.comp_inv {T : V →ₗ[F] W} (h : IsInvertible T) :
    T ∘ₗ h.inv = LinearMap.id := (Classical.choose_spec h).2

/-! Bridge to mathlib's {name}`LinearEquiv`. -/

noncomputable def IsInvertible.toLinearEquiv {T : V →ₗ[F] W}
    (h : IsInvertible T) : V ≃ₗ[F] W :=
  { T with
    invFun := h.inv
    left_inv := fun v => LinearMap.congr_fun h.inv_comp v
    right_inv := fun w => LinearMap.congr_fun h.comp_inv w }

theorem LinearEquiv.isInvertible (E : V ≃ₗ[F] W) :
    IsInvertible (E : V →ₗ[F] W) :=
  ⟨E.symm, by ext v; simp, by ext w; simp⟩

/-! 3.62 Example: {lit}`T(x, y, z) = (-y, x, 4z)` on {lit}`ℝ³`. -/

set_option linter.unnecessarySeqFocus false in
noncomputable def T_3_62 : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) where
  toFun v := ![-v 1, v 0, 4 * v 2]
  map_add' x y := by
    funext i
    fin_cases i <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one] <;> ring
  map_smul' a x := by
    funext i
    fin_cases i <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one] <;> ring

set_option linter.unnecessarySeqFocus false in
noncomputable def T_3_62_inv : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) where
  toFun v := ![v 1, -v 0, v 2 / 4]
  map_add' x y := by
    funext i
    fin_cases i <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one] <;> ring
  map_smul' a x := by
    funext i
    fin_cases i <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one] <;> ring

set_option linter.unnecessarySeqFocus false in
set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in
example : IsInvertible T_3_62 := by
  refine ⟨T_3_62_inv, ?_, ?_⟩
  · ext v i
    fin_cases i <;> simp [T_3_62, T_3_62_inv,
      Matrix.cons_val_zero, Matrix.cons_val_one, LinearMap.coe_mk,
      AddHom.coe_mk] <;> ring
  · ext v i
    fin_cases i <;> simp [T_3_62, T_3_62_inv,
      Matrix.cons_val_zero, Matrix.cons_val_one, LinearMap.coe_mk,
      AddHom.coe_mk] <;> ring

/-! 3.63 Invertible iff injective and surjective -/

theorem isInvertible_of_bijective (T : V →ₗ[F] W) (hT : Function.Bijective T) :
    IsInvertible T := by
  let E : V ≃ₗ[F] W := LinearEquiv.ofBijective T hT
  refine ⟨E.symm, ?_, ?_⟩
  · ext v; exact E.symm_apply_apply v
  · ext w; exact E.apply_symm_apply w

theorem isInvertible_iff_bijective (T : V →ₗ[F] W) :
    IsInvertible T ↔ Function.Bijective T := by
  refine ⟨?_, isInvertible_of_bijective T⟩
  rintro ⟨S, hST, hTS⟩
  refine ⟨?_, ?_⟩
  · intro u v huv
    have h := congrArg S huv
    rw [show S (T u) = u from LinearMap.congr_fun hST u,
        show S (T v) = v from LinearMap.congr_fun hST v] at h
    exact h
  · intro w
    refine ⟨S w, ?_⟩
    exact LinearMap.congr_fun hTS w

/-! 3.64 Example: in infinite dimensions, neither injectivity nor surjectivity
implies invertibility.

- Multiplication by {lit}`X²` on {lit}`𝒫(ℝ)` is injective but not surjective
  (the constant polynomial {lit}`1` is not in its range).
- The backward shift on {lit}`F^∞` is surjective but not injective
  (the unit basis vector {lit}`(1, 0, 0, …)` is in its kernel). -/

example : Function.Injective LADR.Section_3A.multByXSq := by
  intro p q hpq
  have h : (Polynomial.X ^ 2 : Polynomial ℝ) * p = Polynomial.X ^ 2 * q := hpq
  have hX2 : (Polynomial.X ^ 2 : Polynomial ℝ) ≠ 0 := by
    intro h
    have := congrArg (Polynomial.coeff · 2) h
    simp [Polynomial.coeff_X_pow] at this
  exact mul_left_cancel₀ hX2 h

example : ¬ Function.Surjective LADR.Section_3A.multByXSq := by
  intro hsurj
  obtain ⟨p, hp⟩ := hsurj (1 : Polynomial ℝ)
  have h : (Polynomial.X ^ 2 : Polynomial ℝ) * p = 1 := hp
  -- {lit}`(X² · p).coeff 0 = 0 ≠ 1 = (1).coeff 0`.
  have hc : (Polynomial.X ^ 2 * p : Polynomial ℝ).coeff 0 =
      (1 : Polynomial ℝ).coeff 0 := by rw [h]
  rw [Polynomial.mul_coeff_zero, Polynomial.coeff_X_pow, Polynomial.coeff_one]
    at hc
  simp at hc

example : Function.Surjective (LADR.Section_3A.backwardShift (F := F)) := by
  intro x
  refine ⟨fun i => if i = 0 then 0 else x (i - 1), ?_⟩
  funext i
  show (if i + 1 = 0 then (0 : F) else x (i + 1 - 1)) = x i
  rw [if_neg (Nat.succ_ne_zero i)]
  simp

example : ¬ Function.Injective (LADR.Section_3A.backwardShift (F := F)) := by
  intro hinj
  let e : ℕ → F := Pi.single (0 : ℕ) (1 : F)
  have hshift : LADR.Section_3A.backwardShift (F := F) e = 0 := by
    funext i
    show e (i + 1) = 0
    show Pi.single (0 : ℕ) (1 : F) (i + 1) = 0
    rw [Pi.single_apply, if_neg (Nat.succ_ne_zero i)]
  have h0 : LADR.Section_3A.backwardShift (F := F) (0 : ℕ → F) = 0 := by
    funext _; rfl
  have heq : LADR.Section_3A.backwardShift (F := F) e =
             LADR.Section_3A.backwardShift (F := F) 0 := by
    rw [hshift, h0]
  have hPi : e = 0 := hinj heq
  have hPi0 : e 0 = (0 : ℕ → F) 0 := congrFun hPi 0
  show False
  have he0 : e 0 = (1 : F) := by
    show e 0 = (1 : F)
    simp [e]
  rw [he0] at hPi0
  exact one_ne_zero hPi0

/-! 3.65 Injectivity is equivalent to surjectivity (if {lit}`dim V = dim W < ∞`) -/

theorem injective_iff_surjective [Finite F V] [Finite F W]
    (h : finrank F V = finrank F W) (T : V →ₗ[F] W) :
    Function.Injective T ↔ Function.Surjective T := by
  rw [LADR.Section_3B.injective_iff_ker_eq_bot,
      LADR.Section_3B.surjective_iff_range_eq_top,
      LinearMap.ker_eq_bot_iff_range_eq_top_of_finrank_eq_finrank h]

theorem isInvertible_iff_injective [Finite F V] [Finite F W]
    (h : finrank F V = finrank F W) (T : V →ₗ[F] W) :
    IsInvertible T ↔ Function.Injective T := by
  rw [isInvertible_iff_bijective]
  constructor
  · exact fun hb => hb.1
  · intro hinj
    refine ⟨hinj, ?_⟩
    rw [← injective_iff_surjective h]
    exact hinj

theorem isInvertible_iff_surjective [Finite F V] [Finite F W]
    (h : finrank F V = finrank F W) (T : V →ₗ[F] W) :
    IsInvertible T ↔ Function.Surjective T := by
  rw [isInvertible_iff_injective h, injective_iff_surjective h]

/-! 3.67 Example: there exists a polynomial {lit}`p` with
{lit}`((x² + 5x + 7)·p)'' = q`. Skipped: encoded as exercise 3D.20 below in a
more general form. -/

/-! 3.68 {lit}`ST = I ⟺ TS = I` (on vector spaces of the same dimension) -/

theorem mul_eq_id_iff_mul_eq_id [Finite F V] [Finite F W]
    (h : finrank F V = finrank F W) (S : W →ₗ[F] V) (T : V →ₗ[F] W) :
    S ∘ₗ T = LinearMap.id ↔ T ∘ₗ S = LinearMap.id := by
  constructor
  · intro hST
    -- T is injective: if Tv = 0 then v = (ST)v = S(Tv) = S 0 = 0
    have hTinj : Function.Injective T := by
      intro u v huv
      have h₁ : S (T u) = u := LinearMap.congr_fun hST u
      have h₂ : S (T v) = v := LinearMap.congr_fun hST v
      have : S (T u) = S (T v) := congrArg S huv
      rw [h₁, h₂] at this
      exact this
    have hTinv : IsInvertible T :=
      (isInvertible_iff_injective h T).mpr hTinj
    have : S = hTinv.inv := by
      have hSeq : S ∘ₗ T = hTinv.inv ∘ₗ T := by rw [hST, hTinv.inv_comp]
      have : (S ∘ₗ T) ∘ₗ hTinv.inv = (hTinv.inv ∘ₗ T) ∘ₗ hTinv.inv := by
        rw [hSeq]
      simp only [show (S ∘ₗ T) ∘ₗ hTinv.inv = S ∘ₗ (T ∘ₗ hTinv.inv) from rfl,
        show (hTinv.inv ∘ₗ T) ∘ₗ hTinv.inv =
          hTinv.inv ∘ₗ (T ∘ₗ hTinv.inv) from rfl,
        hTinv.comp_inv] at this
      have h1 : S ∘ₗ (LinearMap.id : W →ₗ[F] W) = S := by ext; rfl
      have h2 : hTinv.inv ∘ₗ (LinearMap.id : W →ₗ[F] W) = hTinv.inv := by
        ext; rfl
      rw [h1, h2] at this; exact this
    rw [this, hTinv.comp_inv]
  · intro hTS
    have h' : finrank F W = finrank F V := h.symm
    -- by the forward direction with roles swapped
    have hT : T ∘ₗ S = LinearMap.id := hTS
    -- mirror argument
    have hSinj : Function.Injective S := by
      intro u v huv
      have h₁ : T (S u) = u := LinearMap.congr_fun hTS u
      have h₂ : T (S v) = v := LinearMap.congr_fun hTS v
      have : T (S u) = T (S v) := congrArg T huv
      rw [h₁, h₂] at this
      exact this
    have hSinv : IsInvertible S :=
      (isInvertible_iff_injective h' S).mpr hSinj
    have : T = hSinv.inv := by
      have hTeq : T ∘ₗ S = hSinv.inv ∘ₗ S := by rw [hTS, hSinv.inv_comp]
      have : (T ∘ₗ S) ∘ₗ hSinv.inv = (hSinv.inv ∘ₗ S) ∘ₗ hSinv.inv := by
        rw [hTeq]
      simp only [show (T ∘ₗ S) ∘ₗ hSinv.inv = T ∘ₗ (S ∘ₗ hSinv.inv) from rfl,
        show (hSinv.inv ∘ₗ S) ∘ₗ hSinv.inv =
          hSinv.inv ∘ₗ (S ∘ₗ hSinv.inv) from rfl,
        hSinv.comp_inv] at this
      have h1 : T ∘ₗ (LinearMap.id : V →ₗ[F] V) = T := by ext; rfl
      have h2 : hSinv.inv ∘ₗ (LinearMap.id : V →ₗ[F] V) = hSinv.inv := by
        ext; rfl
      rw [h1, h2] at this; exact this
    rw [this, hSinv.comp_inv]

/-! 3.69 Definition: isomorphism, isomorphic

An *isomorphism* is an invertible linear map; in mathlib, this is exactly
{name}`LinearEquiv` (denoted {lit}`V ≃ₗ[F] W`). Two vector spaces are
*isomorphic* if there is an isomorphism between them. -/

example : Prop := Nonempty (V ≃ₗ[F] W)

/-! 3.70 Dimension shows whether vector spaces are isomorphic -/

@[avoiding FiniteDimensional.nonempty_linearEquiv_iff_finrank_eq]
theorem isomorphic_iff_finrank_eq [Finite F V] [Finite F W] :
    Nonempty (V ≃ₗ[F] W) ↔ finrank F V = finrank F W := by
  constructor
  · rintro ⟨E⟩
    exact E.finrank_eq
  · intro h
    obtain ⟨n, v, hv⟩ := LADR.Section_2B.exists_basis (F := F) (V := V)
    obtain ⟨m, w, hw⟩ := LADR.Section_2B.exists_basis (F := F) (V := W)
    have hn : n = finrank F V :=
      LADR.Section_2C.isBasis_card_eq_finrank v hv
    have hm : m = finrank F W :=
      LADR.Section_2C.isBasis_card_eq_finrank w hw
    have hnm : n = m := by omega
    subst hnm
    obtain ⟨T, hT, _⟩ := LADR.Section_3A.linearMap_lemma v hv w
    have hTbij : Function.Bijective T := by
      refine ⟨?_, ?_⟩
      · rw [LADR.Section_3B.injective_iff_ker_eq_bot, Submodule.eq_bot_iff]
        intro x hx
        rw [LinearMap.mem_ker] at hx
        have hx_in : x ∈ Submodule.span F (Set.range v) := by
          rw [(hv.2 : _ = ⊤)]; exact Submodule.mem_top
        rw [Submodule.mem_span_range_iff_exists_fun] at hx_in
        obtain ⟨a, ha⟩ := hx_in
        rw [← ha] at hx
        rw [map_sum] at hx
        have hTa : ∑ k, a k • w k = 0 := by
          rw [← hx]
          refine Finset.sum_congr rfl (fun k _ => ?_)
          rw [LinearMap.map_smul, hT]
        have ha_zero : a = 0 := by
          funext i
          exact Fintype.linearIndependent_iff.mp hw.1 a hTa i
        rw [← ha, ha_zero]
        simp
      · intro y
        have hy_in : y ∈ Submodule.span F (Set.range w) := by
          rw [(hw.2 : _ = ⊤)]; exact Submodule.mem_top
        rw [Submodule.mem_span_range_iff_exists_fun] at hy_in
        obtain ⟨a, ha⟩ := hy_in
        refine ⟨∑ k, a k • v k, ?_⟩
        rw [map_sum, ← ha]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [LinearMap.map_smul, hT]
    exact ⟨LinearEquiv.ofBijective T hTbij⟩

/-! 3.71 {lit}`ℒ(V, W)` and {lit}`F^{m,n}` are isomorphic.

mathlib provides this directly as {name}`LinearMap.toMatrix`, which is the
{name}`LinearEquiv` underlying our {name}`matrixOf`. -/

noncomputable def matrixOfEquiv {m n : ℕ}
    {v : Fin n → V} {w : Fin m → W}
    (hv : IsBasis F v) (hw : IsBasis F w) :
    (V →ₗ[F] W) ≃ₗ[F] Matrix (Fin m) (Fin n) F :=
  LinearMap.toMatrix hv.toModuleBasis hw.toModuleBasis

/-! 3.72 {lit}`dim ℒ(V, W) = (dim V)(dim W)` -/

@[avoiding Module.finrank_linearMap]
theorem finrank_linearMap [Finite F V] [Finite F W] :
    finrank F (V →ₗ[F] W) = finrank F V * finrank F W := by
  obtain ⟨n, v, hv⟩ := LADR.Section_2B.exists_basis (F := F) (V := V)
  obtain ⟨m, w, hw⟩ := LADR.Section_2B.exists_basis (F := F) (V := W)
  have hn : n = finrank F V :=
    LADR.Section_2C.isBasis_card_eq_finrank v hv
  have hm : m = finrank F W :=
    LADR.Section_2C.isBasis_card_eq_finrank w hw
  have h := (matrixOfEquiv hv hw).finrank_eq
  rw [LADR.Section_3C.finrank_matrix] at h
  rw [h, hn, hm, mul_comm]

/-! 3.73 Definition: matrix of a vector {lit}`ℳ(v)` -/

/-- The column vector of coordinates of {lit}`x ∈ V` in basis {lit}`v`. -/
noncomputable def vectorMatrixOf {n : ℕ}
    {v : Fin n → V} (hv : IsBasis F v) (x : V) :
    Matrix (Fin n) (Fin 1) F :=
  fun i _ => hv.toModuleBasis.repr x i

/-! 3.74 Example: matrix of a vector — for {lit}`x ∈ Fⁿ` with the standard
basis, {lit}`ℳ(x)` is the column vector of components.

The proof is more awkward than Axler's because our basis is built through
{name}`LADR.Section_2B.IsBasis.toModuleBasis` rather than mathlib's
{name}`Pi.basisFun`, so we have to compute {lit}`b.repr x` from scratch by
expressing {lit}`x` in the basis and applying {lit}`b.repr` to both sides. -/

example {n : ℕ} (x : Fin n → F) :
    vectorMatrixOf (F := F) (V := Fin n → F)
      (LADR.Section_2B.isBasis_stdBasis n) x = fun i _ => x i := by
  classical
  ext i _
  show (LADR.Section_2B.isBasis_stdBasis (F := F) n).toModuleBasis.repr x i =
    x i
  set hu : IsBasis F (fun k : Fin n => (Pi.single k 1 : Fin n → F)) :=
    LADR.Section_2B.isBasis_stdBasis n with hu_def
  set b := hu.toModuleBasis with b_def
  have hb_apply : ∀ k, b k = Pi.single k (1 : F) :=
    IsBasis.toModuleBasis_apply hu
  -- Express x in the standard basis: x = ∑ k, x k • Pi.single k 1.
  have hxsum_b : x = ∑ k, x k • b k := by
    funext j
    simp_rw [hb_apply]
    rw [Finset.sum_apply]
    simp_rw [Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single j]
    · rw [Pi.single_eq_same, mul_one]
    · intros k _ hkj; rw [Pi.single_eq_of_ne (Ne.symm hkj), mul_zero]
    · intro h; exact absurd (Finset.mem_univ j) h
  -- Apply b.repr to both sides, using b.repr_self.
  have hreprx : b.repr x = ∑ k, x k • Finsupp.single k (1 : F) := by
    conv_lhs => rw [hxsum_b]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [show b.repr (x k • b k) = x k • b.repr (b k) from
      b.repr.map_smul _ _, b.repr_self]
  rw [hreprx]
  -- Evaluate the Finsupp sum at index i.
  rw [Finsupp.coe_finset_sum, Finset.sum_apply]
  rw [Finset.sum_eq_single i]
  · rw [Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul,
        Finsupp.single_apply, if_pos rfl, mul_one]
  · intros k _ hki
    rw [Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul,
        Finsupp.single_apply, if_neg hki, mul_zero]
  · intro h; exact absurd (Finset.mem_univ i) h

/-! 3.75 Column {lit}`k` of {lit}`ℳ(T)` equals {lit}`ℳ(T v_k)` -/

theorem matrixOf_column_eq_vectorMatrixOf {m n : ℕ}
    {v : Fin n → V} {w : Fin m → W}
    (hv : IsBasis F v) (hw : IsBasis F w)
    (T : V →ₗ[F] W) (k : Fin n) :
    (fun j => matrixOf hv hw T j k) =
      fun j => vectorMatrixOf hw (T (v k)) j 0 := by
  funext j
  rw [matrixOf_apply, vectorMatrixOf]

/-! 3.76 Linear maps act like matrix multiplication -/

theorem matrixOf_apply_vectorMatrixOf {m n : ℕ}
    {v : Fin n → V} {w : Fin m → W}
    (hv : IsBasis F v) (hw : IsBasis F w)
    (T : V →ₗ[F] W) (x : V) :
    vectorMatrixOf hw (T x) =
      matrixOf hv hw T * vectorMatrixOf hv x := by
  ext j k
  show hw.toModuleBasis.repr (T x) j =
    ∑ r, matrixOf hv hw T j r * hv.toModuleBasis.repr x r
  -- Expand {lit}`x = ∑ r b_V.repr(x) r • v_r`, push T through.
  have hx : x = ∑ r, hv.toModuleBasis.repr x r • v r := by
    have hb := hv.toModuleBasis.sum_repr x
    conv_lhs => rw [← hb]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [IsBasis.toModuleBasis_apply]
  have hTx : T x = ∑ r, hv.toModuleBasis.repr x r • T (v r) := by
    conv_lhs => rw [hx]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [LinearMap.map_smul]
  rw [hTx, map_sum, Finsupp.coe_finset_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  -- LHS at index j: {lit}`b_W.repr (a_r • T v_r) j = a_r * b_W.repr (T v_r) j`.
  rw [show hw.toModuleBasis.repr ((hv.toModuleBasis.repr x r) • T (v r)) =
      (hv.toModuleBasis.repr x r) • hw.toModuleBasis.repr (T (v r)) from
      hw.toModuleBasis.repr.map_smul _ _]
  rw [Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, matrixOf_apply, mul_comm]

/-! 3.78 Dimension of {lit}`range T` equals column rank of {lit}`ℳ(T)` -/

theorem finrank_range_eq_columnRank_matrixOf [Finite F V] [Finite F W] {m n : ℕ}
    {v : Fin n → V} {w : Fin m → W}
    (hv : IsBasis F v) (hw : IsBasis F w)
    (T : V →ₗ[F] W) :
    finrank F (LinearMap.range T) = columnRank (matrixOf hv hw T) := by
  classical
  -- The iso {lit}`ψ : W ≃ₗ Fin m → F` via basis {lit}`w`, composed with the
  -- trivial iso to {lit}`Matrix (Fin m) (Fin 1) F`.
  let ψ : W ≃ₗ[F] (Fin m → F) := hw.toModuleBasis.equivFun
  let φ : (Fin m → F) ≃ₗ[F] Matrix (Fin m) (Fin 1) F :=
    { toFun := fun v j _ => v j
      invFun := fun M j => M j 0
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => by
        ext j i; obtain rfl : i = 0 := Subsingleton.elim _ _; rfl }
  let η : W ≃ₗ[F] Matrix (Fin m) (Fin 1) F := ψ.trans φ
  -- {lit}`range T = span (range (T ∘ v))` (3B.10).
  have hrange : LinearMap.range T =
      Submodule.span F (Set.range (fun k => T (v k))) := by
    have hv2 : Submodule.span F (Set.range v) = ⊤ := hv.2
    conv_lhs => rw [LinearMap.range_eq_map, ← hv2]
    rw [Submodule.map_span]
    congr 1
    exact (Set.range_comp T v).symm
  rw [hrange]
  -- Apply {lit}`η`: finrank is preserved.
  have hη_eq :
      finrank F ↥(Submodule.span F (Set.range (fun k => T (v k)))) =
      finrank F ↥(Submodule.map η.toLinearMap
        (Submodule.span F (Set.range (fun k => T (v k))))) :=
    (Submodule.equivMapOfInjective η.toLinearMap η.injective _).finrank_eq
  rw [hη_eq, Submodule.map_span]
  -- Identify the resulting set of images with the set of columns of ℳ(T).
  have hsetrange :
      η.toLinearMap '' Set.range (fun k => T (v k)) =
        Set.range (column (matrixOf hv hw T)) := by
    ext y
    constructor
    · rintro ⟨_, ⟨k, rfl⟩, rfl⟩
      refine ⟨k, ?_⟩
      ext j i
      obtain rfl : i = 0 := Subsingleton.elim _ _
      change column (matrixOf hv hw T) k j 0 = ψ (T (v k)) j
      change matrixOf hv hw T j k = ψ (T (v k)) j
      rw [matrixOf_apply]; rfl
    · rintro ⟨k, rfl⟩
      refine ⟨T (v k), ⟨k, rfl⟩, ?_⟩
      ext j i
      obtain rfl : i = 0 := Subsingleton.elim _ _
      change ψ (T (v k)) j = column (matrixOf hv hw T) k j 0
      change ψ (T (v k)) j = matrixOf hv hw T j k
      rw [matrixOf_apply]; rfl
  rw [hsetrange]
  rfl

/-! 3.79 Definition: identity matrix.
mathlib provides this as {lit}`1 : Matrix (Fin n) (Fin n) F`. -/

example (n : ℕ) : Matrix (Fin n) (Fin n) F := 1

example (n : ℕ) (j k : Fin n) :
    (1 : Matrix (Fin n) (Fin n) F) j k = if j = k then 1 else 0 :=
  Matrix.one_apply

/-! 3.80 Definition: invertible matrix.
A square matrix {lit}`A` is invertible if there exists {lit}`B` with
{lit}`A * B = 1 ∧ B * A = 1`. In mathlib, this is {name}`IsUnit`. -/

example (n : ℕ) (A : Matrix (Fin n) (Fin n) F) : Prop := IsUnit A

/-! 3.81 Matrix of product of linear maps (re-statement of 3.43). -/

example {p m n : ℕ}
    {u : Fin p → U} {v : Fin n → V} {w : Fin m → W}
    (hu : IsBasis F u) (hv : IsBasis F v) (hw : IsBasis F w)
    (S : V →ₗ[F] W) (T : U →ₗ[F] V) :
    matrixOf hu hw (S ∘ₗ T) = matrixOf hv hw S * matrixOf hu hv T :=
  matrixOf_comp hu hv hw S T

/-! 3.82 The matrices {lit}`ℳ(I, u, v)` and {lit}`ℳ(I, v, u)` are mutual
inverses. -/

/-- Helper: the matrix of {lit}`LinearMap.id` with respect to a single
basis is the identity matrix. -/
theorem matrixOf_id_self {n : ℕ} {v : Fin n → V} (hv : IsBasis F v) :
    matrixOf hv hv LinearMap.id = 1 := by
  ext j k
  rw [matrixOf_apply]
  show hv.toModuleBasis.repr ((LinearMap.id : V →ₗ[F] V) (v k)) j =
    (1 : Matrix (Fin n) (Fin n) F) j k
  rw [show ((LinearMap.id : V →ₗ[F] V) (v k)) = v k from rfl]
  rw [show (v k : V) = hv.toModuleBasis k from
      (IsBasis.toModuleBasis_apply hv k).symm]
  rw [Module.Basis.repr_self, Finsupp.single_apply, Matrix.one_apply]
  by_cases hjk : j = k
  · subst hjk; simp
  · rw [if_neg hjk, if_neg (fun heq => hjk heq.symm)]

theorem matrixOf_id_mul_matrixOf_id {n : ℕ}
    {u v : Fin n → V} (hu : IsBasis F u) (hv : IsBasis F v) :
    matrixOf hv hu LinearMap.id * matrixOf hu hv LinearMap.id = 1 := by
  -- By 3.43 applied to {lit}`I ∘ I` going {lit}`u → v → u`.
  have h := matrixOf_comp hu hv hu LinearMap.id LinearMap.id
  have hid_comp : (LinearMap.id : V →ₗ[F] V) ∘ₗ LinearMap.id = LinearMap.id := by
    ext; rfl
  rw [hid_comp, matrixOf_id_self hu] at h
  exact h.symm

/-! 3.84 Change-of-basis formula -/

theorem change_of_basis {n : ℕ}
    {u v : Fin n → V} (hu : IsBasis F u) (hv : IsBasis F v) (T : V →ₗ[F] V) :
    matrixOf hu hu T =
      matrixOf hv hu LinearMap.id *
        matrixOf hv hv T * matrixOf hu hv LinearMap.id := by
  -- Two applications of 3.43: ℳ(T) = ℳ(I ∘ T) and ℳ(T) = ℳ(T ∘ I).
  have h1 : matrixOf hu hv T =
      matrixOf hv hv T * matrixOf hu hv LinearMap.id := by
    have h := matrixOf_comp hu hv hv T LinearMap.id
    have hcomp : T ∘ₗ LinearMap.id = T := by ext; rfl
    rw [hcomp] at h
    exact h
  have h2 : matrixOf hu hu T =
      matrixOf hv hu LinearMap.id * matrixOf hu hv T := by
    have h := matrixOf_comp hu hv hu LinearMap.id T
    have hcomp : (LinearMap.id : V →ₗ[F] V) ∘ₗ T = T := by ext; rfl
    rw [hcomp] at h
    exact h
  rw [h2, h1, mul_assoc]

/-! 3.86 {lit}`ℳ(T⁻¹) = ℳ(T)⁻¹` -/

theorem matrixOf_inv_mul_matrixOf {n : ℕ}
    {v : Fin n → V} (hv : IsBasis F v) (T : V →ₗ[F] V)
    (hT : IsInvertible T) :
    matrixOf hv hv hT.inv * matrixOf hv hv T = 1 := by
  rw [← matrixOf_comp hv hv hv hT.inv T, hT.inv_comp, matrixOf_id_self]

theorem matrixOf_mul_matrixOf_inv {n : ℕ}
    {v : Fin n → V} (hv : IsBasis F v) (T : V →ₗ[F] V)
    (hT : IsInvertible T) :
    matrixOf hv hv T * matrixOf hv hv hT.inv = 1 := by
  rw [← matrixOf_comp hv hv hv T hT.inv, hT.comp_inv, matrixOf_id_self]

/-! # Exercises -/

/-- 3D.1 {lit}`(T⁻¹)⁻¹ = T` -/
theorem exercise_3D_1 (T : V →ₗ[F] W) (hT : IsInvertible T) :
    ∃ hT' : IsInvertible hT.inv, hT'.inv = T := by
  sorry

/-- 3D.2 {lit}`(ST)⁻¹ = T⁻¹ S⁻¹` -/
theorem exercise_3D_2 (T : U →ₗ[F] V) (S : V →ₗ[F] W)
    (hT : IsInvertible T) (hS : IsInvertible S) :
    IsInvertible (S ∘ₗ T) := by
  sorry

/-- 3D.3 -/
theorem exercise_3D_3 [Finite F V] (T : V →ₗ[F] V) :
    (IsInvertible T ↔ ∀ {n : ℕ} (v : Fin n → V), IsBasis F v →
      IsBasis F (fun k => T (v k))) ∧
    (IsInvertible T ↔ ∃ (n : ℕ) (v : Fin n → V),
      IsBasis F v ∧ IsBasis F (fun k => T (v k))) := by
  sorry

/-- 3D.4 -/
theorem exercise_3D_4 [Finite F V] (hV : 1 < finrank F V) :
    ¬ ∃ (U : Submodule F (V →ₗ[F] V)),
      ∀ T : V →ₗ[F] V, T ∈ U ↔ ¬ IsInvertible T := by
  sorry

/-- 3D.5 -/
theorem exercise_3D_5 [Finite F V] (U_sub : Submodule F V) (S : U_sub →ₗ[F] V) :
    (∃ T : V →ₗ[F] V, IsInvertible T ∧ ∀ u : U_sub, T (u : V) = S u) ↔
      Function.Injective S := by
  sorry

/-- 3D.6 -/
theorem exercise_3D_6 [Finite F W] (S T : V →ₗ[F] W) :
    LinearMap.ker S = LinearMap.ker T ↔
      ∃ E : W →ₗ[F] W, IsInvertible E ∧ S = E ∘ₗ T := by
  sorry

/-- 3D.7 -/
theorem exercise_3D_7 [Finite F V] (S T : V →ₗ[F] W) :
    LinearMap.range S = LinearMap.range T ↔
      ∃ E : V →ₗ[F] V, IsInvertible E ∧ S = T ∘ₗ E := by
  sorry

/-- 3D.8 -/
theorem exercise_3D_8 [Finite F V] [Finite F W] (S T : V →ₗ[F] W) :
    (∃ (E₁ : V →ₗ[F] V) (E₂ : W →ₗ[F] W), IsInvertible E₁ ∧ IsInvertible E₂ ∧
      S = E₂ ∘ₗ T ∘ₗ E₁) ↔
      finrank F (LinearMap.ker S) = finrank F (LinearMap.ker T) := by
  sorry

/-- 3D.9 -/
theorem exercise_3D_9 [Finite F V] (T : V →ₗ[F] W) (hT : Function.Surjective T) :
    ∃ U_sub : Submodule F V,
      ∃ E : U_sub ≃ₗ[F] W, ∀ u : U_sub, E u = T (u : V) := by
  sorry

/-- 3D.10 -/
def exercise_3D_10_E (U_sub : Submodule F V) : Submodule F (V →ₗ[F] W) where
  carrier := {T | (U_sub : Set V) ⊆ LinearMap.ker T}
  zero_mem' := by intro x _; rfl
  add_mem' := by
    intro S T hS hT x hx
    show (S + T) x = 0
    rw [LinearMap.add_apply]
    have hSx : S x = 0 := hS hx
    have hTx : T x = 0 := hT hx
    rw [hSx, hTx, add_zero]
  smul_mem' := by
    intro a T hT x hx
    show (a • T) x = 0
    rw [LinearMap.smul_apply, hT hx, smul_zero]

/-- 3D.10 part (b): formula for the dimension. Part (a) — that
{name}`exercise_3D_10_E` is a subspace — is the {name}`Submodule` structure
in its definition. -/
theorem exercise_3D_10 [Finite F V] [Finite F W] (U_sub : Submodule F V) :
    finrank F (exercise_3D_10_E U_sub (W := W)) =
      (finrank F V - finrank F U_sub) * finrank F W := by
  sorry

/-- 3D.11 -/
theorem exercise_3D_11 [Finite F V] (S T : V →ₗ[F] V) :
    IsInvertible (S ∘ₗ T) ↔ IsInvertible S ∧ IsInvertible T := by
  sorry

/-- 3D.12 -/
theorem exercise_3D_12 [Finite F V] (S T U_op : V →ₗ[F] V)
    (h : S ∘ₗ T ∘ₗ U_op = LinearMap.id) :
    ∃ hT : IsInvertible T, hT.inv = U_op ∘ₗ S := by
  sorry

/-- 3D.13 -/
theorem exercise_3D_13 :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℝ V)
      (S T U_op : V →ₗ[ℝ] V),
      S ∘ₗ T ∘ₗ U_op = LinearMap.id ∧ ¬ IsInvertible T := by
  sorry

/-- 3D.14 — prove or counterexample: {lit}`RST` surjective ⟹ {lit}`S`
injective (on f.d.). -/
def exercise_3D_14 :
    Decidable (∀ [Finite F V] (R S T : V →ₗ[F] V),
      Function.Surjective (R ∘ₗ S ∘ₗ T) → Function.Injective S) := by
  sorry

/-- 3D.15 -/
theorem exercise_3D_15 [Finite F V] (T : V →ₗ[F] V) {m : ℕ} (v : Fin m → V)
    (hTv : Spans F (fun k => T (v k))) : Spans F v := by
  sorry

/-- 3D.16 — Every linear map {lit}`F^{n,1} → F^{m,1}` is matrix multiplication. -/
theorem exercise_3D_16 {m n : ℕ}
    (T : Matrix (Fin n) (Fin 1) F →ₗ[F] Matrix (Fin m) (Fin 1) F) :
    ∃ A : Matrix (Fin m) (Fin n) F, ∀ x, T x = A * x := by
  sorry

/-- 3D.17 -/
def exercise_3D_17_𝒜 (S : V →ₗ[F] V) : (V →ₗ[F] V) →ₗ[F] (V →ₗ[F] V) where
  toFun T := S ∘ₗ T
  map_add' T₁ T₂ := by ext v; simp
  map_smul' a T := by ext v; simp

/-- 3D.17 (a) -/
theorem exercise_3D_17a [Finite F V] (S : V →ₗ[F] V) :
    finrank F (LinearMap.ker (exercise_3D_17_𝒜 S)) =
      finrank F V * finrank F (LinearMap.ker S) := by
  sorry

/-- 3D.17 (b) -/
theorem exercise_3D_17b [Finite F V] (S : V →ₗ[F] V) :
    finrank F (LinearMap.range (exercise_3D_17_𝒜 S)) =
      finrank F V * finrank F (LinearMap.range S) := by
  sorry

/-- 3D.18 -/
theorem exercise_3D_18 : Nonempty (V ≃ₗ[F] (F →ₗ[F] V)) := by
  sorry

/-- 3D.19 -/
theorem exercise_3D_19 [Finite F V] (T : V →ₗ[F] V) :
    (∀ {n : ℕ} (u v : Fin n → V) (hu : IsBasis F u) (hv : IsBasis F v),
      matrixOf hu hu T = matrixOf hv hv T) ↔
      ∃ lam : F, T = lam • LinearMap.id := by
  sorry

/-- 3D.20 -/
theorem exercise_3D_20 (q : Polynomial ℝ) :
    ∃ p : Polynomial ℝ, ∀ x : ℝ,
      q.eval x = (x ^ 2 + x) * (p.derivative.derivative.eval x) +
        2 * x * (p.derivative.eval x) + p.eval 3 := by
  sorry

/-- 3D.21 -/
theorem exercise_3D_21 {n : ℕ} (A : Fin n → Fin n → F) :
    (∀ x : Fin n → F, (∀ j, ∑ k, A j k * x k = 0) → x = 0) ↔
      (∀ c : Fin n → F, ∃ x : Fin n → F, ∀ j, ∑ k, A j k * x k = c j) := by
  sorry

/-- 3D.22 -/
theorem exercise_3D_22 [Finite F V] {n : ℕ}
    {v : Fin n → V} (hv : IsBasis F v) (T : V →ₗ[F] V) :
    IsUnit (matrixOf hv hv T) ↔ IsInvertible T := by
  sorry

/-- 3D.23 -/
theorem exercise_3D_23 {n : ℕ}
    {u v : Fin n → V} (hu : IsBasis F u) (hv : IsBasis F v)
    (T : V →ₗ[F] V) (hT : ∀ k, T (v k) = u k) :
    matrixOf hv hv T = matrixOf hu hv LinearMap.id := by
  sorry

/-- 3D.24 — {lit}`A * B = 1 ⟹ B * A = 1` -/
theorem exercise_3D_24 {n : ℕ} (A B : Matrix (Fin n) (Fin n) F)
    (hAB : A * B = 1) : B * A = 1 := by
  sorry

end LADR.Section_3D
