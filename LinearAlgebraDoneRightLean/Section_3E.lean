import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.Prod
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Algebra.Module.Submodule.Map
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Ring
import LinearAlgebraDoneRightLean.Section_1C
import LinearAlgebraDoneRightLean.Section_2A
import LinearAlgebraDoneRightLean.Section_2B
import LinearAlgebraDoneRightLean.Section_2C
import LinearAlgebraDoneRightLean.Section_3A
import LinearAlgebraDoneRightLean.Section_3B
import CompanionHelper

/-!
# Axler, *Linear Algebra Done Right* (4e) — Section 3E: Products and Quotients of Vector Spaces
-/

namespace LADR.Section_3E

open LADR.Section_2A (Spans)
open LADR.Section_2B (IsBasis)
open LADR.Section_1C (IsDirectSum)
open Module (Finite finrank)

variable {F : Type*} [Field F]

/-! 3.87 Definition: product of vector spaces

For a family of vector spaces {lit}`V₁, …, Vₘ` over {lit}`F`, the product
{lit}`V₁ × ⋯ × Vₘ` is the set of all {lit}`m`-tuples. In Lean we encode this
as the dependent function type {lit}`(i : Fin m) → V i`, with pointwise
addition and scalar multiplication. -/

example {m : ℕ} (V : Fin m → Type*) [∀ i, AddCommGroup (V i)]
    [∀ i, Module F (V i)] : Type _ := (i : Fin m) → V i

example {m : ℕ} (V : Fin m → Type*) [∀ i, AddCommGroup (V i)]
    [∀ i, Module F (V i)] (u v : (i : Fin m) → V i) (i : Fin m) :
    (u + v) i = u i + v i := rfl

example {m : ℕ} (V : Fin m → Type*) [∀ i, AddCommGroup (V i)]
    [∀ i, Module F (V i)] (lam : F) (v : (i : Fin m) → V i) (i : Fin m) :
    (lam • v) i = lam • v i := rfl

/-! 3.88 Example: product of {lit}`𝒫₅(ℝ)` and {lit}`ℝ³`. -/

example : Type _ := Polynomial.degreeLT ℝ 6 × (Fin 3 → ℝ)

/-! 3.89 The product of vector spaces is a vector space (automatic in
mathlib). -/

example {m : ℕ} (V : Fin m → Type*) [∀ i, AddCommGroup (V i)]
    [∀ i, Module F (V i)] : Module F ((i : Fin m) → V i) := inferInstance

/-! 3.90 {lit}`ℝ² × ℝ³ ≠ ℝ⁵` but {lit}`ℝ² × ℝ³ ≃ ℝ⁵` -/

/-- The isomorphism {lit}`ℝ² × ℝ³ ≃ₗ[ℝ] ℝ⁵`, given by concatenating the
two lists via {name}`Fin.append`. -/
def prod_two_three_equiv :
    ((Fin 2 → ℝ) × (Fin 3 → ℝ)) ≃ₗ[ℝ] (Fin 5 → ℝ) where
  toFun x := Fin.append x.1 x.2
  invFun y := (fun i => y (Fin.castAdd 3 i), fun j => y (Fin.natAdd 2 j))
  map_add' x y := by
    funext i
    refine Fin.addCases (fun p => ?_) (fun q => ?_) i
    · simp [Fin.append_left]
    · simp [Fin.append_right]
  map_smul' a x := by
    funext i
    refine Fin.addCases (fun p => ?_) (fun q => ?_) i
    · simp [Fin.append_left]
    · simp [Fin.append_right]
  left_inv x := by
    ext1
    · funext i; exact Fin.append_left x.1 x.2 i
    · funext j; exact Fin.append_right x.1 x.2 j
  right_inv y := by
    funext i
    refine Fin.addCases (fun p => ?_) (fun q => ?_) i
    · exact Fin.append_left _ _ p
    · exact Fin.append_right _ _ q

/-! 3.91 Example: a basis of {lit}`𝒫₂(ℝ) × ℝ²` of length 5. Skipped — the
concrete computation. -/

/-! 3.92 The dimension of a product is the sum of dimensions. -/

theorem finrank_prod {m : ℕ} (V : Fin m → Type*)
    [∀ i, AddCommGroup (V i)] [∀ i, Module F (V i)]
    [∀ i, Module.Finite F (V i)] [∀ i, Module.Free F (V i)] :
    finrank F ((i : Fin m) → V i) = ∑ i, finrank F (V i) :=
  Module.finrank_pi_fintype F

variable {V : Type*} [AddCommGroup V] [Module F V]

/-! 3.93 The map {lit}`Γ : V₁ × ⋯ × Vₘ → V₁ + ⋯ + Vₘ` sending
{lit}`(v₁, …, vₘ) ↦ v₁ + ⋯ + vₘ`. The sum is a direct sum iff {lit}`Γ` is
injective. -/

/-- The {lit}`Γ` map from Axler 3.93. -/
def gamma {m : ℕ} (V_sub : Fin m → Submodule F V) :
    ((i : Fin m) → ↥(V_sub i)) →ₗ[F] V where
  toFun u := ∑ i, ((u i : V))
  map_add' u v := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp [Pi.add_apply]
  map_smul' a u := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    show ((a • u i : V_sub i) : V) = a • (u i : V)
    rw [Submodule.coe_smul_of_tower]

@[avoiding Submodule.directSum_iff_internalDirectSum]
theorem directSum_iff_gamma_injective {m : ℕ}
    (V_sub : Fin m → Submodule F V) :
    IsDirectSum V_sub ↔ Function.Injective (gamma V_sub) := by
  constructor
  · intro hds u v huv
    -- huv : ∑ i, u i = ∑ i, v i
    have h : (∑ i, ((u i : V))) = (∑ i, ((v i : V))) := huv
    exact hds u v h
  · intro hinj u v huv
    apply hinj
    show ∑ i, ((u i : V)) = ∑ i, ((v i : V))
    exact huv

/-! 3.94 A sum is a direct sum iff dimensions add up. -/

/-- The range of {lit}`gamma V_sub` equals the sum of subspaces
{lit}`∑ V_sub i`. -/
private theorem gamma_range_eq {m : ℕ} (V_sub : Fin m → Submodule F V) :
    LinearMap.range (gamma V_sub) = ∑ i, V_sub i := by
  classical
  apply le_antisymm
  · -- {lit}`range γ ⊆ ∑ V_sub i`.
    rintro _ ⟨u, rfl⟩
    show (∑ i, ((u i : V))) ∈ (∑ i : Fin m, V_sub i : Submodule F V)
    refine Submodule.sum_mem _ (fun i _ => ?_)
    -- {lit}`(u i : V) ∈ V_sub i ≤ ∑ V_sub i`.
    exact (Finset.single_le_sum (f := V_sub) (fun j _ => bot_le)
      (Finset.mem_univ i)) (u i).property
  · -- {lit}`∑ V_sub i ⊆ range γ`: each {lit}`V_sub i ⊆ range γ`,
    -- and range is a submodule.
    have h_each : ∀ i, V_sub i ≤ LinearMap.range (gamma V_sub) := by
      intro i v hv
      classical
      let u : (j : Fin m) → V_sub j := fun j =>
        if h : j = i then h ▸ (⟨v, hv⟩ : V_sub i) else 0
      refine ⟨u, ?_⟩
      show ∑ j, ((u j : V_sub j) : V) = v
      rw [Finset.sum_eq_single i]
      · show ((u i : V_sub i) : V) = v
        simp [u]
      · intros j _ hji
        show ((u j : V_sub j) : V) = 0
        simp [u, hji]
      · intro h; exact absurd (Finset.mem_univ i) h
    exact Finset.sum_induction (f := V_sub)
      (p := fun U => U ≤ LinearMap.range (gamma V_sub))
      (fun _ _ ha hb => sup_le ha hb) bot_le (fun i _ => h_each i)

theorem directSum_iff_finrank_add [Finite F V] {m : ℕ}
    (V_sub : Fin m → Submodule F V) [∀ i, Module.Finite F (V_sub i)] :
    IsDirectSum V_sub ↔
      finrank F ↥(∑ i, V_sub i : Submodule F V) =
        ∑ i, finrank F (V_sub i) := by
  -- direct sum ↔ γ injective ↔ finrank ker γ = 0 ↔ finrank range = finrank dom.
  rw [directSum_iff_gamma_injective]
  rw [LADR.Section_3B.injective_iff_ker_eq_bot]
  have h_FTL := LADR.Section_3B.finrank_ker_add_finrank_range (gamma V_sub)
  rw [gamma_range_eq] at h_FTL
  rw [finrank_prod (V := fun i => (V_sub i : Type _))] at h_FTL
  constructor
  · intro hker_bot
    rw [hker_bot, finrank_bot] at h_FTL
    omega
  · intro hdim
    rw [← hdim] at h_FTL
    have : finrank F (LinearMap.ker (gamma V_sub)) = 0 := by omega
    rw [Submodule.finrank_eq_zero] at this
    exact this

/-! Quotient Spaces. -/

/-! 3.95 Notation {lit}`v + U`. For {lit}`v ∈ V` and {lit}`U ⊆ V`, the
translate is the set {lit}`{v + u : u ∈ U}`. -/

/-- The translate {lit}`v + U` as a {lit}`Set V`. -/
def translate (v : V) (U : Submodule F V) : Set V :=
  {w : V | ∃ u ∈ U, v + u = w}

example (v : V) (U : Submodule F V) (x : V) :
    x ∈ translate v U ↔ ∃ u ∈ U, v + u = x := Iff.rfl

/-! 3.97 Definition: a translate of {lit}`U` is a set of the form
{lit}`v + U`. -/

def IsTranslate (U : Submodule F V) (A : Set V) : Prop :=
  ∃ v : V, A = translate v U

/-! 3.99 Definition: quotient space {lit}`V/U` — mathlib's {name}`HasQuotient`
provides {lit}`V ⧸ U` as the set of translates. -/

example (U : Submodule F V) : Type _ := V ⧸ U

example (U : Submodule F V) (v : V) : V ⧸ U := Submodule.Quotient.mk v

/-! 3.101 Two translates of a subspace are equal or disjoint. -/

theorem translate_eq_iff (U : Submodule F V) (v w : V) :
    translate v U = translate w U ↔ v - w ∈ U := by
  constructor
  · intro heq
    have hv : v ∈ translate v U := ⟨0, U.zero_mem, by simp⟩
    rw [heq] at hv
    obtain ⟨u, hu, hwu⟩ := hv
    have h_eq : v - w = u := by
      rw [sub_eq_iff_eq_add, add_comm]; exact hwu.symm
    rw [h_eq]; exact hu
  · intro hvw
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      refine ⟨(v - w) + u, U.add_mem hvw hu, ?_⟩
      abel
    · rintro ⟨u, hu, rfl⟩
      refine ⟨(w - v) + u, U.add_mem ?_ hu, ?_⟩
      · rw [show w - v = -(v - w) from by abel]
        exact U.neg_mem hvw
      · abel

theorem translate_inter_nonempty_iff (U : Submodule F V) (v w : V) :
    (translate v U ∩ translate w U).Nonempty ↔ v - w ∈ U := by
  constructor
  · rintro ⟨x, hxv, hxw⟩
    obtain ⟨u₁, hu₁, hxv'⟩ := hxv
    obtain ⟨u₂, hu₂, hxw'⟩ := hxw
    have h : v + u₁ = w + u₂ := hxv'.trans hxw'.symm
    have hdiff : v - w = u₂ - u₁ := by
      rw [sub_eq_sub_iff_add_eq_add, add_comm u₂ w]; exact h
    rw [hdiff]
    exact U.sub_mem hu₂ hu₁
  · intro hvw
    refine ⟨v, ⟨0, U.zero_mem, by simp⟩, ?_⟩
    refine ⟨v - w, hvw, ?_⟩
    abel

theorem quotient_mk_eq_iff (U : Submodule F V) (v w : V) :
    (Submodule.Quotient.mk v : V ⧸ U) = Submodule.Quotient.mk w ↔ v - w ∈ U :=
  Submodule.Quotient.eq U

/-! 3.102 Addition and scalar multiplication on {lit}`V/U` — provided by
mathlib. -/

example (U : Submodule F V) (v w : V) :
    (Submodule.Quotient.mk v + Submodule.Quotient.mk w : V ⧸ U) =
      Submodule.Quotient.mk (v + w) := rfl

example (U : Submodule F V) (lam : F) (v : V) :
    (lam • (Submodule.Quotient.mk v : V ⧸ U)) =
      Submodule.Quotient.mk (lam • v) := rfl

/-! 3.103 {lit}`V/U` is a vector space (automatic in mathlib). -/

example (U : Submodule F V) : Module F (V ⧸ U) := inferInstance

/-! 3.104 Definition: quotient map {lit}`π : V → V/U`. -/

example (U : Submodule F V) : V →ₗ[F] V ⧸ U := U.mkQ

example (U : Submodule F V) (v : V) :
    U.mkQ v = Submodule.Quotient.mk v := rfl

/-! 3.105 Dimension of the quotient space. -/

@[avoiding Submodule.finrank_quotient]
theorem finrank_quotient [Finite F V] (U : Submodule F V) :
    finrank F (V ⧸ U) = finrank F V - finrank F U := by
  have h := Submodule.finrank_quotient_add_finrank U
  omega

/-! 3.106 Notation {lit}`T̃ : V/(null T) → W` — mathlib's
{name}`Submodule.liftQ` gives this. -/

variable {W : Type*} [AddCommGroup W] [Module F W]

noncomputable def Ttilde (T : V →ₗ[F] W) : V ⧸ LinearMap.ker T →ₗ[F] W :=
  Submodule.liftQ (LinearMap.ker T) T (le_refl _)

example (T : V →ₗ[F] W) (v : V) :
    Ttilde T (Submodule.Quotient.mk v) = T v := rfl

/-! 3.107 Properties of {lit}`T̃`. -/

/-- (a) {lit}`T̃ ∘ π = T`. -/
theorem Ttilde_comp_mkQ (T : V →ₗ[F] W) :
    Ttilde T ∘ₗ (LinearMap.ker T).mkQ = T := by
  ext v; rfl

/-- (b) {lit}`T̃` is injective. -/
theorem Ttilde_injective (T : V →ₗ[F] W) : Function.Injective (Ttilde T) := by
  rw [LADR.Section_3B.injective_iff_ker_eq_bot, Submodule.eq_bot_iff]
  intro x hx
  rw [LinearMap.mem_ker] at hx
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hTv : T v = 0 := hx
  exact (Submodule.Quotient.mk_eq_zero _).mpr hTv

/-- (c) {lit}`range T̃ = range T`. -/
theorem Ttilde_range (T : V →ₗ[F] W) :
    LinearMap.range (Ttilde T) = LinearMap.range T := by
  ext w
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact ⟨v, rfl⟩
  · rintro ⟨v, rfl⟩
    exact ⟨Submodule.Quotient.mk v, rfl⟩

/-- (d) {lit}`V/(null T)` and {lit}`range T` are isomorphic. -/
noncomputable def quotKer_equiv_range (T : V →ₗ[F] W) :
    (V ⧸ LinearMap.ker T) ≃ₗ[F] LinearMap.range T :=
  T.quotKerEquivRange

/-! # Exercises -/

/-- 3E.1 -/
theorem exercise_3E_1 {V W : Type*} [AddCommGroup V] [Module F V]
    [AddCommGroup W] [Module F W] (T : V → W) :
    (∃ S : V →ₗ[F] W, ∀ v, S v = T v) ↔
      ∃ (U : Submodule F (V × W)),
        (U : Set (V × W)) = {p | p.2 = T p.1} := by
  sorry

/-- 3E.2 -/
theorem exercise_3E_2 {m : ℕ} (V : Fin m → Type*) [∀ i, AddCommGroup (V i)]
    [∀ i, Module F (V i)] [Finite F ((i : Fin m) → V i)] (i : Fin m) :
    Finite F (V i) := by
  sorry

/-- 3E.3 -/
theorem exercise_3E_3 {m : ℕ} (V : Fin m → Type*) [∀ i, AddCommGroup (V i)]
    [∀ i, Module F (V i)] (W : Type*) [AddCommGroup W] [Module F W] :
    Nonempty ((((i : Fin m) → V i) →ₗ[F] W) ≃ₗ[F]
              ((i : Fin m) → (V i →ₗ[F] W))) := by
  sorry

/-- 3E.4 -/
theorem exercise_3E_4 {m : ℕ} (W : Fin m → Type*) [∀ i, AddCommGroup (W i)]
    [∀ i, Module F (W i)] (V : Type*) [AddCommGroup V] [Module F V] :
    Nonempty ((V →ₗ[F] ((i : Fin m) → W i)) ≃ₗ[F]
              ((i : Fin m) → (V →ₗ[F] W i))) := by
  sorry

/-- 3E.5 -/
theorem exercise_3E_5 (m : ℕ) :
    Nonempty ((Fin m → V) ≃ₗ[F] ((Fin m → F) →ₗ[F] V)) := by
  sorry

/-- 3E.6 -/
theorem exercise_3E_6 (v x : V) (U W : Submodule F V)
    (h : translate v U = translate x W) : U = W := by
  sorry

/-- 3E.7 -/
def exercise_3E_7_U : Submodule ℝ (Fin 3 → ℝ) where
  carrier := {v | 2 * v 0 + 3 * v 1 + 5 * v 2 = 0}
  zero_mem' := by simp
  add_mem' := by
    intro u v hu hv
    show 2 * (u + v) 0 + 3 * (u + v) 1 + 5 * (u + v) 2 = 0
    have hu' : 2 * u 0 + 3 * u 1 + 5 * u 2 = 0 := hu
    have hv' : 2 * v 0 + 3 * v 1 + 5 * v 2 = 0 := hv
    simp only [Pi.add_apply]; linarith
  smul_mem' := by
    intro a v hv
    show 2 * (a • v) 0 + 3 * (a • v) 1 + 5 * (a • v) 2 = 0
    have hv' : 2 * v 0 + 3 * v 1 + 5 * v 2 = 0 := hv
    simp only [Pi.smul_apply, smul_eq_mul]; linear_combination a * hv'

theorem exercise_3E_7 (A : Set (Fin 3 → ℝ)) :
    IsTranslate exercise_3E_7_U A ↔
      ∃ c : ℝ, A = {v : Fin 3 → ℝ | 2 * v 0 + 3 * v 1 + 5 * v 2 = c} := by
  sorry

/-- 3E.8 (a) -/
theorem exercise_3E_8a (T : V →ₗ[F] W) (c : W) :
    {x : V | T x = c} = ∅ ∨ IsTranslate (LinearMap.ker T) {x : V | T x = c} := by
  sorry

/-- 3E.9 -/
theorem exercise_3E_9 (A : Set V) (hA : A.Nonempty) :
    (∃ U : Submodule F V, IsTranslate U A) ↔
      ∀ v ∈ A, ∀ w ∈ A, ∀ lam : F, lam • v + (1 - lam) • w ∈ A := by
  sorry

/-- 3E.10 -/
theorem exercise_3E_10 (A₁ A₂ : Set V) (U₁ U₂ : Submodule F V)
    (v w : V) (_hA₁ : A₁ = translate v U₁) (_hA₂ : A₂ = translate w U₂) :
    A₁ ∩ A₂ = ∅ ∨ ∃ U : Submodule F V, IsTranslate U (A₁ ∩ A₂) := by
  sorry

/-- 3E.11 (a) -/
def exercise_3E_11_U : Submodule F (ℕ → F) where
  carrier := {x | ∀ᶠ k in Filter.atTop, x k = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    filter_upwards [hx, hy] with k hxk hyk
    show x k + y k = 0
    rw [hxk, hyk, add_zero]
  smul_mem' := by
    intro a x hx
    filter_upwards [hx] with k hxk
    show a • x k = 0
    rw [hxk, smul_zero]

/-- 3E.11 (b) -/
theorem exercise_3E_11b : ¬ Finite F ((ℕ → F) ⧸ exercise_3E_11_U (F := F)) := by
  sorry

/-- 3E.12 -/
theorem exercise_3E_12 {m : ℕ} (v : Fin m → V) :
    (∃ U : Submodule F V,
      IsTranslate U
        {x : V | ∃ lam : Fin m → F, (∑ i, lam i) = 1 ∧ x = ∑ i, lam i • v i}) := by
  sorry

/-- 3E.13 -/
theorem exercise_3E_13 (U : Submodule F V) [Finite F (V ⧸ U)] :
    Nonempty (V ≃ₗ[F] U × (V ⧸ U)) := by
  sorry

/-- 3E.14 -/
theorem exercise_3E_14 (U W : Submodule F V) (hUW : IsCompl U W) {m : ℕ}
    (w : Fin m → W) (hw : IsBasis F w) :
    IsBasis F (fun i => (Submodule.Quotient.mk (w i : V) : V ⧸ U)) := by
  sorry

/-- 3E.15 -/
theorem exercise_3E_15 (U : Submodule F V) {m n : ℕ}
    (v : Fin m → V) (hv : IsBasis F (fun i => (Submodule.Quotient.mk (v i) : V ⧸ U)))
    (u : Fin n → U) (hu : IsBasis F u) :
    IsBasis F (Fin.append v (fun i => (u i : V))) := by
  sorry

/-- 3E.16 -/
theorem exercise_3E_16 (phi : V →ₗ[F] F) (hphi : phi ≠ 0) :
    finrank F (V ⧸ LinearMap.ker phi) = 1 := by
  sorry

/-- 3E.17 -/
theorem exercise_3E_17 (U : Submodule F V) (h : finrank F (V ⧸ U) = 1) :
    ∃ phi : V →ₗ[F] F, LinearMap.ker phi = U := by
  sorry

/-- 3E.18 (a) -/
theorem exercise_3E_18a (U : Submodule F V) [Finite F (V ⧸ U)]
    (W : Submodule F V) [Finite F W] (hUW : U ⊔ W = ⊤) :
    finrank F W ≥ finrank F (V ⧸ U) := by
  sorry

/-- 3E.18 (b) -/
theorem exercise_3E_18b (U : Submodule F V) [Finite F (V ⧸ U)] :
    ∃ W : Submodule F V, Finite F W ∧
      finrank F W = finrank F (V ⧸ U) ∧ IsCompl U W := by
  sorry

/-- 3E.19 -/
theorem exercise_3E_19 (T : V →ₗ[F] W) (U : Submodule F V) :
    (∃ S : V ⧸ U →ₗ[F] W, T = S ∘ₗ U.mkQ) ↔ U ≤ LinearMap.ker T := by
  sorry

end LADR.Section_3E
