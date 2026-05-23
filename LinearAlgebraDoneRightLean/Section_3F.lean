import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
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
import LinearAlgebraDoneRightLean.Section_3D
import LinearAlgebraDoneRightLean.Section_3E
import CompanionHelper

/-!
# Axler, *Linear Algebra Done Right* (4e) — Section 3F: Duality
-/

namespace LADR.Section_3F

open LADR.Section_2A (Spans)
open LADR.Section_2B (IsBasis)
open Module (Finite finrank Dual)

variable {F : Type*} [Field F]
  {V : Type*} [AddCommGroup V] [Module F V]
  {W : Type*} [AddCommGroup W] [Module F W]
  {U : Type*} [AddCommGroup U] [Module F U]

/-! 3.108 Definition: linear functional — element of {lit}`V →ₗ[F] F`. -/

example : Type _ := V →ₗ[F] F

/-! 3.109 Examples of linear functionals. -/

/-- {lit}`φ(x, y, z) = 4x − 5y + 2z` on {lit}`ℝ³`. -/
def phi_3_109_a : (Fin 3 → ℝ) →ₗ[ℝ] ℝ where
  toFun v := 4 * v 0 - 5 * v 1 + 2 * v 2
  map_add' x y := by simp [Pi.add_apply]; ring
  map_smul' a x := by simp [Pi.smul_apply, smul_eq_mul]; ring

/-- {lit}`φ(x₁, …, xₙ) = c₁x₁ + ⋯ + cₙxₙ`. -/
def phi_3_109_b {n : ℕ} (c : Fin n → F) : (Fin n → F) →ₗ[F] F where
  toFun x := ∑ i, c i * x i
  map_add' x y := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [Pi.add_apply]; ring
  map_smul' a x := by
    show ∑ i, c i * (a • x) i = a • ∑ i, c i * x i
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Pi.smul_apply, smul_eq_mul, smul_eq_mul]
    ring

/-! 3.110 Definition: dual space {lit}`V'`.

In mathlib, the dual space of {lit}`V` is {name}`Module.Dual` which unfolds
to {lit}`V →ₗ[F] F`. -/

example : Type _ := Module.Dual F V
example : Module.Dual F V = (V →ₗ[F] F) := rfl

/-! 3.111 {lit}`dim V' = dim V` -/

@[avoiding Subspace.dual_finrank_eq]
theorem finrank_dual_eq_finrank [Finite F V] :
    finrank F (Module.Dual F V) = finrank F V := by
  show finrank F (V →ₗ[F] F) = finrank F V
  rw [LADR.Section_3D.finrank_linearMap, Module.finrank_self, mul_one]

/-! 3.112 Definition: dual basis.

In mathlib, given a basis {lit}`v₁, …, vₙ` of {lit}`V`, the dual basis is
provided by {name}`Module.Basis.dualBasis`. -/

noncomputable example {n : ℕ} (v : Fin n → V) (hv : IsBasis F v) :
    Fin n → Module.Dual F V := hv.toModuleBasis.dualBasis

/-! 3.113 Example: the dual basis of the standard basis of {lit}`Fⁿ`
selects the {lit}`j`-th coordinate. -/

example {n : ℕ} (j : Fin n) (x : Fin n → F) :
    (Pi.basisFun F (Fin n)).dualBasis j x = x j := by
  simp [Pi.basisFun_repr]

/-! 3.114 Dual basis gives coefficients for linear combination -/

theorem dualBasis_gives_coefficients {n : ℕ} (v : Fin n → V) (hv : IsBasis F v)
    (x : V) :
    x = ∑ j, hv.toModuleBasis.dualBasis j x • v j := by
  conv_lhs => rw [← hv.toModuleBasis.sum_repr x]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [show hv.toModuleBasis j = v j from IsBasis.toModuleBasis_apply hv j,
    Module.Basis.dualBasis_apply]

/-! 3.116 Dual basis is a basis of the dual space — converted from mathlib's
{name}`Module.Basis.dualBasis`. -/

theorem isBasis_dualBasis [Finite F V] {n : ℕ} (v : Fin n → V)
    (hv : IsBasis F v) : IsBasis F hv.toModuleBasis.dualBasis := by
  refine ⟨hv.toModuleBasis.dualBasis.linearIndependent, ?_⟩
  show Submodule.span F (Set.range hv.toModuleBasis.dualBasis) = ⊤
  exact hv.toModuleBasis.dualBasis.span_eq

/-! 3.118 Definition: dual map {lit}`T'`.

In mathlib, this is {name}`LinearMap.dualMap`. -/

example (T : V →ₗ[F] W) : Module.Dual F W →ₗ[F] Module.Dual F V := T.dualMap

example (T : V →ₗ[F] W) (phi : Module.Dual F W) (v : V) :
    T.dualMap phi v = phi (T v) := T.dualMap_apply phi v

/-! 3.119 Example: the dual map of differentiation. -/

example (phi : Module.Dual ℝ (Polynomial ℝ)) (hphi : ∀ p, phi p = p.eval 3) :
    ∀ p, (Polynomial.derivative.dualMap phi) p = (p.derivative).eval 3 := by
  intro p
  rw [LinearMap.dualMap_apply]
  exact hphi _

/-! 3.120 Algebraic properties of dual maps. -/

/-- (a) {lit}`(S + T)' = S' + T'` -/
example (S T : V →ₗ[F] W) : (S + T).dualMap = S.dualMap + T.dualMap := by
  ext phi v
  simp [LinearMap.dualMap_apply]

/-- (b) {lit}`(λT)' = λT'` -/
example (lam : F) (T : V →ₗ[F] W) : (lam • T).dualMap = lam • T.dualMap := by
  ext phi v
  simp [LinearMap.dualMap_apply]

/-- (c) {lit}`(ST)' = T'S'` -/
example (T : U →ₗ[F] V) (S : V →ₗ[F] W) :
    (S ∘ₗ T).dualMap = T.dualMap ∘ₗ S.dualMap := by
  ext phi v
  simp [LinearMap.dualMap_apply]

/-! 3.121 Definition: annihilator {lit}`U⁰`.

In mathlib, this is {name}`Submodule.dualAnnihilator`. -/

example (U_sub : Submodule F V) : Submodule F (Module.Dual F V) :=
  U_sub.dualAnnihilator

example (U_sub : Submodule F V) (phi : Module.Dual F V) :
    phi ∈ U_sub.dualAnnihilator ↔ ∀ u ∈ U_sub, phi u = 0 :=
  Submodule.mem_dualAnnihilator phi

/-! 3.124 The annihilator is a subspace — automatic since
{name}`Submodule.dualAnnihilator` returns a {name}`Submodule`. -/

example (U_sub : Submodule F V) : Submodule F (Module.Dual F V) :=
  U_sub.dualAnnihilator

/-! 3.125 Dimension of the annihilator. -/

theorem finrank_dualAnnihilator [Finite F V] (U_sub : Submodule F V) :
    finrank F U_sub.dualAnnihilator = finrank F V - finrank F U_sub := by
  have h := Subspace.finrank_add_finrank_dualAnnihilator_eq U_sub
  omega

/-! 3.127 Annihilator equals zero or the whole dual space. -/

theorem dualAnnihilator_eq_bot_iff [Finite F V] (U_sub : Submodule F V) :
    U_sub.dualAnnihilator = ⊥ ↔ U_sub = ⊤ := by
  have h := Subspace.finrank_add_finrank_dualAnnihilator_eq U_sub
  constructor
  · intro hbot
    rw [hbot, finrank_bot] at h
    have h_eq : finrank F U_sub = finrank F V := by omega
    exact LADR.Section_2C.subspace_eq_top_of_finrank_eq U_sub h_eq
  · intro htop; subst htop
    exact Submodule.dualAnnihilator_top

theorem dualAnnihilator_eq_top_iff [Finite F V] (U_sub : Submodule F V) :
    U_sub.dualAnnihilator = ⊤ ↔ U_sub = ⊥ := by
  have h := Subspace.finrank_add_finrank_dualAnnihilator_eq U_sub
  have hdim_dual : finrank F (Module.Dual F V) = finrank F V :=
    finrank_dual_eq_finrank
  constructor
  · intro htop
    have h_top : finrank F U_sub.dualAnnihilator = finrank F V := by
      rw [htop, ← hdim_dual]
      exact Submodule.topEquiv.finrank_eq
    have : finrank F U_sub = 0 := by omega
    rwa [Submodule.finrank_eq_zero] at this
  · intro hbot; subst hbot
    apply LADR.Section_2C.subspace_eq_top_of_finrank_eq
    rw [finrank_dual_eq_finrank]
    have : finrank F (⊥ : Submodule F V) = 0 := finrank_bot F V
    omega

/-! 3.128 The null space of {lit}`T'`. -/

/-- (a) {lit}`null T' = (range T)⁰`. -/
theorem ker_dualMap_eq_range_dualAnnihilator (T : V →ₗ[F] W) :
    LinearMap.ker T.dualMap = (LinearMap.range T).dualAnnihilator := by
  ext phi
  rw [LinearMap.mem_ker, Submodule.mem_dualAnnihilator]
  constructor
  · intro hphi w hw
    obtain ⟨v, rfl⟩ := hw
    have : T.dualMap phi v = 0 := by rw [hphi]; rfl
    rw [LinearMap.dualMap_apply] at this
    exact this
  · intro h
    ext v
    rw [LinearMap.dualMap_apply]
    exact h _ (LinearMap.mem_range_self T v)

/-- (b) {lit}`dim null T' = dim null T + dim W − dim V`. -/
theorem finrank_ker_dualMap [Finite F V] [Finite F W] (T : V →ₗ[F] W) :
    finrank F (LinearMap.ker T.dualMap) =
      finrank F (LinearMap.ker T) + finrank F W - finrank F V := by
  rw [ker_dualMap_eq_range_dualAnnihilator T, finrank_dualAnnihilator]
  have h := LADR.Section_3B.finrank_ker_add_finrank_range T
  omega

/-! 3.129 {lit}`T` surjective iff {lit}`T'` injective. -/

theorem surjective_iff_dualMap_injective [Finite F V] [Finite F W]
    (T : V →ₗ[F] W) :
    Function.Surjective T ↔ Function.Injective T.dualMap := by
  rw [LADR.Section_3B.surjective_iff_range_eq_top,
      LADR.Section_3B.injective_iff_ker_eq_bot,
      ker_dualMap_eq_range_dualAnnihilator,
      dualAnnihilator_eq_bot_iff]

/-! 3.130 The range of {lit}`T'`. -/

/-- (a) {lit}`dim range T' = dim range T`. -/
theorem finrank_range_dualMap [Finite F V] [Finite F W] (T : V →ₗ[F] W) :
    finrank F (LinearMap.range T.dualMap) = finrank F (LinearMap.range T) := by
  -- {lit}`dim range T' = dim W' − dim ker T' = dim W − dim (range T)⁰
  -- = dim W − (dim W − dim range T) = dim range T`.
  have h_FTL := LADR.Section_3B.finrank_ker_add_finrank_range T.dualMap
  rw [ker_dualMap_eq_range_dualAnnihilator, finrank_dualAnnihilator] at h_FTL
  rw [finrank_dual_eq_finrank] at h_FTL
  have h_range_le : finrank F (LinearMap.range T) ≤ finrank F W :=
    LADR.Section_2C.finrank_submodule_le (LinearMap.range T)
  omega

/-- (b) {lit}`range T' = (null T)⁰`. -/
theorem range_dualMap_eq_ker_dualAnnihilator [Finite F V] (T : V →ₗ[F] W) :
    LinearMap.range T.dualMap = (LinearMap.ker T).dualAnnihilator :=
  LinearMap.range_dualMap_eq_dualAnnihilator_ker T

/-! 3.131 {lit}`T` injective iff {lit}`T'` surjective. -/

theorem injective_iff_dualMap_surjective [Finite F V] [Finite F W]
    (T : V →ₗ[F] W) :
    Function.Injective T ↔ Function.Surjective T.dualMap := by
  rw [LADR.Section_3B.injective_iff_ker_eq_bot,
      LADR.Section_3B.surjective_iff_range_eq_top,
      range_dualMap_eq_ker_dualAnnihilator,
      dualAnnihilator_eq_top_iff]

/-! Matrix of Dual of Linear Map. -/

/-! 3.132 Matrix of {lit}`T'` is the transpose of matrix of {lit}`T`.

Given bases of V and W with their dual bases, the matrix of {lit}`T'` in
the dual bases equals the transpose of the matrix of {lit}`T`. -/

/-- Statement-level version: the matrix of {lit}`T'` (computed in the dual
bases) equals the transpose of the matrix of {lit}`T`. Stated using mathlib's
{name}`LinearMap.toMatrix` and {name}`Module.Basis.dualBasis` directly. -/
theorem toMatrix_dualMap_eq_transpose [Finite F V] [Finite F W] {m n : ℕ}
    (v : Fin n → V) (w : Fin m → W) (hv : IsBasis F v) (hw : IsBasis F w)
    (T : V →ₗ[F] W) :
    LinearMap.toMatrix hw.toModuleBasis.dualBasis hv.toModuleBasis.dualBasis
      T.dualMap =
        (LinearMap.toMatrix hv.toModuleBasis hw.toModuleBasis T).transpose := by
  sorry

/-! 3.133 Column rank equals row rank — re-proved using duality. We proved
this directly in {name}`LADR.Section_3C.columnRank_eq_rowRank`. -/

example {m n : ℕ} (A : Matrix (Fin m) (Fin n) F) :
    LADR.Section_3C.columnRank A = LADR.Section_3C.rowRank A :=
  LADR.Section_3C.columnRank_eq_rowRank A

/-! # Exercises -/

/-- 3F.1 Every linear functional is either surjective or the zero map. -/
theorem exercise_3F_1 (phi : V →ₗ[F] F) :
    Function.Surjective phi ∨ phi = 0 := by
  sorry

/-- 3F.3 -/
theorem exercise_3F_3 [Finite F V] (v : V) (hv : v ≠ 0) :
    ∃ phi : Module.Dual F V, phi v = 1 := by
  sorry

/-- 3F.4 -/
theorem exercise_3F_4 [Finite F V] (U_sub : Submodule F V) (hU : U_sub ≠ ⊤) :
    ∃ phi : Module.Dual F V, (∀ u ∈ U_sub, phi u = 0) ∧ phi ≠ 0 := by
  sorry

/-- 3F.5 -/
theorem exercise_3F_5 (T : V →ₗ[F] W) {m : ℕ} (w : Fin m → W)
    (hw : IsBasis F (fun i => (⟨w i, by sorry⟩ : LinearMap.range T))) :
    ∃ phi : Fin m → Module.Dual F V, ∀ v : V,
      T v = ∑ i, phi i v • w i := by
  sorry

/-- 3F.6 -/
theorem exercise_3F_6 (phi beta : Module.Dual F V) :
    LinearMap.ker phi ≤ LinearMap.ker beta ↔
      ∃ c : F, beta = c • phi := by
  sorry

/-- 3F.7 -/
theorem exercise_3F_7 {m : ℕ} (V_fam : Fin m → Type*)
    [∀ i, AddCommGroup (V_fam i)] [∀ i, Module F (V_fam i)] :
    Nonempty (Module.Dual F ((i : Fin m) → V_fam i) ≃ₗ[F]
              ((i : Fin m) → Module.Dual F (V_fam i))) := by
  sorry

/-- 3F.8 The maps {lit}`Γ(v) = (φ₁(v), …, φₙ(v))` and {lit}`Λ(a) = ∑ aᵢvᵢ`
are inverses. -/
theorem exercise_3F_8 {n : ℕ} (v : Fin n → V) (hv : IsBasis F v) :
    Function.LeftInverse
      (fun a : Fin n → F => ∑ i, a i • v i)
      (fun u : V => fun j => hv.toModuleBasis.dualBasis j u) ∧
    Function.RightInverse
      (fun a : Fin n → F => ∑ i, a i • v i)
      (fun u : V => fun j => hv.toModuleBasis.dualBasis j u) := by
  sorry

/-- 3F.9 The dual basis of {lit}`1, x, …, xᵐ` in {lit}`𝒫ₘ(ℝ)` is
{lit}`φₖ(p) = p^(k)(0)/k!`. -/
theorem exercise_3F_9 (m : ℕ) :
    ∃ basis : Fin (m + 1) → Polynomial.degreeLT ℝ (m + 1),
      IsBasis ℝ basis := by
  sorry

/-- 3F.11 -/
theorem exercise_3F_11 {n : ℕ} (v : Fin n → V) (hv : IsBasis F v)
    (psi : Module.Dual F V) :
    psi = ∑ j, psi (v j) • hv.toModuleBasis.dualBasis j := by
  sorry

/-- 3F.12 (a) -/
example (S T : V →ₗ[F] W) : (S + T).dualMap = S.dualMap + T.dualMap := by
  ext phi v; simp [LinearMap.dualMap_apply]

/-- 3F.12 (b) -/
example (lam : F) (T : V →ₗ[F] W) : (lam • T).dualMap = lam • T.dualMap := by
  ext phi v; simp [LinearMap.dualMap_apply]

/-- 3F.13 -/
example : (LinearMap.id : V →ₗ[F] V).dualMap = LinearMap.id := by
  ext phi v; simp

/-- 3F.16 -/
theorem exercise_3F_16 [Finite F W] (T : V →ₗ[F] W) :
    T.dualMap = 0 ↔ T = 0 := by
  sorry

/-- 3F.17 -/
theorem exercise_3F_17 [Finite F V] [Finite F W] (T : V →ₗ[F] W) :
    LADR.Section_3D.IsInvertible T ↔ LADR.Section_3D.IsInvertible T.dualMap := by
  sorry

/-- 3F.18 The map {lit}`T ↦ T'` is an isomorphism
{lit}`ℒ(V, W) ≃ₗ ℒ(W', V')`. -/
theorem exercise_3F_18 [Finite F V] [Finite F W] :
    Nonempty ((V →ₗ[F] W) ≃ₗ[F] (Module.Dual F W →ₗ[F] Module.Dual F V)) := by
  sorry

/-- 3F.19 -/
theorem exercise_3F_19 (U_sub : Submodule F V) (phi : Module.Dual F V) :
    phi ∈ U_sub.dualAnnihilator ↔ (U_sub : Set V) ⊆ LinearMap.ker phi := by
  sorry

/-- 3F.20 -/
theorem exercise_3F_20 [Finite F V] (U_sub : Submodule F V) :
    (U_sub : Set V) =
      {v : V | ∀ phi ∈ U_sub.dualAnnihilator, phi v = 0} := by
  sorry

/-- 3F.21 (a) -/
theorem exercise_3F_21a [Finite F V] (U_sub W_sub : Submodule F V) :
    W_sub.dualAnnihilator ≤ U_sub.dualAnnihilator ↔ U_sub ≤ W_sub := by
  sorry

/-- 3F.21 (b) -/
theorem exercise_3F_21b [Finite F V] (U_sub W_sub : Submodule F V) :
    W_sub.dualAnnihilator = U_sub.dualAnnihilator ↔ U_sub = W_sub := by
  sorry

/-- 3F.22 (a) -/
theorem exercise_3F_22a [Finite F V] (U_sub W_sub : Submodule F V) :
    (U_sub ⊔ W_sub).dualAnnihilator =
      U_sub.dualAnnihilator ⊓ W_sub.dualAnnihilator := by
  sorry

/-- 3F.22 (b) -/
theorem exercise_3F_22b [Finite F V] (U_sub W_sub : Submodule F V) :
    (U_sub ⊓ W_sub).dualAnnihilator =
      U_sub.dualAnnihilator ⊔ W_sub.dualAnnihilator := by
  sorry

/-- 3F.30 -/
theorem exercise_3F_30 [Finite F V] {n : ℕ} (phi : Fin n → Module.Dual F V)
    (hphi : IsBasis F phi) :
    ∃ v : Fin n → V, ∃ hv : IsBasis F v,
      ∀ j, hv.toModuleBasis.dualBasis j = phi j := by
  sorry

/-- 3F.32 (a) {lit}`Λ : V → V''` is linear. -/
def exercise_3F_32_Lambda : V →ₗ[F] Module.Dual F (Module.Dual F V) where
  toFun v := { toFun := fun phi => phi v
               map_add' := fun phi psi => rfl
               map_smul' := fun a phi => rfl }
  map_add' u v := by ext phi; simp
  map_smul' a v := by ext phi; simp

/-- 3F.32 (c) {lit}`Λ` is an isomorphism when {lit}`V` is finite-dimensional. -/
theorem exercise_3F_32c [Finite F V] :
    Function.Bijective (exercise_3F_32_Lambda (F := F) (V := V)) := by
  sorry

/-- 3F.33 (a) The quotient map {lit}`π'` is injective. -/
theorem exercise_3F_33a (U_sub : Submodule F V) :
    Function.Injective U_sub.mkQ.dualMap := by
  sorry

/-- 3F.33 (b) {lit}`range π' = U⁰`. -/
theorem exercise_3F_33b (U_sub : Submodule F V) :
    LinearMap.range U_sub.mkQ.dualMap = U_sub.dualAnnihilator := by
  sorry

end LADR.Section_3F
