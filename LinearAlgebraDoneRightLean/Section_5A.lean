import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Polynomial.DegreeLT
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Ring
import Mathlib.Tactic.TFAE
import LinearAlgebraDoneRightLean.Section_2A
import LinearAlgebraDoneRightLean.Section_2B
import LinearAlgebraDoneRightLean.Section_2C
import LinearAlgebraDoneRightLean.Section_3A
import LinearAlgebraDoneRightLean.Section_3B
import LinearAlgebraDoneRightLean.Section_3D
import CompanionHelper

/-!
# Axler, *Linear Algebra Done Right* (4e) — Section 5A: Invariant Subspaces
-/

namespace LADR.Section_5A

open LADR.Section_2B (IsBasis)
open LADR.Section_3D (IsInvertible)
open LinearMap (ker range)
open Module (Finite finrank)
open Polynomial (aeval)

variable {F : Type*} [Field F]
  {V : Type*} [AddCommGroup V] [Module F V]

/-! 5.1 Definition: operator

A linear map from a vector space to itself is called an *operator*;
Axler writes {lit}`ℒ(V) = ℒ(V, V)`. In Lean an operator is simply
{lit}`T : V →ₗ[F] V`; mathlib's {name}`Module.End` is definitionally the
same type, and provides the ring structure (composition as multiplication,
powers, etc.) that we use later in this section. -/

example : Module.End F V = (V →ₗ[F] V) := rfl

/-! 5.2 Definition: invariant subspace -/

/-- A subspace {lit}`U` of {lit}`V` is *invariant under* {lit}`T ∈ ℒ(V)` if
{lit}`Tu ∈ U` for every {lit}`u ∈ U`. -/
def InvariantUnder (T : V →ₗ[F] V) (U : Submodule F V) : Prop :=
  ∀ u ∈ U, T u ∈ U

/-- Equivalently, {lit}`U` is invariant under {lit}`T` iff the image of
{lit}`U` under {lit}`T` is contained in {lit}`U`. (In mathlib the lattice of
invariant submodules is {name}`Module.End.invtSubmodule`.) -/
theorem invariantUnder_iff_map_le (T : V →ₗ[F] V) (U : Submodule F V) :
    InvariantUnder T U ↔ U.map T ≤ U := by
  constructor
  · rintro h _ ⟨u, hu, rfl⟩
    exact h u hu
  · intro h u hu
    exact h ⟨u, hu, rfl⟩

/-- Thus {lit}`U` is invariant under {lit}`T` iff {lit}`T` restricts to an
operator {lit}`T|_U ∈ ℒ(U)` — mathlib's {name}`LinearMap.restrict`. -/
noncomputable def InvariantUnder.restrict {T : V →ₗ[F] V} {U : Submodule F V}
    (h : InvariantUnder T U) : U →ₗ[F] U :=
  T.restrict h

@[simp]
theorem InvariantUnder.restrict_apply {T : V →ₗ[F] V} {U : Submodule F V}
    (h : InvariantUnder T U) (u : U) :
    (h.restrict u : V) = T u := rfl

/-! 5.3 Example: {lit}`𝒫₄(ℝ)` (here {lit}`degreeLT ℝ 5`) is invariant under
the differentiation operator {lit}`p ↦ p′` on {lit}`𝒫(ℝ)`, because
differentiation does not raise degree. -/

example : InvariantUnder (Polynomial.derivative : Polynomial ℝ →ₗ[ℝ] Polynomial ℝ)
    (Polynomial.degreeLT ℝ 5) := by
  intro p hp
  rw [Polynomial.mem_degreeLT] at hp ⊢
  exact lt_of_le_of_lt (Polynomial.degree_derivative_le (p := p)) hp

/-! 5.4 Example: four invariant subspaces, not necessarily all different:
{lit}`{0}`, {lit}`V`, {lit}`null T`, {lit}`range T`. -/

example (T : V →ₗ[F] V) : InvariantUnder T ⊥ := by
  intro u hu
  rw [Submodule.mem_bot] at hu ⊢
  rw [hu, map_zero]

example (T : V →ₗ[F] V) : InvariantUnder T ⊤ :=
  fun _u _ => Submodule.mem_top

example (T : V →ₗ[F] V) : InvariantUnder T (ker T) := by
  intro u hu
  rw [LinearMap.mem_ker] at hu ⊢
  rw [hu, map_zero]

example (T : V →ₗ[F] V) : InvariantUnder T (range T) :=
  fun u _ => LinearMap.mem_range_self T u

/-! One-dimensional invariant subspaces: for {lit}`v ≠ 0`, the line
{lit}`span(v)` is invariant under {lit}`T` iff {lit}`Tv` is a scalar multiple
of {lit}`v`. This computation motivates the definition of eigenvalue. -/

theorem span_singleton_invariant_iff (T : V →ₗ[F] V) {v : V} (_hv : v ≠ 0) :
    InvariantUnder T (Submodule.span F {v}) ↔ ∃ lam : F, T v = lam • v := by
  constructor
  · intro h
    have hTv : T v ∈ Submodule.span F {v} :=
      h v (Submodule.mem_span_singleton_self v)
    obtain ⟨lam, hlam⟩ := Submodule.mem_span_singleton.mp hTv
    exact ⟨lam, hlam.symm⟩
  · rintro ⟨lam, hlam⟩ u hu
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hu
    rw [map_smul, hlam, smul_smul]
    exact Submodule.mem_span_singleton.mpr ⟨a * lam, rfl⟩

/-! 5.5 Definition: eigenvalue -/

/-- {lit}`λ ∈ F` is an *eigenvalue* of {lit}`T ∈ ℒ(V)` if there exists
{lit}`v ∈ V` with {lit}`v ≠ 0` and {lit}`Tv = λv`. -/
def IsEigenvalue (T : V →ₗ[F] V) (lam : F) : Prop :=
  ∃ v : V, v ≠ 0 ∧ T v = lam • v

/-- Bridge to mathlib, where the same notion is
{name}`Module.End.HasEigenvalue` (defined via a nontrivial eigenspace). -/
theorem isEigenvalue_iff_hasEigenvalue (T : V →ₗ[F] V) (lam : F) :
    IsEigenvalue T lam ↔ Module.End.HasEigenvalue T lam := by
  constructor
  · rintro ⟨v, hv, hTv⟩
    exact Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.mpr hTv, hv⟩
  · intro h
    obtain ⟨v, hv⟩ := h.exists_hasEigenvector
    exact ⟨v, hv.2, Module.End.mem_eigenspace_iff.mp hv.1⟩

/-- {lit}`V` has a one-dimensional subspace invariant under {lit}`T` iff
{lit}`T` has an eigenvalue. -/
theorem exists_invariant_line_iff (T : V →ₗ[F] V) :
    (∃ v : V, v ≠ 0 ∧ InvariantUnder T (Submodule.span F {v})) ↔
      ∃ lam : F, IsEigenvalue T lam := by
  constructor
  · rintro ⟨v, hv, hinv⟩
    obtain ⟨lam, hlam⟩ := (span_singleton_invariant_iff T hv).mp hinv
    exact ⟨lam, v, hv, hlam⟩
  · rintro ⟨lam, v, hv, hlam⟩
    exact ⟨v, hv, (span_singleton_invariant_iff T hv).mpr ⟨lam, hlam⟩⟩

/-! 5.6 Example: {lit}`T(x, y, z) = (7x + 3z, 3x + 6y + 9z, −6y)` on
{lit}`F³` has eigenvalue {lit}`6`, with eigenvector {lit}`(3, 1, −1)`. -/

def T_5_6 : (Fin 3 → F) →ₗ[F] (Fin 3 → F) where
  toFun v := ![7 * v 0 + 3 * v 2, 3 * v 0 + 6 * v 1 + 9 * v 2, -(6 * v 1)]
  map_add' x y := by
    funext i
    fin_cases i <;> simp <;> ring
  map_smul' a x := by
    funext i
    fin_cases i <;> simp <;> ring

example : IsEigenvalue (T_5_6 (F := F)) 6 := by
  refine ⟨![3, 1, -1], ?_, ?_⟩
  · intro h
    have h1 : (![3, 1, -1] : Fin 3 → F) 1 = 0 := by rw [h]; rfl
    simp at h1
  · funext i
    fin_cases i <;> simp [T_5_6] <;> norm_num

/-! 5.7 Equivalent conditions to be an eigenvalue (finite-dimensional case):
{lit}`λ` is an eigenvalue of {lit}`T` iff {lit}`T − λI` is not injective, iff
{lit}`T − λI` is not surjective, iff {lit}`T − λI` is not invertible.
The last three equivalences are Axler's 3.65
({name}`LADR.Section_3D.tfae_isInvertible`). -/

theorem tfae_isEigenvalue [Finite F V] (T : V →ₗ[F] V) (lam : F) :
    [IsEigenvalue T lam,
      ¬ Function.Injective (T - lam • (LinearMap.id : V →ₗ[F] V)),
      ¬ Function.Surjective (T - lam • (LinearMap.id : V →ₗ[F] V)),
      ¬ IsInvertible (T - lam • (LinearMap.id : V →ₗ[F] V))].TFAE := by
  have h365 := LADR.Section_3D.tfae_isInvertible (F := F) (V := V) (W := V)
    rfl (T - lam • LinearMap.id)
  -- (a) ↔ (b): {lit}`Tv = λv` iff {lit}`(T − λI)v = 0`.
  tfae_have 1 ↔ 2 := by
    constructor
    · rintro ⟨v, hv, hTv⟩ hinj
      apply hv
      have h0 : (T - lam • (LinearMap.id : V →ₗ[F] V)) v = 0 := by
        rw [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
          hTv, sub_self]
      exact hinj (by simpa using h0)
    · intro hinj
      rw [LADR.Section_3B.injective_iff_ker_eq_bot] at hinj
      obtain ⟨v, hv_mem, hv_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hinj
      refine ⟨v, hv_ne, ?_⟩
      rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
        LinearMap.id_apply, sub_eq_zero] at hv_mem
      exact hv_mem
  tfae_have 2 ↔ 3 := not_congr (h365.out 1 2)
  tfae_have 2 ↔ 4 := not_congr (h365.out 1 0)
  tfae_finish

/-! 5.8 Definition: eigenvector -/

/-- A vector {lit}`v ∈ V` is an *eigenvector* of {lit}`T` corresponding to the
eigenvalue {lit}`λ` if {lit}`v ≠ 0` and {lit}`Tv = λv`. (mathlib:
{name}`Module.End.HasEigenvector`.) -/
def IsEigenvector (T : V →ₗ[F] V) (lam : F) (v : V) : Prop :=
  v ≠ 0 ∧ T v = lam • v

theorem isEigenvector_iff_hasEigenvector (T : V →ₗ[F] V) (lam : F) (v : V) :
    IsEigenvector T lam v ↔ Module.End.HasEigenvector T lam v := by
  constructor
  · rintro ⟨hv, hTv⟩
    exact ⟨Module.End.mem_eigenspace_iff.mpr hTv, hv⟩
  · rintro ⟨hmem, hv⟩
    exact ⟨hv, Module.End.mem_eigenspace_iff.mp hmem⟩

/-- A nonzero vector {lit}`v` is an eigenvector of {lit}`T` corresponding to
{lit}`λ` iff {lit}`v ∈ null (T − λI)`. -/
theorem isEigenvector_iff_mem_ker (T : V →ₗ[F] V) (lam : F) (v : V) :
    IsEigenvector T lam v ↔ v ≠ 0 ∧ v ∈ ker (T - lam • LinearMap.id) := by
  unfold IsEigenvector
  rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
  simp [eq_comm]

/-! 5.9 Example: {lit}`T(w, z) = (−z, w)`.

(a) Over {lit}`ℝ` this is rotation by 90°, which sends no nonzero vector to a
scalar multiple of itself: {lit}`T` has no (real) eigenvalues.

(b) Over {lit}`ℂ`, solving {lit}`T(w, z) = λ(w, z)` (equations 5.10) leads to
{lit}`λ² = −1`, so the eigenvalues are exactly {lit}`i` and {lit}`−i`. -/

def T_5_9 (F : Type*) [Field F] : (Fin 2 → F) →ₗ[F] (Fin 2 → F) where
  toFun v := ![-v 1, v 0]
  map_add' x y := by
    funext i
    fin_cases i
    · simp [add_comm]
    · simp
  map_smul' a x := by
    funext i
    fin_cases i <;> simp

example : ¬ ∃ lam : ℝ, IsEigenvalue (T_5_9 ℝ) lam := by
  rintro ⟨lam, v, hv, hTv⟩
  -- The two coordinates of {lit}`Tv = λv` say {lit}`−v₁ = λv₀` and
  -- {lit}`v₀ = λv₁`; together {lit}`(λ² + 1)v₁ = 0` and {lit}`(λ² + 1)v₀ = 0`.
  have h0 : -v 1 = lam * v 0 := congrFun hTv 0
  have h1 : v 0 = lam * v 1 := congrFun hTv 1
  have h2 : (1 + lam ^ 2) * v 0 = 0 := by linear_combination h1 - lam * h0
  have h3 : (1 + lam ^ 2) * v 1 = 0 := by linear_combination -h0 - lam * h1
  have hpos : (0 : ℝ) < 1 + lam ^ 2 := by positivity
  apply hv
  funext i
  fin_cases i
  · exact (mul_eq_zero.mp h2).resolve_left (ne_of_gt hpos)
  · exact (mul_eq_zero.mp h3).resolve_left (ne_of_gt hpos)

example : ∀ lam : ℂ, IsEigenvalue (T_5_9 ℂ) lam ↔
    lam = Complex.I ∨ lam = -Complex.I := by
  intro lam
  constructor
  · rintro ⟨v, hv, hTv⟩
    have h0 : -v 1 = lam * v 0 := congrFun hTv 0
    have h1 : v 0 = lam * v 1 := congrFun hTv 1
    -- {lit}`−v₁ = λ²v₁`; if {lit}`v₁ = 0` then also {lit}`v₀ = 0`,
    -- contradicting {lit}`v ≠ 0`. Hence {lit}`λ² = −1`.
    have hv1 : v 1 ≠ 0 := by
      intro h
      apply hv
      funext i
      fin_cases i
      · simpa [h] using h1
      · exact h
    have hlam_sq : lam ^ 2 = -1 := by
      have h2 : lam ^ 2 * v 1 = -v 1 := by
        rw [pow_two, mul_assoc, ← h1, ← h0]
      have h3 : (lam ^ 2 + 1) * v 1 = 0 := by linear_combination h2
      rcases mul_eq_zero.mp h3 with h | h
      · linear_combination h
      · exact absurd h hv1
    have hfactor : (lam - Complex.I) * (lam + Complex.I) = 0 := by
      have : Complex.I ^ 2 = -1 := Complex.I_sq
      linear_combination hlam_sq - this
    rcases mul_eq_zero.mp hfactor with h | h
    · exact Or.inl (by linear_combination h)
    · exact Or.inr (by linear_combination h)
  · rintro (rfl | rfl)
    · -- eigenvector {lit}`(1, −i)` for {lit}`λ = i`
      refine ⟨![1, -Complex.I], ?_, ?_⟩
      · intro h
        have h0 : (![1, -Complex.I] : Fin 2 → ℂ) 0 = 0 := by rw [h]; rfl
        simp at h0
      · funext i
        fin_cases i <;> simp [T_5_9]
    · -- eigenvector {lit}`(1, i)` for {lit}`λ = −i`
      refine ⟨![1, Complex.I], ?_, ?_⟩
      · intro h
        have h0 : (![1, Complex.I] : Fin 2 → ℂ) 0 = 0 := by rw [h]; rfl
        simp at h0
      · funext i
        fin_cases i <;> simp [T_5_9]

/-! 5.11 Linearly independent eigenvectors.

Axler's proof takes a minimal-length linearly dependent list of eigenvectors,
applies {lit}`T − λₘI` to a dependence relation, and contradicts minimality.
mathlib proves the same statement (by induction) as
{name}`Module.End.eigenvectors_linearIndependent'`; we bridge to it. -/

theorem eigenvectors_linearIndependent (T : V →ₗ[F] V) {m : ℕ}
    (lam : Fin m → F) (hlam : Function.Injective lam) (v : Fin m → V)
    (hv : ∀ k, IsEigenvector T (lam k) (v k)) :
    LinearIndependent F v :=
  Module.End.eigenvectors_linearIndependent' T lam hlam v
    fun k => (isEigenvector_iff_hasEigenvector T (lam k) (v k)).mp (hv k)

/-! 5.12 An operator cannot have more eigenvalues than the dimension of the
vector space. -/

theorem card_eigenvalues_le_finrank [Finite F V] (T : V →ₗ[F] V) {m : ℕ}
    (lam : Fin m → F) (hlam : Function.Injective lam)
    (hev : ∀ k, IsEigenvalue T (lam k)) : m ≤ finrank F V := by
  -- Choose an eigenvector for each eigenvalue; by 5.11 the list is linearly
  -- independent, so its length is at most {lit}`dim V` (2.22).
  choose v hv_ne hv_eq using hev
  have hli : LinearIndependent F v :=
    eigenvectors_linearIndependent T lam hlam v fun k => ⟨hv_ne k, hv_eq k⟩
  simpa using hli.fintype_card_le_finrank

/-! Polynomials Applied to Operators -/

/-! 5.13 Notation: {lit}`Tᵐ`.

Because {lit}`V →ₗ[F] V` is mathlib's {name}`Module.End`, it is a monoid
under composition and the power {lit}`T ^ m` is available, with
{lit}`T⁰ = I` (mathlib's {lit}`1 = LinearMap.id`). For invertible {lit}`T`
the negative powers are {lit}`T⁻ᵐ = (T⁻¹)ᵐ`. -/

example (T : V →ₗ[F] V) (m : ℕ) : V →ₗ[F] V := T ^ m

example (T : V →ₗ[F] V) : T ^ 0 = LinearMap.id := rfl

example (T : V →ₗ[F] V) : T ^ 1 = T := pow_one T

example (T S : V →ₗ[F] V) : T * S = T ∘ₗ S := rfl

-- {lit}`T⁻ᵐ = (T⁻¹)ᵐ` for invertible {lit}`T`, via 3D's inverse.
noncomputable example (T : V →ₗ[F] V) (h : IsInvertible T) (m : ℕ) :
    V →ₗ[F] V :=
  h.inv ^ m

-- "You should verify that ...": {lit}`TᵐTⁿ = Tᵐ⁺ⁿ` and {lit}`(Tᵐ)ⁿ = Tᵐⁿ`.
example (T : V →ₗ[F] V) (m n : ℕ) : T ^ m * T ^ n = T ^ (m + n) :=
  (pow_add T m n).symm

example (T : V →ₗ[F] V) (m n : ℕ) : (T ^ m) ^ n = T ^ (m * n) :=
  (pow_mul T m n).symm

/-! 5.14 Notation: {lit}`p(T)`.

For {lit}`p(z) = a₀ + a₁z + ⋯ + aₘzᵐ`, the operator {lit}`p(T)` is
{lit}`a₀I + a₁T + ⋯ + aₘTᵐ`. In mathlib this is {name}`Polynomial.aeval`
(evaluation of a polynomial in the {lit}`F`-algebra {lit}`ℒ(V)`). -/

noncomputable example (T : V →ₗ[F] V) (p : Polynomial F) : V →ₗ[F] V :=
  aeval T p

example (T : V →ₗ[F] V) (p : Polynomial F) :
    aeval T p = ∑ k ∈ Finset.range (p.natDegree + 1), p.coeff k • T ^ k :=
  Polynomial.aeval_eq_sum_range (R := F) T

-- The constant term becomes {lit}`a₀ I`:
example (T : V →ₗ[F] V) (a : F) :
    aeval T (Polynomial.C a) = a • LinearMap.id := by
  rw [Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one]
  rfl

example (T : V →ₗ[F] V) : aeval T (Polynomial.X : Polynomial F) = T :=
  Polynomial.aeval_X T

/-! 5.15 Example: for the differentiation operator {lit}`D q = q′` and
{lit}`p(x) = 7 − 3x + 5x²`, we get {lit}`p(D) q = 7q − 3q′ + 5q″`. -/

example (q : Polynomial ℝ) :
    aeval (Polynomial.derivative : Polynomial ℝ →ₗ[ℝ] Polynomial ℝ)
        (Polynomial.C (7 : ℝ) - Polynomial.C 3 * Polynomial.X +
          Polynomial.C 5 * Polynomial.X ^ 2) q =
      (7 : ℝ) • q - (3 : ℝ) • Polynomial.derivative q +
        (5 : ℝ) • Polynomial.derivative (Polynomial.derivative q) := by
  simp only [map_add, map_sub, map_mul, Polynomial.aeval_C,
    Polynomial.aeval_X, Algebra.algebraMap_eq_smul_one, pow_two,
    LinearMap.add_apply, LinearMap.sub_apply, Module.End.mul_apply,
    LinearMap.smul_apply, Module.End.one_apply]

/-- For fixed {lit}`T`, the function {lit}`p ↦ p(T)` from {lit}`𝒫(F)` to
{lit}`ℒ(V)` is linear (as you should verify). -/
example (T : V →ₗ[F] V) (a : F) (p q : Polynomial F) :
    aeval T (a • p + q) = a • aeval T p + aeval T q := by
  rw [map_add, map_smul]

/-! 5.16 Definition: product of polynomials — mathlib's {lit}`p * q`,
satisfying {lit}`(pq)(z) = p(z)q(z)`. -/

example (p q : Polynomial F) (z : F) : (p * q).eval z = p.eval z * q.eval z :=
  Polynomial.eval_mul

/-! 5.17 Multiplicative properties: {lit}`(pq)(T) = p(T)q(T)` and
{lit}`p(T)q(T) = q(T)p(T)`. Both follow because {lit}`aeval T` is a ring
homomorphism into the commutative image generated by {lit}`T`. -/

theorem aeval_mul_eq_comp (T : V →ₗ[F] V) (p q : Polynomial F) :
    aeval T (p * q) = aeval T p ∘ₗ aeval T q := by
  rw [map_mul]
  rfl

theorem aeval_comp_comm (T : V →ₗ[F] V) (p q : Polynomial F) :
    aeval T p ∘ₗ aeval T q = aeval T q ∘ₗ aeval T p := by
  rw [← aeval_mul_eq_comp, ← aeval_mul_eq_comp, mul_comm]

/-- In particular {lit}`p(T)` commutes with {lit}`T` itself (take
{lit}`q = X` in 5.17). -/
theorem aeval_comm_self (T : V →ₗ[F] V) (p : Polynomial F) (v : V) :
    aeval T p (T v) = T (aeval T p v) := by
  have h := aeval_comp_comm T p Polynomial.X
  rw [Polynomial.aeval_X] at h
  exact LinearMap.congr_fun h v

/-! 5.18 Null space and range of {lit}`p(T)` are invariant under {lit}`T`. -/

theorem ker_aeval_invariant (T : V →ₗ[F] V) (p : Polynomial F) :
    InvariantUnder T (ker (aeval T p)) := by
  intro u hu
  rw [LinearMap.mem_ker] at hu ⊢
  -- {lit}`p(T)(Tu) = T(p(T)u) = T0 = 0`.
  rw [aeval_comm_self, hu, map_zero]

theorem range_aeval_invariant (T : V →ₗ[F] V) (p : Polynomial F) :
    InvariantUnder T (range (aeval T p)) := by
  rintro u hu
  obtain ⟨v, rfl⟩ := hu
  -- {lit}`T(p(T)v) = p(T)(Tv) ∈ range p(T)`.
  exact ⟨T v, aeval_comm_self T p v⟩

/-! # Exercises -/

/-- 5A.1 (a) -/
theorem exercise_5A_1a (T : V →ₗ[F] V) (U : Submodule F V)
    (h : U ≤ ker T) : InvariantUnder T U := by
  sorry

/-- 5A.1 (b) -/
theorem exercise_5A_1b (T : V →ₗ[F] V) (U : Submodule F V)
    (h : range T ≤ U) : InvariantUnder T U := by
  sorry

/-- 5A.2 -/
theorem exercise_5A_2 (T : V →ₗ[F] V) {m : ℕ} (W : Fin m → Submodule F V)
    (h : ∀ i, InvariantUnder T (W i)) : InvariantUnder T (⨆ i, W i) := by
  sorry

/-- 5A.3 -/
theorem exercise_5A_3 (T : V →ₗ[F] V) (𝒮 : Set (Submodule F V))
    (h : ∀ U ∈ 𝒮, InvariantUnder T U) : InvariantUnder T (sInf 𝒮) := by
  sorry

/-- 5A.4 Prove or give a counterexample: if {lit}`U` is invariant under every
operator on a finite-dimensional {lit}`V`, then {lit}`U = {0}` or
{lit}`U = V`. -/
def exercise_5A_4 [Finite F V] :
    Decidable (∀ U : Submodule F V,
      (∀ T : V →ₗ[F] V, InvariantUnder T U) → U = ⊥ ∨ U = ⊤) := by
  -- first line should be `apply isTrue` or `apply isFalse`
  sorry

/-- 5A.5 {lit}`T(x, y) = (−3y, x)` on {lit}`ℝ²`: find the eigenvalues. -/
def T_ex_5A_5 : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) where
  toFun v := ![-(3 * v 1), v 0]
  map_add' x y := by
    funext i
    fin_cases i
    · simp [mul_add, add_comm]
    · simp
  map_smul' a x := by
    funext i
    fin_cases i
    · simp [mul_left_comm]
    · simp

theorem exercise_5A_5 : ∀ lam : ℝ, ¬ IsEigenvalue T_ex_5A_5 lam := by
  sorry

/-- 5A.6 {lit}`T(w, z) = (z, w)` on {lit}`F²`: the eigenvalues are
{lit}`1` and {lit}`−1`… -/
def T_ex_5A_6 : (Fin 2 → F) →ₗ[F] (Fin 2 → F) where
  toFun v := ![v 1, v 0]
  map_add' x y := by
    funext i
    fin_cases i <;> simp
  map_smul' a x := by
    funext i
    fin_cases i <;> simp

theorem exercise_5A_6a : ∀ lam : F, IsEigenvalue (T_ex_5A_6 (F := F)) lam ↔
    lam = 1 ∨ lam = -1 := by
  sorry

/-- …with eigenvectors the nonzero vectors {lit}`(w, w)` resp.
{lit}`(w, −w)`. -/
theorem exercise_5A_6b (v : Fin 2 → F) :
    (IsEigenvector (T_ex_5A_6 (F := F)) 1 v ↔ v ≠ 0 ∧ v 1 = v 0) ∧
    (IsEigenvector (T_ex_5A_6 (F := F)) (-1) v ↔ v ≠ 0 ∧ v 1 = -v 0) := by
  sorry

/-- 5A.7 {lit}`T(z₁, z₂, z₃) = (2z₂, 0, 5z₃)` on {lit}`F³`: find all
eigenvalues and eigenvectors. -/
def T_ex_5A_7 : (Fin 3 → F) →ₗ[F] (Fin 3 → F) where
  toFun v := ![2 * v 1, 0, 5 * v 2]
  map_add' x y := by
    funext i
    fin_cases i <;> simp <;> ring
  map_smul' a x := by
    funext i
    fin_cases i <;> simp <;> ring

theorem exercise_5A_7a : ∀ lam : F, IsEigenvalue (T_ex_5A_7 (F := F)) lam ↔
    lam = 0 ∨ lam = 5 := by
  sorry

theorem exercise_5A_7b (v : Fin 3 → F) :
    (IsEigenvector (T_ex_5A_7 (F := F)) 0 v ↔
      v ≠ 0 ∧ v 1 = 0 ∧ v 2 = 0) ∧
    (IsEigenvector (T_ex_5A_7 (F := F)) 5 v ↔
      v ≠ 0 ∧ v 0 = 0 ∧ v 1 = 0) := by
  sorry

/-- 5A.8 -/
theorem exercise_5A_8 (P : V →ₗ[F] V) (hP : P ∘ₗ P = P) (lam : F)
    (h : IsEigenvalue P lam) : lam = 0 ∨ lam = 1 := by
  sorry

/-- 5A.9 The differentiation operator on {lit}`𝒫(ℝ)`: the only eigenvalue is
{lit}`0`, and its eigenvectors are the nonzero constant polynomials. -/
theorem exercise_5A_9 :
    (∀ lam : ℝ,
      IsEigenvalue (Polynomial.derivative : Polynomial ℝ →ₗ[ℝ] Polynomial ℝ)
        lam ↔ lam = 0) ∧
    (∀ p : Polynomial ℝ,
      IsEigenvector (Polynomial.derivative : Polynomial ℝ →ₗ[ℝ] Polynomial ℝ)
        0 p ↔ ∃ c : ℝ, c ≠ 0 ∧ p = Polynomial.C c) := by
  sorry

/-- 5A.10 {lit}`(Tp)(x) = x p′(x)` as an operator on {lit}`𝒫₄(ℝ)`
(here {lit}`degreeLT ℝ 5`). -/
noncomputable def T_ex_5A_10 :
    Polynomial.degreeLT ℝ 5 →ₗ[ℝ] Polynomial.degreeLT ℝ 5 where
  toFun p := ⟨Polynomial.X * Polynomial.derivative (p : Polynomial ℝ), by
    rw [Polynomial.mem_degreeLT]
    have hp := Polynomial.mem_degreeLT.mp p.2
    rcases eq_or_ne (Polynomial.derivative (p : Polynomial ℝ)) 0 with hd0 | hd0
    · rw [hd0, mul_zero, Polynomial.degree_zero]
      exact bot_lt_iff_ne_bot.mpr (by simp)
    · have hp0 : (p : Polynomial ℝ) ≠ 0 := fun h => hd0 (by simp [h])
      have hnd0 : (p : Polynomial ℝ).natDegree ≠ 0 := by
        intro h
        obtain ⟨a, ha⟩ := Polynomial.natDegree_eq_zero.mp h
        exact hd0 (by rw [← ha, Polynomial.derivative_C])
      rw [← Polynomial.natDegree_lt_iff_degree_lt
        (mul_ne_zero Polynomial.X_ne_zero hd0),
        Polynomial.natDegree_mul Polynomial.X_ne_zero hd0,
        Polynomial.natDegree_X]
      have h1 := Polynomial.natDegree_derivative_lt hnd0
      have h2 : (p : Polynomial ℝ).natDegree < 5 :=
        (Polynomial.natDegree_lt_iff_degree_lt hp0).mpr hp
      omega⟩
  map_add' p q := by
    ext
    simp [mul_add]
  map_smul' a p := by
    ext
    simp

theorem exercise_5A_10a : ∀ lam : ℝ, IsEigenvalue T_ex_5A_10 lam ↔
    lam = 0 ∨ lam = 1 ∨ lam = 2 ∨ lam = 3 ∨ lam = 4 := by
  sorry

theorem exercise_5A_10b (k : Fin 5) (p : Polynomial.degreeLT ℝ 5) :
    IsEigenvector T_ex_5A_10 (k : ℝ) p ↔
      ∃ c : ℝ, c ≠ 0 ∧ (p : Polynomial ℝ) =
        Polynomial.C c * Polynomial.X ^ (k : ℕ) := by
  sorry

/-- 5A.11 Eigenvalues are isolated: away from {lit}`α` (but close to it),
{lit}`T − λI` is invertible. Stated over {lit}`ℂ`. -/
theorem exercise_5A_11 {V : Type*} [AddCommGroup V] [Module ℂ V]
    [Finite ℂ V] (T : V →ₗ[ℂ] V) (α : ℂ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ lam : ℂ, 0 < ‖α - lam‖ → ‖α - lam‖ < δ →
      IsInvertible (T - lam • LinearMap.id) := by
  sorry

/-- 5A.12 {lit}`V = U ⊕ W` with {lit}`U, W` nonzero, and
{lit}`P(u + w) = u`: the eigenvalues of {lit}`P` are exactly {lit}`0` and
{lit}`1`… -/
theorem exercise_5A_12a (U W : Submodule F V) (hUW : IsCompl U W)
    (hU : U ≠ ⊥) (hW : W ≠ ⊥) (P : V →ₗ[F] V)
    (hP : ∀ u ∈ U, ∀ w ∈ W, P (u + w) = u) :
    ∀ lam : F, IsEigenvalue P lam ↔ lam = 0 ∨ lam = 1 := by
  sorry

/-- …with eigenvectors of {lit}`0` the nonzero vectors of {lit}`W` and
eigenvectors of {lit}`1` the nonzero vectors of {lit}`U`. -/
theorem exercise_5A_12b (U W : Submodule F V) (hUW : IsCompl U W)
    (P : V →ₗ[F] V) (hP : ∀ u ∈ U, ∀ w ∈ W, P (u + w) = u) (v : V) :
    (IsEigenvector P 0 v ↔ v ≠ 0 ∧ v ∈ W) ∧
    (IsEigenvector P 1 v ↔ v ≠ 0 ∧ v ∈ U) := by
  sorry

/-- 5A.13 (a) {lit}`T` and {lit}`S⁻¹TS` have the same eigenvalues. -/
theorem exercise_5A_13a (T S : V →ₗ[F] V) (hS : IsInvertible S) (lam : F) :
    IsEigenvalue T lam ↔ IsEigenvalue (hS.inv ∘ₗ T ∘ₗ S) lam := by
  sorry

/-- 5A.13 (b) The eigenvectors of {lit}`S⁻¹TS` are obtained from the
eigenvectors of {lit}`T` by applying {lit}`S⁻¹`: {lit}`v` is an eigenvector
of {lit}`S⁻¹TS` iff {lit}`Sv` is an eigenvector of {lit}`T`. -/
theorem exercise_5A_13b (T S : V →ₗ[F] V) (hS : IsInvertible S) (lam : F)
    (v : V) :
    IsEigenvector (hS.inv ∘ₗ T ∘ₗ S) lam v ↔ IsEigenvector T lam (S v) := by
  sorry

/-- 5A.14 -/
theorem exercise_5A_14 :
    ∃ T : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ), ∀ lam : ℝ, ¬ IsEigenvalue T lam := by
  sorry

/-- 5A.15 {lit}`λ` is an eigenvalue of {lit}`T` iff it is an eigenvalue of the
dual operator {lit}`T′ ∈ ℒ(V′)`. -/
theorem exercise_5A_15 [Finite F V] (T : V →ₗ[F] V) (lam : F) :
    IsEigenvalue T lam ↔ IsEigenvalue T.dualMap lam := by
  sorry

/-- 5A.16 An eigenvalue bound from any matrix of {lit}`T`:
{lit}`|λ| ≤ n max |𝒜(T)_{j,k}|`, stated with an arbitrary bound {lit}`M`
on the entries (over {lit}`ℂ`). -/
theorem exercise_5A_16 {V : Type*} [AddCommGroup V] [Module ℂ V]
    {n : ℕ} {v : Fin n → V} (hv : IsBasis ℂ v) (T : V →ₗ[ℂ] V) (lam : ℂ)
    (hlam : IsEigenvalue T lam) (M : ℝ)
    (hM : ∀ j k, ‖LADR.Section_3C.matrixOf hv hv T j k‖ ≤ M) :
    ‖lam‖ ≤ n * M := by
  sorry

open LADR.Section_1B (Complexification exercise_1B_8) in
open LADR.Section_3B (complexification_map) in
/-- 5A.17 For {lit}`F = ℝ`: {lit}`λ ∈ ℝ` is an eigenvalue of {lit}`T` iff it
is an eigenvalue of the complexification {lit}`T_ℂ`. -/
theorem exercise_5A_17 {V : Type*} [AddCommGroup V] [Module ℝ V]
    (T : V →ₗ[ℝ] V) (lam : ℝ) :
    letI : Module ℂ (Complexification V) := exercise_1B_8 V
    (IsEigenvalue T lam ↔
      IsEigenvalue (complexification_map T) (lam : ℂ)) := by
  sorry

open LADR.Section_1B (Complexification exercise_1B_8) in
open LADR.Section_3B (complexification_map) in
/-- 5A.18 For {lit}`F = ℝ` and {lit}`λ ∈ ℂ`: {lit}`λ` is an eigenvalue of
{lit}`T_ℂ` iff {lit}`λ̄` is an eigenvalue of {lit}`T_ℂ`. -/
theorem exercise_5A_18 {V : Type*} [AddCommGroup V] [Module ℝ V]
    (T : V →ₗ[ℝ] V) (lam : ℂ) :
    letI : Module ℂ (Complexification V) := exercise_1B_8 V
    (IsEigenvalue (complexification_map T) lam ↔
      IsEigenvalue (complexification_map T) (starRingEnd ℂ lam)) := by
  sorry

/-- 5A.19 The forward shift {lit}`T(z₁, z₂, …) = (0, z₁, z₂, …)` on
{lit}`F^∞` has no eigenvalues. -/
def forwardShift : (ℕ → F) →ₗ[F] (ℕ → F) where
  toFun x := fun i => match i with
    | 0 => 0
    | n + 1 => x n
  map_add' x y := by
    funext i
    cases i <;> simp
  map_smul' a x := by
    funext i
    cases i <;> simp

theorem exercise_5A_19 : ∀ lam : F, ¬ IsEigenvalue (forwardShift (F := F)) lam := by
  sorry

open LADR.Section_3A (backwardShift) in
/-- 5A.20 (a) Every {lit}`λ ∈ F` is an eigenvalue of the backward shift
{lit}`S(z₁, z₂, z₃, …) = (z₂, z₃, …)`. -/
theorem exercise_5A_20a : ∀ lam : F, IsEigenvalue (backwardShift (F := F)) lam := by
  sorry

open LADR.Section_3A (backwardShift) in
/-- 5A.20 (b) The eigenvectors of {lit}`λ` are the nonzero geometric
sequences {lit}`(c, cλ, cλ², …)`. -/
theorem exercise_5A_20b (lam : F) (x : ℕ → F) :
    IsEigenvector (backwardShift (F := F)) lam x ↔
      x ≠ 0 ∧ ∀ n, x n = x 0 * lam ^ n := by
  sorry

/-- 5A.21 (a) For invertible {lit}`T` and {lit}`λ ≠ 0`: {lit}`λ` is an
eigenvalue of {lit}`T` iff {lit}`1/λ` is an eigenvalue of {lit}`T⁻¹`. -/
theorem exercise_5A_21a (T : V →ₗ[F] V) (hT : IsInvertible T) (lam : F)
    (hlam : lam ≠ 0) :
    IsEigenvalue T lam ↔ IsEigenvalue hT.inv lam⁻¹ := by
  sorry

/-- 5A.21 (b) {lit}`T` and {lit}`T⁻¹` have the same eigenvectors. -/
theorem exercise_5A_21b (T : V →ₗ[F] V) (hT : IsInvertible T) (v : V) :
    (∃ lam, IsEigenvector T lam v) ↔ (∃ lam, IsEigenvector hT.inv lam v) := by
  sorry

/-- 5A.22 -/
theorem exercise_5A_22 (T : V →ₗ[F] V) (u w : V) (hu : u ≠ 0) (hw : w ≠ 0)
    (huw : T u = 3 • w) (hwu : T w = 3 • u) :
    IsEigenvalue T 3 ∨ IsEigenvalue T (-3) := by
  sorry

/-- 5A.23 -/
theorem exercise_5A_23 [Finite F V] (S T : V →ₗ[F] V) (lam : F) :
    IsEigenvalue (S ∘ₗ T) lam ↔ IsEigenvalue (T ∘ₗ S) lam := by
  sorry

open LADR.Section_3A (fromFnToFm) in
/-- 5A.24 (a) If every row of the {lit}`n`-by-{lit}`n` matrix {lit}`A` sums
to {lit}`1`, then {lit}`1` is an eigenvalue of {lit}`x ↦ Ax`. -/
theorem exercise_5A_24a {n : ℕ} (hn : 0 < n) (A : Fin n → Fin n → F)
    (h : ∀ j, ∑ k, A j k = 1) :
    IsEigenvalue (fromFnToFm A) 1 := by
  sorry

open LADR.Section_3A (fromFnToFm) in
/-- 5A.24 (b) If every column of {lit}`A` sums to {lit}`1`, then {lit}`1` is
an eigenvalue of {lit}`x ↦ Ax`. -/
theorem exercise_5A_24b {n : ℕ} (hn : 0 < n) (A : Fin n → Fin n → F)
    (h : ∀ k, ∑ j, A j k = 1) :
    IsEigenvalue (fromFnToFm A) 1 := by
  sorry

/-- 5A.25 -/
theorem exercise_5A_25 (T : V →ₗ[F] V) (u w : V) (a b : F)
    (hu : IsEigenvector T a u) (hw : IsEigenvector T b w)
    (huw : ∃ c, IsEigenvector T c (u + w)) : a = b := by
  sorry

/-- 5A.26 -/
theorem exercise_5A_26 (T : V →ₗ[F] V)
    (h : ∀ v : V, v ≠ 0 → ∃ lam : F, T v = lam • v) :
    ∃ c : F, T = c • LinearMap.id := by
  sorry

/-- 5A.27 -/
theorem exercise_5A_27 [Finite F V] (T : V →ₗ[F] V) (k : ℕ)
    (hk : 1 ≤ k) (hk' : k ≤ finrank F V - 1)
    (h : ∀ U : Submodule F V, finrank F U = k → InvariantUnder T U) :
    ∃ c : F, T = c • LinearMap.id := by
  sorry

/-- 5A.28 -/
theorem exercise_5A_28 [Finite F V] (T : V →ₗ[F] V) {m : ℕ}
    (lam : Fin m → F) (hlam : Function.Injective lam)
    (hev : ∀ k, IsEigenvalue T (lam k)) :
    m ≤ 1 + finrank F (range T) := by
  sorry

/-- 5A.29 -/
theorem exercise_5A_29 (T : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ))
    (h4 : IsEigenvalue T (-4)) (h5 : IsEigenvalue T 5)
    (h7 : IsEigenvalue T (Real.sqrt 7)) :
    ∃ x : Fin 3 → ℝ, T x - 9 • x = ![-4, 5, Real.sqrt 7] := by
  sorry

/-- 5A.30 -/
theorem exercise_5A_30 (T : V →ₗ[F] V)
    (h : (T - 2 • LinearMap.id) ∘ₗ (T - 3 • LinearMap.id) ∘ₗ
      (T - 4 • LinearMap.id) = 0)
    (lam : F) (hlam : IsEigenvalue T lam) :
    lam = 2 ∨ lam = 3 ∨ lam = 4 := by
  sorry

/-- 5A.31 -/
theorem exercise_5A_31 :
    ∃ T : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ), T ^ 4 = -LinearMap.id := by
  sorry

/-- 5A.32 -/
theorem exercise_5A_32 (T : V →ₗ[F] V)
    (h : ∀ lam : F, ¬ IsEigenvalue T lam) (h4 : T ^ 4 = LinearMap.id) :
    T ^ 2 = -LinearMap.id := by
  sorry

/-- 5A.33 (a) -/
theorem exercise_5A_33a (T : V →ₗ[F] V) (m : ℕ) (hm : 0 < m) :
    Function.Injective T ↔ Function.Injective (T ^ m) := by
  sorry

/-- 5A.33 (b) -/
theorem exercise_5A_33b (T : V →ₗ[F] V) (m : ℕ) (hm : 0 < m) :
    Function.Surjective T ↔ Function.Surjective (T ^ m) := by
  sorry

/-- 5A.34 -/
theorem exercise_5A_34 [Finite F V] {m : ℕ} (v : Fin m → V) :
    LinearIndependent F v ↔
      ∃ (T : V →ₗ[F] V) (lam : Fin m → F), Function.Injective lam ∧
        ∀ k, IsEigenvector T (lam k) (v k) := by
  sorry

/-- 5A.35 For distinct {lit}`λ₁, …, λₙ`, the functions {lit}`e^{λ₁x}, …,
e^{λₙx}` are linearly independent in the space of real-valued functions
on {lit}`ℝ`. -/
theorem exercise_5A_35 {n : ℕ} (lam : Fin n → ℝ)
    (hlam : Function.Injective lam) :
    LinearIndependent ℝ (fun k => fun x : ℝ => Real.exp (lam k * x)) := by
  sorry

/-- 5A.36 For distinct positive {lit}`λ₁, …, λₙ`, the functions
{lit}`cos(λ₁x), …, cos(λₙx)` are linearly independent. -/
theorem exercise_5A_36 {n : ℕ} (lam : Fin n → ℝ)
    (hlam : Function.Injective lam) (hpos : ∀ k, 0 < lam k) :
    LinearIndependent ℝ (fun k => fun x : ℝ => Real.cos (lam k * x)) := by
  sorry

/-- 5A.37 The operator {lit}`𝒜 ∈ ℒ(ℒ(V))` of left composition with
{lit}`T` ({lit}`𝒜(S) = TS`, mathlib's {name}`LinearMap.mulLeft`) has the same
eigenvalues as {lit}`T`. -/
theorem exercise_5A_37 [Finite F V] (T : V →ₗ[F] V) (lam : F) :
    IsEigenvalue (LinearMap.mulLeft F T : (V →ₗ[F] V) →ₗ[F] (V →ₗ[F] V)) lam ↔
      IsEigenvalue T lam := by
  sorry

/-- 5A.38 (a) The quotient operator {lit}`T/U ∈ ℒ(V/U)` defined by
{lit}`(T/U)(v + U) = Tv + U` when {lit}`U` is invariant under {lit}`T`.
The {lit}`sorry` is the well-definedness condition (which requires the
invariance of {lit}`U`); mathlib's {name}`Submodule.mapQ` then provides the
operator, satisfying {lit}`(T/U)(v + U) = Tv + U` by
{name}`Submodule.mapQ_apply`. -/
def exercise_5A_38_quotient_op (T : V →ₗ[F] V) (U : Submodule F V)
    (hU : InvariantUnder T U) : V ⧸ U →ₗ[F] V ⧸ U :=
  Submodule.mapQ U U T (by sorry)

-- The defining property, for use in later sections:
example (T : V →ₗ[F] V) (U : Submodule F V) (hU : InvariantUnder T U)
    (v : V) :
    exercise_5A_38_quotient_op T U hU (U.mkQ v) = U.mkQ (T v) := by
  simp [exercise_5A_38_quotient_op, Submodule.mapQ_apply]

/-- 5A.38 (b) Each eigenvalue of {lit}`T/U` is an eigenvalue of {lit}`T`. -/
theorem exercise_5A_38b [Finite F V] (T : V →ₗ[F] V) (U : Submodule F V)
    (hU : InvariantUnder T U) (lam : F)
    (h : IsEigenvalue (exercise_5A_38_quotient_op T U hU) lam) :
    IsEigenvalue T lam := by
  sorry

/-- 5A.39 -/
theorem exercise_5A_39 [Finite F V] (T : V →ₗ[F] V) :
    (∃ lam : F, IsEigenvalue T lam) ↔
      ∃ U : Submodule F V, InvariantUnder T U ∧
        finrank F U = finrank F V - 1 := by
  sorry

/-- 5A.40 -/
theorem exercise_5A_40 (S T : V →ₗ[F] V) (hS : IsInvertible S)
    (p : Polynomial F) :
    aeval (S ∘ₗ T ∘ₗ hS.inv) p = S ∘ₗ aeval T p ∘ₗ hS.inv := by
  sorry

/-- 5A.41 -/
theorem exercise_5A_41 (T : V →ₗ[F] V) (U : Submodule F V)
    (hU : InvariantUnder T U) (p : Polynomial F) :
    InvariantUnder (aeval T p) U := by
  sorry

/-- 5A.42 {lit}`T(x₁, …, xₙ) = (x₁, 2x₂, 3x₃, …, nxₙ)` on {lit}`ℝⁿ`.
(a) The eigenvalues are exactly {lit}`1, …, n`, with eigenvectors the nonzero
multiples of the standard basis vectors. -/
def T_ex_5A_42 (n : ℕ) : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) where
  toFun v := fun j => ((j : ℕ) + 1) * v j
  map_add' x y := by
    funext j
    simp [mul_add]
  map_smul' a x := by
    funext j
    simp
    ring

theorem exercise_5A_42a (n : ℕ) :
    (∀ lam : ℝ, IsEigenvalue (T_ex_5A_42 n) lam ↔
      ∃ j : Fin n, lam = (j : ℕ) + 1) ∧
    (∀ (j : Fin n) (v : Fin n → ℝ),
      IsEigenvector (T_ex_5A_42 n) ((j : ℕ) + 1) v ↔
        v ≠ 0 ∧ ∀ k, k ≠ j → v k = 0) := by
  sorry

/-- 5A.42 (b) The invariant subspaces of {lit}`T` are exactly the spans of
subsets of the standard basis vectors. -/
theorem exercise_5A_42b (n : ℕ) (U : Submodule ℝ (Fin n → ℝ)) :
    InvariantUnder (T_ex_5A_42 n) U ↔
      ∃ s : Finset (Fin n),
        U = Submodule.span ℝ
          ((fun j => (Pi.single j 1 : Fin n → ℝ)) '' s) := by
  sorry

/-- 5A.43 -/
theorem exercise_5A_43 [Finite F V] (hV : 1 < finrank F V)
    (T : V →ₗ[F] V) :
    ∃ S : V →ₗ[F] V, ∀ p : Polynomial F, aeval T p ≠ S := by
  sorry

end LADR.Section_5A
