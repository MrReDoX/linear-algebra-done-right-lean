import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Data.Complex.Basic
import Mathlib.Dynamics.Newton
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.JordanChevalley
import Mathlib.LinearAlgebra.Semisimple
import Mathlib.RingTheory.Adjoin.Polynomial
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Linter.Style
import LinearAlgebraDoneRightLean.Section_8A
import LinearAlgebraDoneRightLean.Section_8B
import CompanionHelper

/-!
# Axler, *Linear Algebra Done Right* (4e) — Section 8C: Consequences of Generalized Eigenspace Decomposition
-/

namespace LADR.Section_8C

open LADR.Section_5A (InvariantUnder)
open Module.End (HasEigenvalue maxGenEigenspace)
open LinearMap (ker range)
open Module (Finite finrank)
open Polynomial (aeval X C derivative)

variable {F : Type*} [Field F]
  {V : Type*} [AddCommGroup V] [Module F V]

/-! # Square Roots of Operators -/

/-! Recall (Axler 7.36) that a *square root* of an operator {lit}`T ∈ ℒ(V)` is an
operator {lit}`R ∈ ℒ(V)` with {lit}`R² = T`. Every complex number has a square
root, but not every operator on a complex vector space does — for example
{lit}`T(z₁, z₂, z₃) = (z₂, z₃, 0)` on {lit}`ℂ³` has none (Exercise 1). The
noninvertibility of that operator is no accident: we build square roots first for
{lit}`I + N` with {lit}`N` nilpotent (8.39), then for every invertible operator
over {lit}`ℂ` (8.41). -/

/-! The algebraic core of 8.39, isolated in a commutative ring. If {lit}`2` is a
unit and {lit}`a` is nilpotent, then {lit}`1 + a` is a square. Axler finds the
square root as a truncated Taylor series {lit}`1 + a₁a + a₂a² + ⋯` (see 8.40);
we instead obtain it from Newton's method / Hensel's lemma
({name}`Polynomial.existsUnique_nilpotent_sub_and_aeval_eq_zero`): the point
{lit}`1` is an approximate root of {lit}`X² − (1 + a)` (the value there is the
nilpotent {lit}`−a`) and the derivative {lit}`2` is a unit there, so Newton
iteration converges to an exact root. -/

theorem isSquare_one_add_of_isNilpotent {S : Type*} [CommRing S] (h2 : IsUnit (2 : S))
    {a : S} (ha : IsNilpotent a) : ∃ r : S, r ^ 2 = 1 + a := by
  set P : Polynomial S := X ^ 2 - C (1 + a) with hP
  have hval : aeval (1 : S) P = -a := by
    rw [hP]; simp only [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C,
      Algebra.algebraMap_self_apply, one_pow]; ring
  have hnil : IsNilpotent (aeval (1 : S) P) := by rw [hval]; exact ha.neg
  have hder : aeval (1 : S) (derivative P) = 2 := by
    rw [hP]; simp only [Polynomial.derivative_sub, Polynomial.derivative_C,
      Polynomial.derivative_X_pow, sub_zero, map_mul, map_pow, Polynomial.aeval_C,
      Polynomial.aeval_X, Algebra.algebraMap_self_apply]; norm_num
  have hunit : IsUnit (aeval (1 : S) (derivative P)) := by rw [hder]; exact h2
  obtain ⟨r, ⟨-, hr⟩, -⟩ :=
    Polynomial.existsUnique_nilpotent_sub_and_aeval_eq_zero hnil hunit
  refine ⟨r, ?_⟩
  have hexp : aeval r P = r ^ 2 - (1 + a) := by
    rw [hP]; simp only [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C,
      Algebra.algebraMap_self_apply]
  rw [hexp] at hr
  exact sub_eq_zero.mp hr

/-! 8.39 Identity plus nilpotent has a square root.

Suppose {lit}`T ∈ ℒ(V)` is nilpotent. Then {lit}`I + T` has a square root. This
holds over any field in which {lit}`2` is invertible (in particular over
{lit}`ℝ` and {lit}`ℂ`, matching Axler's statement for real and complex vector
spaces). We reduce to {name}`isSquare_one_add_of_isNilpotent` by working inside
the commutative subalgebra {lit}`𝔽[T] = Algebra.adjoin F {T}` (all its elements
are polynomials in {lit}`T`, hence commute), whose {lit}`CommRing` structure is
the mathlib instance {lit}`Polynomial.instCommRingAdjoinSingleton`. -/

theorem isSquare_one_add_of_isNilpotent_End (T : V →ₗ[F] V) (h2 : IsUnit (2 : F))
    (hT : IsNilpotent T) : ∃ R : V →ₗ[F] V, R ^ 2 = 1 + T := by
  have hmem : T ∈ Algebra.adjoin F {T} := Algebra.self_mem_adjoin_singleton F T
  let t : Algebra.adjoin F {T} := ⟨T, hmem⟩
  have hnil : IsNilpotent t := by
    obtain ⟨k, hk⟩ := hT
    refine ⟨k, ?_⟩
    apply Subtype.ext
    rw [ZeroMemClass.coe_zero, SubmonoidClass.coe_pow]
    exact hk
  have h2A : IsUnit (2 : Algebra.adjoin F {T}) := by
    have h := h2.map (algebraMap F (Algebra.adjoin F {T}))
    rwa [map_ofNat] at h
  obtain ⟨r, hr⟩ := isSquare_one_add_of_isNilpotent (a := t) h2A hnil
  refine ⟨(r : V →ₗ[F] V), ?_⟩
  have h := congrArg (Subalgebra.val (Algebra.adjoin F {T})) hr
  rw [map_pow, map_add, map_one, Subalgebra.val_apply, Subalgebra.val_apply] at h
  exact h

/-! 8.40 The Taylor series {lit}`√(1 + x) = 1 + a₁x + a₂x² + ⋯` used as
motivation for the construction in 8.39. It is a formal power-series identity
(the coefficients {lit}`a₁ = 1/2`, {lit}`a₂ = −1/8`, … are chosen so that the
square of the truncation matches {lit}`1 + x`); Axler explicitly does not prove
convergence and uses it only heuristically. It is not a theorem to formalize; our
proof of 8.39 above replaces it with Newton's method, which supplies the same
truncated-polynomial square root without reference to the series. -/

open DirectSum in
/-- Build an operator on `M` from operators on the summands of an internal direct
sum: the glued `g` acts as `f i` on each summand `A i`. -/
theorem glue_endo {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {ι : Type*}
    [DecidableEq ι] (A : ι → Submodule R M) (hA : DirectSum.IsInternal A)
    (f : ∀ i, A i →ₗ[R] A i) :
    ∃ g : M →ₗ[R] M, ∀ i (x : A i), g (x : M) = (f i x : M) := by
  set e : (⨁ i, A i) ≃ₗ[R] M := LinearEquiv.ofBijective (DirectSum.coeLinearMap A) hA with he
  set D : (⨁ i, A i) →ₗ[R] (⨁ i, A i) :=
    DirectSum.toModule R ι _ (fun i => (DirectSum.lof R ι (fun i => A i) i) ∘ₗ f i) with hD
  refine ⟨e.toLinearMap ∘ₗ D ∘ₗ e.symm.toLinearMap, fun i x => ?_⟩
  have hex : e.symm (x : M) = DirectSum.lof R ι (fun i => A i) i x := by
    apply e.injective
    rw [LinearEquiv.apply_symm_apply, he, LinearEquiv.ofBijective_apply,
      DirectSum.lof_eq_of, DirectSum.coeLinearMap_of]
  show e (D (e.symm (x : M))) = (f i x : M)
  rw [hex, hD, DirectSum.toModule_lof, LinearMap.comp_apply, he, LinearEquiv.ofBijective_apply,
    DirectSum.lof_eq_of, DirectSum.coeLinearMap_of]

open DirectSum in
/-- If on each summand of an internal direct sum `f i ∘ f i` agrees with `T`, then
gluing the `f i` produces a square root of `T`. -/
theorem exists_sqComp_of_forall_restrict {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] {ι : Type*} [DecidableEq ι] (A : ι → Submodule R M)
    (hA : DirectSum.IsInternal A) (T : M →ₗ[R] M) (f : ∀ i, A i →ₗ[R] A i)
    (hf : ∀ i (x : A i), (f i (f i x) : M) = T (x : M)) : ∃ R' : M →ₗ[R] M, R' ∘ₗ R' = T := by
  obtain ⟨g, hg⟩ := glue_endo A hA f
  refine ⟨g, ?_⟩
  set e : (⨁ i, A i) ≃ₗ[R] M := LinearEquiv.ofBijective (DirectSum.coeLinearMap A) hA with he
  have key : (g ∘ₗ g) ∘ₗ e.toLinearMap = T ∘ₗ e.toLinearMap := by
    refine DirectSum.linearMap_ext _ fun i => LinearMap.ext fun x => ?_
    have hei : e (DirectSum.lof R ι (fun i => A i) i x) = (x : M) := by
      rw [he, LinearEquiv.ofBijective_apply, DirectSum.lof_eq_of, DirectSum.coeLinearMap_of]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hei]
    rw [hg i x, hg i (f i x)]
    exact hf i x
  ext v
  obtain ⟨w, rfl⟩ := e.surjective v
  exact LinearMap.congr_fun key w

/-- 8.41 Over `ℂ`, every invertible operator has a square root. Following Axler:
by the generalized eigenspace decomposition `V = ⊕ G(λₖ, T)`, on each `G(λₖ, T)`
one has `T = λₖ(I + Nₖ/λₖ)` with `Nₖ` nilpotent (`λₖ ≠ 0` since `T` is invertible),
so `√λₖ · √(I + Nₖ/λₖ)` (the scalar root exists over `ℂ`, the operator root by 8.39)
squares to the restriction; gluing these along the direct sum gives a square root
of `T`. -/
theorem exists_sqComp_of_bijective {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (T : V →ₗ[ℂ] V) (hT : Function.Bijective T) :
    ∃ R : V →ₗ[ℂ] V, R ∘ₗ R = T := by
  classical
  have hmaps : ∀ μ : ℂ, Set.MapsTo (T : Module.End ℂ V)
      (maxGenEigenspace T μ) (maxGenEigenspace T μ) :=
    fun μ => Module.End.mapsTo_maxGenEigenspace_of_comm (Commute.refl _) μ
  have hper : ∀ μ : ℂ, ∃ fμ : (maxGenEigenspace T μ) →ₗ[ℂ] (maxGenEigenspace T μ),
      fμ ∘ₗ fμ = T.restrict (hmaps μ) := by
    intro μ
    by_cases hb : maxGenEigenspace T μ = ⊥
    · haveI : Subsingleton (maxGenEigenspace T μ) := by rw [hb]; infer_instance
      exact ⟨0, Subsingleton.elim _ _⟩
    · have hμ : μ ≠ 0 := by
        rintro rfl
        apply hb
        rw [Submodule.eq_bot_iff]
        intro x hx
        rw [Module.End.mem_maxGenEigenspace] at hx
        obtain ⟨k, hk⟩ := hx
        simp only [zero_smul, sub_zero] at hk
        have hTk : Function.Injective ⇑((T : Module.End ℂ V) ^ k) := by
          rw [Module.End.coe_pow]; exact hT.injective.iterate k
        exact hTk (by rw [hk, map_zero])
      set hN := Module.End.mapsTo_maxGenEigenspace_of_comm
        (Algebra.mul_sub_algebraMap_commutes (T : Module.End ℂ V) μ) μ with hNmaps
      set N : (maxGenEigenspace T μ) →ₗ[ℂ] (maxGenEigenspace T μ) :=
        ((T : Module.End ℂ V) - algebraMap ℂ (Module.End ℂ V) μ).restrict hN with hNval
      have hNnil : IsNilpotent N := LADR.Section_8B.isNilpotent_restrict_sub_algebraMap T μ
      obtain ⟨S, hS⟩ := isSquare_one_add_of_isNilpotent_End (μ⁻¹ • N)
        (isUnit_iff_ne_zero.mpr two_ne_zero) (hNnil.smul μ⁻¹)
      obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq μ (n := 2) (by norm_num)
      have hSc : S ∘ₗ S = 1 + μ⁻¹ • N := by rw [← Module.End.mul_eq_comp, ← pow_two]; exact hS
      have hTres : T.restrict (hmaps μ) = μ • 1 + N := by
        ext y
        simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply,
          Submodule.coe_add, Submodule.coe_smul, hNval, LinearMap.restrict_coe_apply,
          LinearMap.sub_apply, Module.algebraMap_end_apply]
        abel
      refine ⟨z • S, ?_⟩
      rw [hTres, LinearMap.smul_comp, LinearMap.comp_smul, smul_smul, ← pow_two, hz, hSc,
        smul_add, smul_smul, mul_inv_cancel₀ hμ, one_smul]
  choose f hf using hper
  refine exists_sqComp_of_forall_restrict (fun μ : ℂ => maxGenEigenspace T μ)
    (LADR.Section_8B.isInternal_maxGenEigenspace T) T f (fun μ x => ?_)
  rw [← LinearMap.comp_apply, hf μ, LinearMap.restrict_coe_apply]

/-! Axler's closing remark: by imitating the same technique (using {lit}`k`-th
roots of {lit}`I + Tₖ/λₖ` and of the scalars {lit}`λₖ`) one shows that over
{lit}`ℂ` every invertible operator has a {lit}`k`-th root for each positive
integer {lit}`k`. The nilpotent building block generalizes cleanly: for any
field with {lit}`k` invertible, {lit}`I + T` has a {lit}`k`-th root — this is a
{lit}`k`-th-root analogue of 8.39, provable by the same Newton argument with
{lit}`Xᵏ − (1 + a)`. -/

/-! # Jordan Form -/

/-! For every {lit}`T ∈ ℒ(V)` over {lit}`ℂ` there is a basis giving a "nice"
upper-triangular matrix (8.37); the Jordan form does better, producing a matrix
that is {lit}`0` except on the diagonal and the line directly above it. The
constructions and definitions in this subsection (8.44–8.46) are phrased entirely
in terms of the matrix {lit}`ℳ(T, basis)` of an operator with respect to a
basis, machinery that — as in the deferrals of 8.18(c) (Section 8A) and 8.31,
8.37 (Section 8B) — is not developed in these companion sections. We record the
two motivating nilpotent examples (8.42, 8.43), whose nilpotency we do prove, and
state the definition and theorems in prose with deferral notes. -/

/-! 8.42 Example: nilpotent operator with nice matrix.

{lit}`T(z₁, z₂, z₃, z₄) = (0, z₁, z₂, z₃)` on {lit}`ℂ⁴` satisfies {lit}`T⁴ = 0`,
so {lit}`T` is nilpotent. For {lit}`v = (1, 0, 0, 0)` the list
{lit}`T³v, T²v, Tv, v` is a basis (a single Jordan block); its matrix has
{lit}`1`'s on the superdiagonal and {lit}`0`'s elsewhere. We record the operator
and prove {lit}`T⁴ = 0`. -/

def T_8_42 : (Fin 4 → ℂ) →ₗ[ℂ] (Fin 4 → ℂ) where
  toFun v := ![0, v 0, v 1, v 2]
  map_add' x y := by funext i; fin_cases i <;> simp
  map_smul' a x := by funext i; fin_cases i <;> simp

theorem T_8_42_isNilpotent : IsNilpotent T_8_42 := by
  refine ⟨4, ?_⟩
  apply LinearMap.ext
  intro v
  funext i
  fin_cases i <;> simp [pow_succ, Module.End.mul_apply, T_8_42]

/-! 8.43 Example: nilpotent operator with a slightly more complicated matrix.

{lit}`T(z₁, …, z₆) = (0, z₁, z₂, 0, z₄, 0)` on {lit}`ℂ⁶` satisfies {lit}`T³ = 0`.
Unlike 8.42 there is no single vector {lit}`v` with {lit}`T⁵v, …, v` a basis;
instead {lit}`v₁ = e₁, v₂ = e₄, v₃ = e₆` give the Jordan basis
{lit}`T²v₁, Tv₁, v₁, Tv₂, v₂, v₃`, whose matrix is block diagonal with a
{lit}`3`-by-{lit}`3`, a {lit}`2`-by-{lit}`2`, and a {lit}`1`-by-{lit}`1` nilpotent
Jordan block. We record the operator and prove {lit}`T³ = 0`. -/

def T_8_43 : (Fin 6 → ℂ) →ₗ[ℂ] (Fin 6 → ℂ) where
  toFun v := ![0, v 0, v 1, 0, v 3, 0]
  map_add' x y := by funext i; fin_cases i <;> simp
  map_smul' a x := by funext i; fin_cases i <;> simp

theorem T_8_43_isNilpotent : IsNilpotent T_8_43 := by
  refine ⟨3, ?_⟩
  apply LinearMap.ext
  intro v
  funext i
  fin_cases i <;> simp [pow_succ, Module.End.mul_apply, T_8_43]

/-! 8.44 Definition: Jordan basis.

A basis of {lit}`V` is a *Jordan basis* for {lit}`T` if the matrix of {lit}`T`
with respect to it is block diagonal with each block {lit}`Aₖ` upper triangular,
having a single eigenvalue {lit}`λₖ` on its diagonal, {lit}`1`'s on the line
directly above the diagonal, and {lit}`0`'s elsewhere. As with the block-diagonal
definition 8.35, this is a statement about {lit}`ℳ(T, basis)`; the
matrix-of-a-basis correspondence is not developed here, so we describe it only in
prose. -/

/-! 8.45 Every nilpotent operator has a Jordan basis.

**Deferred.** If {lit}`T ∈ ℒ(V)` is nilpotent then {lit}`V` has a Jordan basis
for {lit}`T`. Axler's inductive proof constructs vectors {lit}`v₁, …, vₙ` with
{lit}`{Tʲvₖ}` a basis of {lit}`V`. The statement is intrinsically about the
matrix of {lit}`T` in the resulting basis (8.44), which is not formalized in this
companion; moreover mathlib does not provide a Jordan-normal-form theorem. So we
state 8.45 in prose rather than as an unproved numbered claim. The combinatorial
content is captured by Exercises 9 and 13 (stated below). -/

/-! 8.46 Jordan form.

**Deferred.** If {lit}`F = ℂ` and {lit}`T ∈ ℒ(V)`, then {lit}`V` has a Jordan
basis for {lit}`T`. Axler's proof applies 8.45 to each nilpotent
{lit}`(T − λₖI)|_{G(λₖ,T)}` and assembles the bases via the generalized
eigenspace decomposition. Both the base case 8.45 and the Jordan-basis notion
8.44 rest on the matrix-of-a-basis formalism absent here (and mathlib has no
Jordan-normal-form theorem), so 8.46 is deferred. -/

/-! The closest formally available analogue is the **Jordan–Chevalley–Dunford
decomposition**: over {lit}`ℂ` (indeed any perfect field) every operator on a
finite-dimensional space is a sum {lit}`T = N + S` of a nilpotent operator and a
semisimple operator, both polynomials in {lit}`T`. This is mathlib's
{name}`Module.End.exists_isNilpotent_isSemisimple`. Over {lit}`ℂ` "semisimple"
coincides with "diagonalizable", so this is the additive counterpart of the
Jordan form (each Jordan block splits as its diagonal part plus its nilpotent
superdiagonal part). We record it as a proved consequence. -/

theorem exists_isNilpotent_isSemisimple {V : Type*} [AddCommGroup V] [Module ℂ V]
    [Finite ℂ V] (T : V →ₗ[ℂ] V) :
    ∃ N S : V →ₗ[ℂ] V, IsNilpotent N ∧ Module.End.IsSemisimple S ∧ T = N + S := by
  obtain ⟨n, -, s, -, hn, hs, hT⟩ :=
    Module.End.exists_isNilpotent_isSemisimple (f := T)
  exact ⟨n, s, hn, hs, hT⟩

/-! # Exercises -/

/-- 8C.1 {lit}`T(z₁, z₂, z₃) = (z₂, z₃, 0)` on {lit}`ℂ³` has no square root. -/
def T_ex_8C_1 : (Fin 3 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ) where
  toFun v := ![v 1, v 2, 0]
  map_add' x y := by funext i; fin_cases i <;> simp
  map_smul' a x := by funext i; fin_cases i <;> simp

theorem exercise_8C_1 : ¬ ∃ R : (Fin 3 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ), R ^ 2 = T_ex_8C_1 := by
  sorry

/-- 8C.2 {lit}`T(x₁, …, x₅) = (2x₂, 3x₃, −x₄, 4x₅, 0)` on {lit}`F⁵`. -/
def T_ex_8C_2 (F : Type*) [Field F] : (Fin 5 → F) →ₗ[F] (Fin 5 → F) where
  toFun v := ![2 * v 1, 3 * v 2, - v 3, 4 * v 4, 0]
  map_add' x y := by funext i; fin_cases i <;> simp <;> ring
  map_smul' a x := by funext i; fin_cases i <;> simp <;> ring

/-- 8C.2 (a) {lit}`T` is nilpotent. -/
theorem exercise_8C_2a : IsNilpotent (T_ex_8C_2 F) := by
  sorry

/-- 8C.2 (b) {lit}`I + T` has a square root. -/
theorem exercise_8C_2b :
    ∃ R : (Fin 5 → F) →ₗ[F] (Fin 5 → F), R ^ 2 = 1 + T_ex_8C_2 F := by
  sorry

/-- 8C.3 Over {lit}`ℂ`, every invertible operator has a cube root. Invertibility
is encoded via a two-sided inverse {lit}`S`. -/
theorem exercise_8C_3 {V : Type*} [AddCommGroup V] [Module ℂ V] [Finite ℂ V]
    (T S : V →ₗ[ℂ] V) (hTS : T * S = 1) (hST : S * T = 1) :
    ∃ R : V →ₗ[ℂ] V, R ^ 3 = T := by
  sorry

/-- 8C.4 On a real vector space, {lit}`−I` has a square root iff {lit}`dim V` is
even. -/
theorem exercise_8C_4 {V : Type*} [AddCommGroup V] [Module ℝ V] [Finite ℝ V] :
    (∃ R : V →ₗ[ℝ] V, R ^ 2 = -1) ↔ Even (finrank ℝ V) := by
  sorry

/-- 8C.5 {lit}`T(w, z) = (−w − z, 9w + 5z)` on {lit}`ℂ²`. Its characteristic and
minimal polynomials are {lit}`(z − 2)²`, so {lit}`T` is a single {lit}`2`-by-{lit}`2`
Jordan block; a Jordan basis is any {lit}`v, (T − 2I)v` with {lit}`(T − 2I)v ≠ 0`.
We record the minimal-polynomial computation that pins down the Jordan structure. -/
def T_ex_8C_5 : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ) where
  toFun v := ![- v 0 - v 1, 9 * v 0 + 5 * v 1]
  map_add' x y := by funext i; fin_cases i <;> simp <;> ring
  map_smul' a x := by funext i; fin_cases i <;> simp <;> ring

theorem exercise_8C_5 : minpoly ℂ T_ex_8C_5 = (X - C 2) ^ 2 := by
  sorry

/-! Exercises 6–13 concern Jordan bases directly (finding one for the
differentiation operator on {lit}`𝒫₄(ℝ)`, describing the matrix of {lit}`T²` or
of {lit}`T` in a reversed Jordan basis, showing {lit}`n = dim null T`, etc.).
They are stated in terms of the matrix-of-a-basis / Jordan-basis formalism
deferred above (8.44), so we do not encode them here. -/

/-- 8C.14 Over {lit}`ℂ`, there is no decomposition of {lit}`V` into two nonzero
{lit}`T`-invariant subspaces iff the minimal polynomial of {lit}`T` is
{lit}`(z − λ)^{dim V}` for some {lit}`λ`. -/
theorem exercise_8C_14 {V : Type*} [AddCommGroup V] [Module ℂ V] [Finite ℂ V]
    (T : V →ₗ[ℂ] V) :
    (¬ ∃ U W : Submodule ℂ V, U ≠ ⊥ ∧ W ≠ ⊥ ∧
        InvariantUnder T U ∧ InvariantUnder T W ∧ IsCompl U W) ↔
      ∃ lam : ℂ, minpoly ℂ T = (X - C lam) ^ (finrank ℂ V) := by
  sorry

end LADR.Section_8C
