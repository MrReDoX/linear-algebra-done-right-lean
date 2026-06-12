import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Ring
import LinearAlgebraDoneRightLean.Section_2A
import LinearAlgebraDoneRightLean.Section_2B
import LinearAlgebraDoneRightLean.Section_3B
import LinearAlgebraDoneRightLean.Section_3C
import LinearAlgebraDoneRightLean.Section_3D
import LinearAlgebraDoneRightLean.Section_3E
import LinearAlgebraDoneRightLean.Chapter_4
import LinearAlgebraDoneRightLean.Section_5A
import CompanionHelper

/-!
# Axler, *Linear Algebra Done Right* (4e) — Section 5B: The Minimal Polynomial
-/

namespace LADR.Section_5B

open LADR.Section_2B (IsBasis)
open LADR.Section_3D (IsInvertible)
open LADR.Section_5A (InvariantUnder IsEigenvalue IsEigenvector
  isEigenvalue_iff_hasEigenvalue isEigenvector_iff_hasEigenvector
  tfae_isEigenvalue aeval_mul_eq_comp aeval_comp_comm aeval_comm_self
  ker_aeval_invariant range_aeval_invariant)
open LinearMap (ker range)
open Module (Finite finrank)
open Polynomial (aeval)

universe u

variable {F : Type*} [Field F]
  {V : Type*} [AddCommGroup V] [Module F V]

/-! Existence of Eigenvalues on Complex Vector Spaces -/

/-! 5.19 Existence of eigenvalues: every operator on a finite-dimensional
nonzero complex vector space has an eigenvalue.

Axler's proof: for {lit}`v ≠ 0` the list {lit}`v, Tv, T²v, …, Tⁿv` (with
{lit}`n = dim V`) is linearly dependent, so some nonzero polynomial {lit}`p`
satisfies {lit}`p(T)v = 0`. By the fundamental theorem of algebra {lit}`p`
has a root {lit}`λ`, so {lit}`p(z) = (z − λ)q(z)`; then
{lit}`0 = p(T)v = (T − λI)(q(T)v)`, and if {lit}`q(T)v ≠ 0` we are done while
otherwise we recurse on the smaller-degree polynomial {lit}`q`.
(mathlib's version is {name}`Module.End.exists_eigenvalue`.) -/

/-- Helper for 5.19: if some nonzero polynomial annihilates a nonzero vector,
then {lit}`T` has an eigenvalue. Induction on the degree, peeling off one
root at a time. -/
private lemma exists_eigenvalue_aux {V : Type*} [AddCommGroup V] [Module ℂ V]
    (T : V →ₗ[ℂ] V) :
    ∀ (n : ℕ) (p : Polynomial ℂ), p.natDegree = n → p ≠ 0 →
      ∀ v : V, v ≠ 0 → aeval T p v = 0 → ∃ lam : ℂ, IsEigenvalue T lam := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro p hdeg hp v hv hpv
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · -- A nonzero constant polynomial cannot annihilate {lit}`v ≠ 0`.
      exfalso
      subst h0
      have hC := Polynomial.eq_C_of_natDegree_eq_zero hdeg
      have hc0 : p.coeff 0 ≠ 0 := fun h => hp (by rw [hC, h, map_zero])
      rw [hC, Polynomial.aeval_C] at hpv
      have hsmul : p.coeff 0 • v = 0 := by
        rwa [Module.algebraMap_end_apply] at hpv
      rcases smul_eq_zero.mp hsmul with h | h
      · exact hc0 h
      · exact hv h
    · -- {lit}`p` has positive degree, so FTA provides a root {lit}`λ`.
      have hdegpos : 0 < p.degree :=
        Polynomial.natDegree_pos_iff_degree_pos.mp (hdeg ▸ hpos)
      obtain ⟨lam, hlam⟩ := Complex.exists_root hdegpos
      obtain ⟨q, hpq⟩ := Polynomial.dvd_iff_isRoot.mpr hlam
      have hq : q ≠ 0 := fun h => hp (by rw [hpq, h, mul_zero])
      have hqdeg : q.natDegree = n - 1 := by
        have hmul := Polynomial.natDegree_mul
          (Polynomial.X_sub_C_ne_zero lam) hq
        rw [← hpq, Polynomial.natDegree_X_sub_C, hdeg] at hmul
        omega
      by_cases hqv : aeval T q v = 0
      · exact ih (n - 1) (by omega) q hqdeg hq v hv hqv
      · -- {lit}`(T − λI)(q(T)v) = p(T)v = 0`, so {lit}`q(T)v` is an
        -- eigenvector for {lit}`λ`.
        refine ⟨lam, aeval T q v, hqv, ?_⟩
        rw [hpq, aeval_mul_eq_comp] at hpv
        have h2 : T (aeval T q v) - lam • aeval T q v = 0 := by
          have h3 : aeval T (Polynomial.X - Polynomial.C lam)
              (aeval T q v) = 0 := hpv
          rwa [map_sub, Polynomial.aeval_X, Polynomial.aeval_C,
            LinearMap.sub_apply, Module.algebraMap_end_apply] at h3
        rw [sub_eq_zero] at h2
        exact h2

theorem exists_eigenvalue {V : Type*} [AddCommGroup V] [Module ℂ V]
    [Finite ℂ V] [Nontrivial V] (T : V →ₗ[ℂ] V) :
    ∃ lam : ℂ, IsEigenvalue T lam := by
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  set n := finrank ℂ V with hn
  -- {lit}`v, Tv, …, Tⁿv` has length {lit}`n + 1`, hence is linearly
  -- dependent (2.22).
  have hdep : ¬ LinearIndependent ℂ (fun i : Fin (n + 1) => (T ^ (i : ℕ)) v) := by
    intro hli
    have hcard := hli.fintype_card_le_finrank
    rw [Fintype.card_fin, ← hn] at hcard
    omega
  obtain ⟨g, hsum, i₀, hi₀⟩ := Fintype.not_linearIndependent_iff.mp hdep
  -- Package the dependence as a nonzero polynomial with {lit}`p(T)v = 0`.
  set p : Polynomial ℂ := ∑ i : Fin (n + 1), Polynomial.monomial (i : ℕ) (g i)
    with hp_def
  have hp_coeff : ∀ j : Fin (n + 1), p.coeff (j : ℕ) = g j := by
    intro j
    rw [hp_def, Polynomial.finset_sum_coeff]
    rw [Finset.sum_eq_single j]
    · rw [Polynomial.coeff_monomial, if_pos rfl]
    · intro i _ hij
      rw [Polynomial.coeff_monomial, if_neg (fun h => hij (Fin.val_injective h))]
    · intro h
      exact absurd (Finset.mem_univ j) h
  have hp_ne : p ≠ 0 := fun h =>
    hi₀ (by rw [← hp_coeff i₀, h, Polynomial.coeff_zero])
  have hpv : aeval T p v = 0 := by
    rw [hp_def, map_sum, LinearMap.sum_apply, ← hsum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Polynomial.aeval_monomial, Module.End.mul_apply,
      Module.algebraMap_end_apply]
  exact exists_eigenvalue_aux T p.natDegree p rfl hp_ne v hv hpv

/-! 5.20 Example: on the infinite-dimensional space {lit}`𝒫(ℂ)`, the operator
{lit}`Tp = z·p` has no eigenvalues: multiplying by {lit}`z` raises the degree
of every nonzero polynomial, so {lit}`Tp` is never a scalar multiple of
{lit}`p`. -/

noncomputable def T_5_20 : Polynomial ℂ →ₗ[ℂ] Polynomial ℂ where
  toFun p := Polynomial.X * p
  map_add' p q := mul_add _ p q
  map_smul' a p := by
    simp only [RingHom.id_apply]
    exact mul_smul_comm a _ p

example : ∀ lam : ℂ, ¬ IsEigenvalue T_5_20 lam := by
  rintro lam ⟨p, hp, hXp⟩
  have hXp' : Polynomial.X * p = lam • p := by
    simpa [T_5_20] using hXp
  rcases eq_or_ne lam 0 with rfl | hlam
  · rw [zero_smul] at hXp'
    rcases mul_eq_zero.mp hXp' with h | h
    · exact Polynomial.X_ne_zero h
    · exact hp h
  · have hdeg := congrArg Polynomial.natDegree hXp'
    rw [Polynomial.natDegree_mul Polynomial.X_ne_zero hp,
      Polynomial.natDegree_X, Polynomial.smul_eq_C_mul,
      Polynomial.natDegree_C_mul hlam] at hdeg
    omega

/-! Eigenvalues and the Minimal Polynomial -/

/-! 5.21 Definition: monic polynomial — mathlib's {name}`Polynomial.Monic`
(highest-degree coefficient equals {lit}`1`). For example,
{lit}`2 + 9z² + z⁷` is monic. -/

example (p : Polynomial F) : p.Monic ↔ p.leadingCoeff = 1 := Iff.rfl

example : (Polynomial.X ^ 7 + Polynomial.C 9 * Polynomial.X ^ 2 +
    Polynomial.C 2 : Polynomial ℂ).Monic := by
  monicity!

/-! 5.22 Existence, uniqueness, and degree of minimal polynomial.

In mathlib the minimal polynomial of {lit}`T` is {name}`minpoly`
({lit}`minpoly F T`), available because a finite-dimensional {lit}`V` makes
every operator integral over {lit}`F`
({name}`Module.End.isIntegral`). Axler proves the degree bound
{lit}`deg p ≤ dim V` by an induction on dimension; here we obtain it from
the Cayley–Hamilton theorem (the minimal polynomial divides the
characteristic polynomial, which has degree {lit}`dim V`). -/

theorem exists_unique_minimal_polynomial [Finite F V] (T : V →ₗ[F] V) :
    ∃! p : Polynomial F, p.Monic ∧ aeval T p = 0 ∧
      ∀ q : Polynomial F, q.Monic → aeval T q = 0 → p.degree ≤ q.degree := by
  have hT : IsIntegral F T := Algebra.IsIntegral.isIntegral T
  refine ⟨minpoly F T,
    ⟨minpoly.monic hT, minpoly.aeval F T, fun q hq hq0 => minpoly.min F T hq hq0⟩,
    ?_⟩
  rintro p ⟨hmonic, haeval, hmin⟩
  exact minpoly.unique F T hmonic haeval hmin

theorem minpoly_natDegree_le [Finite F V] (T : V →ₗ[F] V) :
    (minpoly F T).natDegree ≤ finrank F V := by
  have h := minpoly.min (A := F) T T.charpoly_monic T.aeval_self_charpoly
  calc (minpoly F T).natDegree
      ≤ T.charpoly.natDegree := Polynomial.natDegree_le_natDegree h
    _ = finrank F V := T.charpoly_natDegree

/-! 5.24 Definition: minimal polynomial — mathlib's {name}`minpoly`. It is
monic, annihilates {lit}`T`, and has minimal degree among monic annihilating
polynomials. -/

noncomputable example [Finite F V] (T : V →ₗ[F] V) : Polynomial F :=
  minpoly F T

example [Finite F V] (T : V →ₗ[F] V) : (minpoly F T).Monic :=
  minpoly.monic (Algebra.IsIntegral.isIntegral T)

example [Finite F V] (T : V →ₗ[F] V) : aeval T (minpoly F T) = 0 :=
  minpoly.aeval F T

example [Finite F V] (T : V →ₗ[F] V) (q : Polynomial F) (hq : q.Monic)
    (hq0 : aeval T q = 0) : (minpoly F T).degree ≤ q.degree :=
  minpoly.min F T hq hq0

/-! 5.27 Eigenvalues are the zeros of the minimal polynomial.

(a) is mathlib's {name}`Module.End.hasEigenvalue_iff_isRoot`; we give Axler's
proof. -/

theorem isEigenvalue_iff_isRoot [Finite F V] (T : V →ₗ[F] V) (lam : F) :
    IsEigenvalue T lam ↔ (minpoly F T).IsRoot lam := by
  constructor
  · -- An eigenvalue is a zero: {lit}`0 = p(T)v = p(λ)v` and {lit}`v ≠ 0`.
    rintro ⟨v, hv, hTv⟩
    have hkey : aeval T (minpoly F T) v = (minpoly F T).eval lam • v :=
      Module.End.aeval_apply_of_hasEigenvector
        ((isEigenvector_iff_hasEigenvector T lam v).mp ⟨hv, hTv⟩)
    rw [minpoly.aeval, LinearMap.zero_apply] at hkey
    rcases smul_eq_zero.mp hkey.symm with h | h
    · exact h
    · exact absurd h hv
  · -- A zero is an eigenvalue: write {lit}`p(z) = (z − λ)q(z)`; minimality
    -- gives {lit}`q(T) ≠ 0`, and {lit}`(T − λI)(q(T)v) = p(T)v = 0`.
    intro hroot
    obtain ⟨q, hq⟩ := Polynomial.dvd_iff_isRoot.mpr hroot
    have hminne : minpoly F T ≠ 0 :=
      minpoly.ne_zero (Algebra.IsIntegral.isIntegral T)
    have hqne : q ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hq
      exact hminne hq
    have hqT : aeval T q ≠ 0 := by
      intro h0
      have hdvd := minpoly.dvd F T h0
      have hle := Polynomial.natDegree_le_of_dvd hdvd hqne
      have hmul := Polynomial.natDegree_mul
        (Polynomial.X_sub_C_ne_zero lam) hqne
      rw [← hq, Polynomial.natDegree_X_sub_C] at hmul
      omega
    obtain ⟨v, hv⟩ : ∃ v, aeval T q v ≠ 0 := by
      by_contra h
      push Not at h
      exact hqT (LinearMap.ext fun v => by rw [h v, LinearMap.zero_apply])
    refine ⟨aeval T q v, hv, ?_⟩
    have h1 : aeval T (minpoly F T) v = 0 := by
      rw [minpoly.aeval, LinearMap.zero_apply]
    rw [hq, aeval_mul_eq_comp, LinearMap.comp_apply] at h1
    have h2 : T (aeval T q v) - lam • aeval T q v = 0 := by
      rwa [map_sub, Polynomial.aeval_X, Polynomial.aeval_C,
        LinearMap.sub_apply, Module.algebraMap_end_apply] at h1
    rw [sub_eq_zero] at h2
    exact h2

/-- 5.27 (b) On a complex vector space the minimal polynomial factors as
{lit}`(z − λ₁)⋯(z − λₘ)` where {lit}`λ₁, …, λₘ` are exactly the eigenvalues
of {lit}`T` (with possible repetitions), encoded via the multiset of roots. -/
theorem minpoly_eq_prod_roots {V : Type*} [AddCommGroup V] [Module ℂ V]
    [Finite ℂ V] (T : V →ₗ[ℂ] V) :
    minpoly ℂ T = (Multiset.map (fun a => Polynomial.X - Polynomial.C a)
        (minpoly ℂ T).roots).prod ∧
      ∀ lam : ℂ, lam ∈ (minpoly ℂ T).roots ↔ IsEigenvalue T lam := by
  have hmonic : (minpoly ℂ T).Monic :=
    minpoly.monic (Algebra.IsIntegral.isIntegral T)
  constructor
  · have h := Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C
      (p := minpoly ℂ T)
      (Polynomial.splits_iff_card_roots.mp (IsAlgClosed.splits _))
    rw [hmonic.leadingCoeff, Polynomial.C_1, one_mul] at h
    exact h.symm
  · intro lam
    rw [Polynomial.mem_roots hmonic.ne_zero, isEigenvalue_iff_isRoot]

/-! 5.29 {lit}`q(T) = 0` iff {lit}`q` is a polynomial multiple of the minimal
polynomial. Axler's proof uses the division algorithm (4.9); mathlib's
version of the forward direction is {name}`minpoly.dvd`. -/

theorem aeval_eq_zero_iff_minpoly_dvd [Finite F V] (T : V →ₗ[F] V)
    (q : Polynomial F) : aeval T q = 0 ↔ minpoly F T ∣ q := by
  constructor
  · intro hq
    have hp_ne : minpoly F T ≠ 0 :=
      minpoly.ne_zero (Algebra.IsIntegral.isIntegral T)
    -- Division algorithm: {lit}`q = ps + r` with {lit}`deg r < deg p`.
    obtain ⟨⟨s, r⟩, ⟨hqe, hdeg⟩, -⟩ :=
      LADR.Chapter_4.division_algorithm q (minpoly F T) hp_ne
    -- {lit}`r(T) = q(T) − p(T)s(T) = 0`.
    have hr : aeval T r = 0 := by
      have h := congrArg (aeval T) hqe
      rwa [map_add, map_mul, minpoly.aeval, zero_mul, zero_add, hq, eq_comm]
        at h
    -- If {lit}`r ≠ 0` then dividing by its leading coefficient gives a monic
    -- annihilator of smaller degree than the minimal polynomial.
    rcases eq_or_ne r 0 with rfl | hr0
    · exact ⟨s, by rw [hqe, add_zero]⟩
    · exfalso
      have hmonic : (r * Polynomial.C r.leadingCoeff⁻¹).Monic :=
        Polynomial.monic_mul_leadingCoeff_inv hr0
      have haev : aeval T (r * Polynomial.C r.leadingCoeff⁻¹) = 0 := by
        rw [map_mul, hr, zero_mul]
      have hge := minpoly.min F T hmonic haev
      rw [Polynomial.degree_mul_leadingCoeff_inv r hr0] at hge
      exact absurd hdeg (not_lt.mpr hge)
  · rintro ⟨s, rfl⟩
    rw [map_mul, minpoly.aeval, zero_mul]

/-! Restriction of an operator to an invariant subspace, and powers and
polynomials of the restriction. -/

theorem restrict_pow_coe {T : V →ₗ[F] V} {U : Submodule F V}
    (h : InvariantUnder T U) (n : ℕ) (u : U) :
    (((h.restrict ^ n) u : U) : V) = (T ^ n) (u : V) := by
  induction n generalizing u with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, Module.End.mul_apply, pow_succ, Module.End.mul_apply,
      ih (h.restrict u)]
    congr 1

theorem aeval_restrict_coe {T : V →ₗ[F] V} {U : Submodule F V}
    (h : InvariantUnder T U) (p : Polynomial F) (u : U) :
    (((aeval h.restrict p) u : U) : V) = aeval T p (u : V) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply,
      Submodule.coe_add, hp, hq]
  | monomial n a =>
    rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial,
      Module.End.mul_apply, Module.End.mul_apply,
      Module.algebraMap_end_apply, Module.algebraMap_end_apply,
      Submodule.coe_smul, restrict_pow_coe h n u]

/-! 5.31 The minimal polynomial of {lit}`T` is a polynomial multiple of the
minimal polynomial of the restriction {lit}`T|_U` to an invariant
subspace. -/

theorem minpoly_restrict_dvd [Finite F V] (T : V →ₗ[F] V) (U : Submodule F V)
    (hU : InvariantUnder T U) : minpoly F hU.restrict ∣ minpoly F T := by
  -- {lit}`p(T|_U) = 0` because {lit}`p(T)u = 0` for every {lit}`u ∈ U`,
  -- then apply 5.29 to {lit}`T|_U`.
  rw [← aeval_eq_zero_iff_minpoly_dvd]
  apply LinearMap.ext
  intro u
  apply Subtype.ext
  rw [LinearMap.zero_apply, aeval_restrict_coe hU (minpoly F T) u,
    LinearMap.congr_fun (minpoly.aeval F T) (u : V)]
  simp

/-! 5.32 {lit}`T` is not invertible iff the constant term of its minimal
polynomial is {lit}`0`. -/

theorem not_invertible_iff_minpoly_coeff_zero [Finite F V] (T : V →ₗ[F] V) :
    ¬ IsInvertible T ↔ (minpoly F T).coeff 0 = 0 := by
  -- {lit}`T` not invertible ⟺ {lit}`0` eigenvalue (5.7)
  -- ⟺ {lit}`0` zero of {lit}`p` (5.27) ⟺ constant term {lit}`0`.
  have h0 : T - (0 : F) • (LinearMap.id : V →ₗ[F] V) = T := by
    rw [zero_smul, sub_zero]
  have h2 := (tfae_isEigenvalue T 0).out 0 3
  rw [h0] at h2
  rw [← h2, isEigenvalue_iff_isRoot, Polynomial.IsRoot.def,
    Polynomial.coeff_zero_eq_eval_zero]

/-! Eigenvalues on Odd-Dimensional Real Vector Spaces -/

/-- The quotient operator {lit}`T/U` on {lit}`V/U`, for {lit}`U` invariant
under {lit}`T` (mathlib's {name}`Submodule.mapQ`). The reader meets this
operator in Exercise 5A.38; here we need it (with proofs) for 5.33. -/
def quotOp (T : V →ₗ[F] V) (U : Submodule F V) (hU : InvariantUnder T U) :
    V ⧸ U →ₗ[F] V ⧸ U :=
  Submodule.mapQ U U T hU

theorem quotOp_mkQ (T : V →ₗ[F] V) {U : Submodule F V}
    (hU : InvariantUnder T U) (v : V) :
    quotOp T U hU (U.mkQ v) = U.mkQ (T v) := by
  simp [quotOp, Submodule.mapQ_apply]

theorem quotOp_pow_mkQ (T : V →ₗ[F] V) {U : Submodule F V}
    (hU : InvariantUnder T U) (n : ℕ) (v : V) :
    ((quotOp T U hU) ^ n) (U.mkQ v) = U.mkQ ((T ^ n) v) := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, Module.End.mul_apply, quotOp_mkQ, ih (T v), pow_succ,
      Module.End.mul_apply]

theorem aeval_quotOp_mkQ (T : V →ₗ[F] V) {U : Submodule F V}
    (hU : InvariantUnder T U) (p : Polynomial F) (v : V) :
    aeval (quotOp T U hU) p (U.mkQ v) = U.mkQ (aeval T p v) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, map_add, LinearMap.add_apply, hp, hq, LinearMap.add_apply,
      map_add]
  | monomial n a =>
    rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial,
      Module.End.mul_apply, Module.End.mul_apply,
      Module.algebraMap_end_apply, Module.algebraMap_end_apply,
      quotOp_pow_mkQ, map_smul]

/-! 5.33 Even-dimensional null space: if {lit}`F = ℝ` and {lit}`b² < 4c`,
then {lit}`null(T² + bT + cI)` has even dimension.

The proof here is by induction: an operator {lit}`S` satisfying
{lit}`S² + bS + cI = 0` has no (real) eigenvalues, so for {lit}`w ≠ 0` the
subspace {lit}`U = span(w, Sw)` is two-dimensional and invariant; the
quotient operator {lit}`S/U` satisfies the same quadratic, and induction on
dimension finishes. (Axler instead takes {lit}`U` maximal even-dimensional
invariant.) -/

private lemma no_eigenvalue_of_quadratic {W : Type u} [AddCommGroup W]
    [Module ℝ W] {b c : ℝ} (hbc : b ^ 2 < 4 * c) (S : W →ₗ[ℝ] W)
    (hS : aeval S (Polynomial.X ^ 2 + Polynomial.C b * Polynomial.X +
      Polynomial.C c) = 0)
    (lam : ℝ) (v : W) (hv : v ≠ 0) : S v ≠ lam • v := by
  intro heq
  have hev : Module.End.HasEigenvector S lam v :=
    ⟨Module.End.mem_eigenspace_iff.mpr heq, hv⟩
  have h1 := Module.End.aeval_apply_of_hasEigenvector
    (p := Polynomial.X ^ 2 + Polynomial.C b * Polynomial.X +
      Polynomial.C c) hev
  rw [hS, LinearMap.zero_apply] at h1
  have heval : (lam ^ 2 + b * lam + c) • v = 0 := by
    have : (Polynomial.X ^ 2 + Polynomial.C b * Polynomial.X +
        Polynomial.C c).eval lam = lam ^ 2 + b * lam + c := by
      simp
    rw [← this]
    exact h1.symm
  rcases smul_eq_zero.mp heval with h | h
  · nlinarith [sq_nonneg (lam + b / 2)]
  · exact hv h

private lemma even_finrank_of_quadratic_aux {b c : ℝ} (hbc : b ^ 2 < 4 * c) :
    ∀ (n : ℕ) (W : Type u) (_ : AddCommGroup W),
      ∀ (_ : Module ℝ W) (_ : Module.Finite ℝ W), finrank ℝ W = n →
      ∀ S : W →ₗ[ℝ] W,
        aeval S (Polynomial.X ^ 2 + Polynomial.C b * Polynomial.X +
          Polynomial.C c) = 0 →
        Even n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro W _ _ _ hW S hS
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · simp [h0]
    · have : Nontrivial W := by
        apply Module.nontrivial_of_finrank_pos (R := ℝ)
        omega
      obtain ⟨w, hw⟩ := exists_ne (0 : W)
      -- {lit}`U = span(w, Sw)` is two-dimensional…
      set U : Submodule ℝ W := Submodule.span ℝ {w, S w} with hU_def
      have hw_mem : w ∈ U := Submodule.subset_span (by simp)
      have hSw_mem : S w ∈ U := Submodule.subset_span (by simp)
      -- {lit}`S²w = −b·Sw − c·w` from the quadratic relation.
      have hS2 : S (S w) = -(b • S w) - c • w := by
        have h1 := LinearMap.congr_fun hS w
        simp only [map_add, map_mul, Polynomial.aeval_X,
          Polynomial.aeval_C, LinearMap.add_apply, Module.End.mul_apply,
          Module.algebraMap_end_apply, LinearMap.zero_apply, pow_two] at h1
        have h2 : S (S w) + (b • S w + c • w) = 0 := by
          rw [← add_assoc]
          exact h1
        rw [add_eq_zero_iff_eq_neg] at h2
        rw [h2]
        abel
      -- …invariant under {lit}`S`…
      have hU_inv : InvariantUnder S U := by
        intro u hu
        rw [hU_def, Submodule.mem_span_pair] at hu ⊢
        obtain ⟨s, t, rfl⟩ := hu
        refine ⟨-(t * c), s - t * b, ?_⟩
        rw [map_add, map_smul, map_smul, hS2]
        module
      -- …of dimension exactly {lit}`2` because {lit}`S` has no eigenvalues.
      have hli : LinearIndependent ℝ ![w, S w] := by
        rw [LinearIndependent.pair_iff]
        intro s t hst
        by_cases ht : t = 0
        · subst ht
          rw [zero_smul, add_zero] at hst
          rcases smul_eq_zero.mp hst with h | h
          · exact ⟨h, rfl⟩
          · exact absurd h hw
        · exfalso
          have hSw : S w = (-(t⁻¹ * s)) • w := by
            have h1 : t • S w = -(s • w) := by
              rw [eq_neg_iff_add_eq_zero, add_comm]
              exact hst
            have h2 := congrArg (fun x => t⁻¹ • x) h1
            simp only [smul_smul, inv_mul_cancel₀ ht, one_smul, smul_neg]
              at h2
            rw [← neg_smul] at h2
            exact h2
          exact no_eigenvalue_of_quadratic hbc S hS (-(t⁻¹ * s)) w hw hSw
      have hU_rank : finrank ℝ U = 2 := by
        have hrange : Set.range ![w, S w] = ({w, S w} : Set W) := by
          ext x
          constructor
          · rintro ⟨i, rfl⟩
            fin_cases i <;> simp
          · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
            rintro (rfl | rfl)
            · exact ⟨0, rfl⟩
            · exact ⟨1, rfl⟩
        rw [hU_def, ← hrange, finrank_span_eq_card hli, Fintype.card_fin]
      -- The quotient operator satisfies the same quadratic…
      have hquot : aeval (quotOp S U hU_inv)
          (Polynomial.X ^ 2 + Polynomial.C b * Polynomial.X +
            Polynomial.C c) = 0 := by
        apply LinearMap.ext
        intro x
        obtain ⟨v, rfl⟩ := U.mkQ_surjective x
        rw [aeval_quotOp_mkQ, LinearMap.congr_fun hS v,
          LinearMap.zero_apply, map_zero, LinearMap.zero_apply]
      -- …on a space of dimension {lit}`n − 2`; induction gives evenness.
      have hquot_rank : finrank ℝ (W ⧸ U) = n - 2 := by
        rw [LADR.Section_3E.finrank_quotient U, hW, hU_rank]
      have h2n : 2 ≤ n := by
        rw [← hW, ← hU_rank]
        exact Submodule.finrank_le U
      have heven := ih (n - 2) (by omega) (W ⧸ U) inferInstance
        inferInstance inferInstance hquot_rank (quotOp S U hU_inv) hquot
      obtain ⟨k, hk⟩ := heven
      exact ⟨k + 1, by omega⟩

theorem even_finrank_ker_quadratic {V : Type u} [AddCommGroup V] [Module ℝ V]
    [Finite ℝ V] (T : V →ₗ[ℝ] V) {b c : ℝ} (hbc : b ^ 2 < 4 * c) :
    Even (finrank ℝ (ker (aeval T (Polynomial.X ^ 2 +
      Polynomial.C b * Polynomial.X + Polynomial.C c)))) := by
  -- The null space is invariant under {lit}`T` (5.18); the restriction of
  -- {lit}`T` to it satisfies the quadratic relation, so the helper applies.
  set q : Polynomial ℝ := Polynomial.X ^ 2 + Polynomial.C b * Polynomial.X +
    Polynomial.C c with hq_def
  have hinv : InvariantUnder T (ker (aeval T q)) := ker_aeval_invariant T q
  have hrestrict : aeval hinv.restrict q = 0 := by
    apply LinearMap.ext
    intro u
    apply Subtype.ext
    rw [LinearMap.zero_apply, aeval_restrict_coe hinv q u]
    have hu := u.2
    rw [LinearMap.mem_ker] at hu
    rw [hu]
    rfl
  exact even_finrank_of_quadratic_aux hbc _ (ker (aeval T q)) inferInstance
    inferInstance inferInstance rfl hinv.restrict hrestrict

/-! 5.34 Every operator on an odd-dimensional real vector space has an
eigenvalue.

Axler's proof: if the minimal polynomial {lit}`p` had no real zero, then by
4.16 it would be a product of quadratics with negative discriminant; peeling
off one quadratic factor {lit}`x² + bx + c`, minimality forces
{lit}`range(T² + bT + cI) ≠ V`; this range is invariant under {lit}`T`,
and by 5.33 plus the fundamental theorem of linear maps it has odd dimension
smaller than {lit}`dim V` — so induction applies, and the resulting
eigenvalue of the restriction is an eigenvalue of {lit}`T`, contradicting
the assumption that {lit}`p` has no real zero. -/

private lemma exists_eigenvalue_of_odd_aux :
    ∀ (n : ℕ), Odd n → ∀ (W : Type u) (_ : AddCommGroup W),
      ∀ (_ : Module ℝ W) (_ : Module.Finite ℝ W), finrank ℝ W = n →
      ∀ T : W →ₗ[ℝ] W, ∃ lam : ℝ, IsEigenvalue T lam := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hodd W _ _ _ hW T
    by_cases hroot : ∃ lam : ℝ, (minpoly ℝ T).IsRoot lam
    · obtain ⟨lam, hlam⟩ := hroot
      exact ⟨lam, (isEigenvalue_iff_isRoot T lam).mpr hlam⟩
    · exfalso
      push Not at hroot
      have hn_pos : 0 < n := hodd.pos
      have hW_nontrivial : Nontrivial W := by
        apply Module.nontrivial_of_finrank_pos (R := ℝ)
        omega
      set p : Polynomial ℝ := minpoly ℝ T with hp_def
      have hp_ne : p ≠ 0 := minpoly.ne_zero (Algebra.IsIntegral.isIntegral T)
      have hp_deg_pos : 0 < p.natDegree :=
        minpoly.natDegree_pos (Algebra.IsIntegral.isIntegral T)
      -- 4.16: {lit}`p` factors into linear and quadratic factors; since
      -- {lit}`p` has no real zero there are no linear factors.
      obtain ⟨c, m, M, lams, bs, cs, hdisc, hfact⟩ :=
        LADR.Chapter_4.real_polynomial_factorization p hp_ne
      have hm : m = 0 := by
        by_contra hm0
        have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
        apply hroot (lams ⟨0, hmpos⟩)
        rw [Polynomial.IsRoot.def, hfact]
        rw [Polynomial.eval_mul, Polynomial.eval_mul]
        have : Polynomial.eval (lams ⟨0, hmpos⟩)
            (∏ k, (Polynomial.X - Polynomial.C (lams k))) = 0 := by
          rw [Polynomial.eval_prod]
          exact Finset.prod_eq_zero (Finset.mem_univ ⟨0, hmpos⟩) (by simp)
        rw [this, mul_zero, zero_mul]
      subst hm
      -- {lit}`p = C c · ∏ quadratics`, and {lit}`M ≥ 1` since {lit}`p` is
      -- nonconstant.
      rw [show (∏ k : Fin 0, (Polynomial.X - Polynomial.C (lams k))) = 1 from
        Finset.prod_of_isEmpty _, mul_one] at hfact
      have hM : 0 < M := by
        by_contra hM0
        have : M = 0 := by omega
        subst this
        rw [show (∏ k : Fin 0, (Polynomial.X ^ 2 +
          Polynomial.C (bs k) * Polynomial.X + Polynomial.C (cs k))) = 1 from
          Finset.prod_of_isEmpty _, mul_one] at hfact
        rw [hfact, Polynomial.natDegree_C] at hp_deg_pos
        omega
      -- Peel off the quadratic factor {lit}`q = x² + b₀x + c₀`.
      set k0 : Fin M := ⟨0, hM⟩
      set q : Polynomial ℝ := Polynomial.X ^ 2 +
        Polynomial.C (bs k0) * Polynomial.X + Polynomial.C (cs k0) with hq_def
      have hq_deg : q.natDegree = 2 := by
        rw [hq_def]
        compute_degree!
      have hq_ne : q ≠ 0 := fun h => by
        rw [h, Polynomial.natDegree_zero] at hq_deg
        omega
      obtain ⟨s, hps⟩ : q ∣ p := by
        rw [hfact]
        exact Dvd.dvd.mul_left
          (Finset.dvd_prod_of_mem _ (Finset.mem_univ k0)) _
      have hs_ne : s ≠ 0 := fun h => hp_ne (by rw [hps, h, mul_zero])
      have hs_deg : s.natDegree = p.natDegree - 2 := by
        have := Polynomial.natDegree_mul hq_ne hs_ne
        rw [← hps, hq_deg] at this
        omega
      -- {lit}`U = range q(T)` is a proper invariant subspace…
      set U : Submodule ℝ W := range (aeval T q) with hU_def
      have hU_inv : InvariantUnder T U := range_aeval_invariant T q
      have hU_ne_top : U ≠ ⊤ := by
        intro htop
        -- otherwise {lit}`s(T) = 0`, contradicting minimality of {lit}`p`.
        have hsT : aeval T s = 0 := by
          apply LinearMap.ext
          intro w
          have hw : w ∈ U := by rw [htop]; exact Submodule.mem_top
          obtain ⟨v, hv⟩ := LinearMap.mem_range.mp hw
          rw [LinearMap.zero_apply, ← hv, ← LinearMap.comp_apply,
            ← aeval_mul_eq_comp, mul_comm s q, ← hps, hp_def,
            minpoly.aeval, LinearMap.zero_apply]
        have hdvd := minpoly.dvd ℝ T hsT
        have hle := Polynomial.natDegree_le_of_dvd hdvd hs_ne
        rw [← hp_def] at hle
        omega
      -- …of odd dimension (5.33 + fundamental theorem of linear maps).
      have hker_even : Even (finrank ℝ (ker (aeval T q))) := by
        rw [hq_def]
        exact even_finrank_ker_quadratic T (by have := hdisc k0; nlinarith)
      have hrank_sum := LADR.Section_3B.finrank_ker_add_finrank_range
        (aeval T q)
      have hU_lt : finrank ℝ U < n := by
        rw [← hW]
        exact Submodule.finrank_lt hU_ne_top
      have hU_odd : Odd (finrank ℝ U) := by
        obtain ⟨j, hj⟩ := hker_even
        obtain ⟨i, hi⟩ := hodd
        rw [← hU_def] at hrank_sum
        rw [hW] at hrank_sum
        exact ⟨i - j, by omega⟩
      -- Induction: {lit}`T|_U` has an eigenvalue, which lifts to {lit}`T`
      -- and is then a real zero of {lit}`p` — contradiction.
      obtain ⟨lam, u, hu_ne, hu_eq⟩ := ih (finrank ℝ U) hU_lt hU_odd U
        inferInstance inferInstance inferInstance rfl hU_inv.restrict
      have hTlam : IsEigenvalue T lam := by
        refine ⟨(u : W), fun h => hu_ne (Subtype.ext h), ?_⟩
        have := congrArg (Subtype.val) hu_eq
        rwa [Submodule.coe_smul] at this
      exact hroot lam ((isEigenvalue_iff_isRoot T lam).mp hTlam)

theorem exists_eigenvalue_of_odd_finrank {V : Type u} [AddCommGroup V]
    [Module ℝ V] [Finite ℝ V] (hodd : Odd (finrank ℝ V)) (T : V →ₗ[ℝ] V) :
    ∃ lam : ℝ, IsEigenvalue T lam :=
  exists_eigenvalue_of_odd_aux (finrank ℝ V) hodd V inferInstance
    inferInstance inferInstance rfl T

/-! # Exercises -/

/-- 5B.1 -/
theorem exercise_5B_1 (T : V →ₗ[F] V) :
    IsEigenvalue (T ^ 2) 9 ↔ IsEigenvalue T 3 ∨ IsEigenvalue T (-3) := by
  sorry

/-- 5B.2 -/
theorem exercise_5B_2 {V : Type*} [AddCommGroup V] [Module ℂ V]
    (T : V →ₗ[ℂ] V) (h : ∀ lam : ℂ, ¬ IsEigenvalue T lam)
    (U : Submodule ℂ V) (hU : InvariantUnder T U) :
    U = ⊥ ∨ ¬ Module.Finite ℂ U := by
  sorry

/-- 5B.3 {lit}`T(x₁, …, xₙ) = (x₁ + ⋯ + xₙ, …, x₁ + ⋯ + xₙ)`. -/
def T_ex_5B_3 (n : ℕ) : (Fin n → F) →ₗ[F] (Fin n → F) where
  toFun x := fun _ => ∑ k, x k
  map_add' x y := by
    funext j
    simp [Finset.sum_add_distrib]
  map_smul' a x := by
    funext j
    simp [Finset.mul_sum]

theorem exercise_5B_3a (n : ℕ) (hn : 1 < n) :
    ∀ lam : F, IsEigenvalue (T_ex_5B_3 (F := F) n) lam ↔
      lam = 0 ∨ lam = (n : F) := by
  sorry

theorem exercise_5B_3b (n : ℕ) (hn : 1 < n) :
    minpoly F (T_ex_5B_3 (F := F) n) =
      Polynomial.X ^ 2 - Polynomial.C (n : F) * Polynomial.X := by
  sorry

/-- 5B.4 Spectral mapping: for {lit}`F = ℂ` and nonconstant {lit}`p`,
the eigenvalues of {lit}`p(T)` are exactly {lit}`p` of the eigenvalues
of {lit}`T`. -/
theorem exercise_5B_4 {V : Type*} [AddCommGroup V] [Module ℂ V]
    [Finite ℂ V] (T : V →ₗ[ℂ] V) (p : Polynomial ℂ)
    (hp : 0 < p.natDegree) (alpha : ℂ) :
    IsEigenvalue (aeval T p) alpha ↔
      ∃ lam : ℂ, IsEigenvalue T lam ∧ alpha = p.eval lam := by
  sorry

/-- 5B.5 The previous exercise fails over {lit}`ℝ`. -/
theorem exercise_5B_5 :
    ∃ (T : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ)) (p : Polynomial ℝ) (alpha : ℝ),
      IsEigenvalue (aeval T p) alpha ∧
        ¬ ∃ lam : ℝ, IsEigenvalue T lam ∧ alpha = p.eval lam := by
  sorry

open LADR.Section_5A (T_5_9) in
/-- 5B.6 The minimal polynomial of {lit}`T(w, z) = (−z, w)`. -/
theorem exercise_5B_6 :
    minpoly F (T_5_9 F) = Polynomial.X ^ 2 + 1 := by
  sorry

/-- 5B.7 (a) -/
theorem exercise_5B_7a :
    ∃ S T : (Fin 2 → F) →ₗ[F] (Fin 2 → F),
      minpoly F (S ∘ₗ T) ≠ minpoly F (T ∘ₗ S) := by
  sorry

/-- 5B.7 (b) -/
theorem exercise_5B_7b [Finite F V] (S T : V →ₗ[F] V)
    (hS : IsInvertible S) :
    minpoly F (S ∘ₗ T) = minpoly F (T ∘ₗ S) := by
  sorry

/-- 5B.8 The minimal polynomial of counterclockwise rotation by {lit}`1°`
is {lit}`x² − (2cos 1°)x + 1`. -/
noncomputable def T_ex_5B_8 : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) where
  toFun v := ![Real.cos (Real.pi / 180) * v 0 - Real.sin (Real.pi / 180) * v 1,
    Real.sin (Real.pi / 180) * v 0 + Real.cos (Real.pi / 180) * v 1]
  map_add' x y := by
    funext i
    fin_cases i
    · simp [mul_add]
      ring
    · simp [mul_add]
      ring
  map_smul' a x := by
    funext i
    fin_cases i
    · simp
      ring
    · simp
      ring

theorem exercise_5B_8 :
    minpoly ℝ T_ex_5B_8 = Polynomial.X ^ 2 -
      Polynomial.C (2 * Real.cos (Real.pi / 180)) * Polynomial.X + 1 := by
  sorry

open LADR.Section_3C (matrixOf) in
/-- 5B.9 If the matrix of {lit}`T` with respect to some basis has rational
entries, then all coefficients of the minimal polynomial are rational. -/
theorem exercise_5B_9 {V : Type*} [AddCommGroup V] [Module ℝ V] [Finite ℝ V]
    {n : ℕ} {v : Fin n → V} (hv : IsBasis ℝ v) (T : V →ₗ[ℝ] V)
    (hrat : ∀ j k, ∃ r : ℚ, matrixOf hv hv T j k = (r : ℝ)) :
    ∀ k, ∃ r : ℚ, (minpoly ℝ T).coeff k = (r : ℝ) := by
  sorry

/-- 5B.10 -/
theorem exercise_5B_10 [Finite F V] (T : V →ₗ[F] V) (v : V) (m : ℕ)
    (hm : finrank F V - 1 ≤ m) :
    Submodule.span F (Set.range fun i : Fin (m + 1) => (T ^ (i : ℕ)) v) =
      Submodule.span F
        (Set.range fun i : Fin (finrank F V) => (T ^ (i : ℕ)) v) := by
  sorry

open LADR.Section_3C (matrixOf) in
/-- 5B.11 (a) On a two-dimensional {lit}`V`, with
{lit}`ℳ(T) = (a c; b d)`: {lit}`T² − (a + d)T + (ad − bc)I = 0`. -/
theorem exercise_5B_11a {v : Fin 2 → V} (hv : IsBasis F v) (T : V →ₗ[F] V) :
    T ^ 2 - (matrixOf hv hv T 0 0 + matrixOf hv hv T 1 1) • T +
      (matrixOf hv hv T 0 0 * matrixOf hv hv T 1 1 -
        matrixOf hv hv T 1 0 * matrixOf hv hv T 0 1) • LinearMap.id = 0 := by
  sorry

open LADR.Section_3C (matrixOf) in
/-- 5B.11 (b), first case: if the matrix is {lit}`aI`, the minimal
polynomial is {lit}`z − a`. -/
theorem exercise_5B_11b1 [Finite F V] {v : Fin 2 → V} (hv : IsBasis F v)
    (T : V →ₗ[F] V) (hb : matrixOf hv hv T 1 0 = 0)
    (hc : matrixOf hv hv T 0 1 = 0)
    (had : matrixOf hv hv T 0 0 = matrixOf hv hv T 1 1) :
    minpoly F T = Polynomial.X - Polynomial.C (matrixOf hv hv T 0 0) := by
  sorry

open LADR.Section_3C (matrixOf) in
/-- 5B.11 (b), second case: otherwise the minimal polynomial is
{lit}`z² − (a + d)z + (ad − bc)`. -/
theorem exercise_5B_11b2 [Finite F V] {v : Fin 2 → V} (hv : IsBasis F v)
    (T : V →ₗ[F] V)
    (h : ¬ (matrixOf hv hv T 1 0 = 0 ∧ matrixOf hv hv T 0 1 = 0 ∧
      matrixOf hv hv T 0 0 = matrixOf hv hv T 1 1)) :
    minpoly F T = Polynomial.X ^ 2 -
      Polynomial.C (matrixOf hv hv T 0 0 + matrixOf hv hv T 1 1) *
        Polynomial.X +
      Polynomial.C (matrixOf hv hv T 0 0 * matrixOf hv hv T 1 1 -
        matrixOf hv hv T 1 0 * matrixOf hv hv T 0 1) := by
  sorry

open LADR.Section_5A (T_ex_5A_42) in
/-- 5B.12 The minimal polynomial of
{lit}`T(x₁, …, xₙ) = (x₁, 2x₂, …, nxₙ)`. -/
theorem exercise_5B_12 (n : ℕ) :
    minpoly ℝ (T_ex_5A_42 n) =
      ∏ k : Fin n, (Polynomial.X - Polynomial.C ((k : ℕ) + 1 : ℝ)) := by
  sorry

/-- 5B.13 -/
theorem exercise_5B_13 [Finite F V] (T : V →ₗ[F] V) (p : Polynomial F) :
    ∃! r : Polynomial F, aeval T r = aeval T p ∧
      r.degree < (minpoly F T).degree := by
  sorry

/-- 5B.14 An operator with minimal polynomial
{lit}`4 + 5z − 6z² − 7z³ + 2z⁴ + z⁵` is invertible (constant term nonzero),
and the minimal polynomial of {lit}`T⁻¹` is
{lit}`1/4 + z/2 − 7z²/4 − 3z³/2 + 5z⁴/4 + z⁵`. -/
theorem exercise_5B_14 {V : Type*} [AddCommGroup V] [Module ℝ V]
    [Finite ℝ V] (T : V →ₗ[ℝ] V) (hT : IsInvertible T)
    (hmin : minpoly ℝ T = Polynomial.C 4 + Polynomial.C 5 * Polynomial.X -
      Polynomial.C 6 * Polynomial.X ^ 2 - Polynomial.C 7 * Polynomial.X ^ 3 +
      Polynomial.C 2 * Polynomial.X ^ 4 + Polynomial.X ^ 5) :
    minpoly ℝ hT.inv = Polynomial.C (1 / 4 : ℝ) +
      Polynomial.C (1 / 2) * Polynomial.X -
      Polynomial.C (7 / 4) * Polynomial.X ^ 2 -
      Polynomial.C (3 / 2) * Polynomial.X ^ 3 +
      Polynomial.C (5 / 4) * Polynomial.X ^ 4 + Polynomial.X ^ 5 := by
  sorry

/-- 5B.15 The function {lit}`λ ↦ dim range(T − λI)` is not continuous
(for {lit}`V` a nonzero finite-dimensional complex vector space). -/
theorem exercise_5B_15 {V : Type*} [AddCommGroup V] [Module ℂ V]
    [Finite ℂ V] (hV : 0 < finrank ℂ V) (T : V →ₗ[ℂ] V) :
    ¬ Continuous (fun lam : ℂ =>
      (finrank ℂ (range (T - lam • (LinearMap.id : V →ₗ[ℂ] V))) : ℝ)) := by
  sorry

open LADR.Section_3A (fromFnToFm) in
/-- 5B.16 The companion-matrix operator with last column
{lit}`(−a₀, …, −a_{n−1})` has minimal polynomial
{lit}`a₀ + a₁z + ⋯ + a_{n−1}z^{n−1} + zⁿ`; hence every monic polynomial is
the minimal polynomial of some operator. -/
def companionOp {n : ℕ} (a : Fin n → F) : (Fin n → F) →ₗ[F] (Fin n → F) :=
  LADR.Section_3A.fromFnToFm fun j k =>
    if (k : ℕ) = n - 1 then -(a j)
    else if (j : ℕ) = (k : ℕ) + 1 then 1 else 0

theorem exercise_5B_16 {n : ℕ} (hn : 0 < n) (a : Fin n → F) :
    minpoly F (companionOp a) =
      Polynomial.X ^ n + ∑ i : Fin n, Polynomial.C (a i) *
        Polynomial.X ^ (i : ℕ) := by
  sorry

/-- 5B.17 -/
theorem exercise_5B_17 [Finite F V] (T : V →ₗ[F] V) (lam : F) :
    minpoly F (T - lam • (LinearMap.id : V →ₗ[F] V)) =
      (minpoly F T).comp (Polynomial.X + Polynomial.C lam) := by
  sorry

/-- 5B.18 -/
theorem exercise_5B_18 [Finite F V] (T : V →ₗ[F] V) (lam : F)
    (hlam : lam ≠ 0) :
    minpoly F (lam • T) = Polynomial.C (lam ^ (minpoly F T).natDegree) *
      (minpoly F T).comp (Polynomial.C lam⁻¹ * Polynomial.X) := by
  sorry

/-- 5B.19 The subspace {lit}`ℰ = {q(T) : q ∈ 𝒫(F)}` of {lit}`ℒ(V)` has
dimension equal to the degree of the minimal polynomial of {lit}`T`. -/
theorem exercise_5B_19 [Finite F V] (T : V →ₗ[F] V) :
    finrank F (range (Polynomial.aeval (R := F) T).toLinearMap) =
      (minpoly F T).natDegree := by
  sorry

/-- 5B.20 -/
theorem exercise_5B_20 (T : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ))
    (hev : ∀ lam : ℝ, IsEigenvalue T lam ↔ lam = 3 ∨ lam = 5 ∨ lam = 8) :
    ((T - 3 • LinearMap.id) ^ 2) ∘ₗ ((T - 5 • LinearMap.id) ^ 2) ∘ₗ
      ((T - 8 • LinearMap.id) ^ 2) = 0 := by
  sorry

/-- 5B.21 -/
theorem exercise_5B_21 [Finite F V] (T : V →ₗ[F] V) :
    (minpoly F T).natDegree ≤ 1 + finrank F (range T) := by
  sorry

/-- 5B.22 -/
theorem exercise_5B_22 [Finite F V] (T : V →ₗ[F] V) :
    IsInvertible T ↔ LinearMap.id ∈ Submodule.span F
      (Set.range fun i : Fin (finrank F V) => T ^ ((i : ℕ) + 1)) := by
  sorry

/-- 5B.23 -/
theorem exercise_5B_23 [Finite F V] (T : V →ₗ[F] V) (v : V) :
    InvariantUnder T (Submodule.span F
      (Set.range fun i : Fin (finrank F V) => (T ^ (i : ℕ)) v)) := by
  sorry

/-- 5B.24 -/
theorem exercise_5B_24 {V : Type*} [AddCommGroup V] [Module ℂ V]
    [Finite ℂ V] (T : V →ₗ[ℂ] V)
    (hev : ∀ lam : ℂ, IsEigenvalue T lam ↔ lam = 5 ∨ lam = 6) :
    ((T - 5 • LinearMap.id) ^ (finrank ℂ V - 1)) ∘ₗ
      ((T - 6 • LinearMap.id) ^ (finrank ℂ V - 1)) = 0 := by
  sorry

open LADR.Section_5A (exercise_5A_38_quotient_op) in
/-- 5B.25 (a) The minimal polynomial of {lit}`T` is a polynomial multiple of
the minimal polynomial of the quotient operator {lit}`T/U`. -/
theorem exercise_5B_25a [Finite F V] (T : V →ₗ[F] V) (U : Submodule F V)
    (hU : InvariantUnder T U) :
    minpoly F (exercise_5A_38_quotient_op T U hU) ∣ minpoly F T := by
  sorry

open LADR.Section_5A (exercise_5A_38_quotient_op) in
/-- 5B.25 (b) {lit}`(minpoly T|_U) · (minpoly T/U)` is a polynomial multiple
of the minimal polynomial of {lit}`T`. -/
theorem exercise_5B_25b [Finite F V] (T : V →ₗ[F] V) (U : Submodule F V)
    (hU : InvariantUnder T U) :
    minpoly F T ∣
      minpoly F hU.restrict * minpoly F (exercise_5A_38_quotient_op T U hU) := by
  sorry

open LADR.Section_5A (exercise_5A_38_quotient_op) in
/-- 5B.26 The eigenvalues of {lit}`T` are exactly the eigenvalues of
{lit}`T|_U` together with those of {lit}`T/U`. -/
theorem exercise_5B_26 [Finite F V] (T : V →ₗ[F] V) (U : Submodule F V)
    (hU : InvariantUnder T U) (lam : F) :
    IsEigenvalue T lam ↔ IsEigenvalue hU.restrict lam ∨
      IsEigenvalue (exercise_5A_38_quotient_op T U hU) lam := by
  sorry

open LADR.Section_1B (Complexification exercise_1B_8) in
open LADR.Section_3B (complexification_map) in
/-- 5B.27 The minimal polynomial of the complexification {lit}`T_ℂ` is the
(complexification of the) minimal polynomial of {lit}`T`. -/
theorem exercise_5B_27 {V : Type*} [AddCommGroup V] [Module ℝ V]
    [Finite ℝ V] (T : V →ₗ[ℝ] V) :
    letI : Module ℂ (Complexification V) := exercise_1B_8 V
    minpoly ℂ (complexification_map T) =
      (minpoly ℝ T).map (algebraMap ℝ ℂ) := by
  sorry

/-- 5B.28 The minimal polynomial of the dual operator {lit}`T′` equals the
minimal polynomial of {lit}`T`. -/
theorem exercise_5B_28 [Finite F V] (T : V →ₗ[F] V) :
    minpoly F T.dualMap = minpoly F T := by
  sorry

/-- 5B.29 Every operator on a finite-dimensional real vector space of
dimension at least two has an invariant subspace of dimension two. -/
theorem exercise_5B_29 {V : Type*} [AddCommGroup V] [Module ℝ V]
    [Finite ℝ V] (hV : 2 ≤ finrank ℝ V) (T : V →ₗ[ℝ] V) :
    ∃ U : Submodule ℝ V, InvariantUnder T U ∧ finrank ℝ U = 2 := by
  sorry

end LADR.Section_5B
