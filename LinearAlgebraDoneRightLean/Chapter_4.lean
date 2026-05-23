import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Ring
import LinearAlgebraDoneRightLean.Section_2A
import LinearAlgebraDoneRightLean.Section_2B
import LinearAlgebraDoneRightLean.Section_2C
import CompanionHelper

/-!
# Axler, *Linear Algebra Done Right* (4e) — Chapter 4: Polynomials
-/

namespace LADR.Chapter_4

open LADR.Section_2A (Spans)
open LADR.Section_2B (IsBasis)
open Module (finrank)

/-! 4.1 Definition: real part {lit}`Re z`, imaginary part {lit}`Im z` -/

example (z : ℂ) : ℝ := z.re
example (z : ℂ) : ℝ := z.im
example (z : ℂ) : z = z.re + z.im * Complex.I := (Complex.re_add_im z).symm

/-! 4.2 Definition: complex conjugate {lit}`z̄`, absolute value {lit}`|z|`.

In mathlib the conjugate is {name}`starRingEnd` (with star notation) and the
absolute value is the {lit}`Norm` notation {lit}`‖z‖ = √(Re z)² + (Im z)²`. -/

example (z : ℂ) : ℂ := starRingEnd ℂ z
example (z : ℂ) : starRingEnd ℂ z = z.re - z.im * Complex.I := by
  apply Complex.ext <;> simp

noncomputable example (z : ℂ) : ℝ := ‖z‖
example (z : ℂ) : ‖z‖ = Real.sqrt (z.re ^ 2 + z.im ^ 2) :=
  Complex.norm_eq_sqrt_sq_add_sq z

/-! 4.3 Example: properties of {lit}`3 + 2i`. -/

example : (3 + 2 * Complex.I : ℂ).re = 3 := by simp
example : (3 + 2 * Complex.I : ℂ).im = 2 := by simp
example : starRingEnd ℂ (3 + 2 * Complex.I) = 3 - 2 * Complex.I := by
  apply Complex.ext <;> simp

/-! 4.4 Properties of complex numbers — provided by mathlib. -/

set_option linter.unnecessarySeqFocus false in
example (z : ℂ) : z + starRingEnd ℂ z = 2 * z.re := by
  apply Complex.ext <;> simp <;> ring

set_option linter.unnecessarySeqFocus false in
example (z : ℂ) : z - starRingEnd ℂ z = 2 * z.im * Complex.I := by
  apply Complex.ext <;> simp <;> ring

example (z : ℂ) : z * starRingEnd ℂ z = (‖z‖ : ℂ) ^ 2 := by
  rw [Complex.mul_conj, ← Complex.sq_norm z]
  push_cast
  rfl

example (w z : ℂ) : starRingEnd ℂ (w + z) =
    starRingEnd ℂ w + starRingEnd ℂ z := map_add _ _ _

example (w z : ℂ) : starRingEnd ℂ (w * z) =
    starRingEnd ℂ w * starRingEnd ℂ z := map_mul _ _ _

example (z : ℂ) : starRingEnd ℂ (starRingEnd ℂ z) = z := by
  apply Complex.ext <;> simp

example (z : ℂ) : |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm z

example (z : ℂ) : |z.im| ≤ ‖z‖ := Complex.abs_im_le_norm z

example (z : ℂ) : ‖starRingEnd ℂ z‖ = ‖z‖ := Complex.norm_conj _

example (w z : ℂ) : ‖w * z‖ = ‖w‖ * ‖z‖ := norm_mul w z

/-- (triangle inequality) -/
example (w z : ℂ) : ‖w + z‖ ≤ ‖w‖ + ‖z‖ := norm_add_le w z

/-! Zeros of Polynomials.

Following Axler, a polynomial is a formal expression in {lit}`z` of the form
sum of coefficients times powers of {lit}`z`. In mathlib this is
{lit}`Polynomial F`, with evaluation {name}`Polynomial.eval`. -/

variable {F : Type*} [Field F]

/-! 4.5 Definition: zero of a polynomial — mathlib's
{name}`Polynomial.IsRoot`. -/

example (p : Polynomial F) (lam : F) : Prop := p.IsRoot lam

example (p : Polynomial F) (lam : F) : p.IsRoot lam ↔ p.eval lam = 0 :=
  Polynomial.IsRoot.def

/-! 4.6 Each zero of a polynomial corresponds to a degree-one factor -/

theorem isRoot_iff_dvd (p : Polynomial F) (lam : F) :
    p.IsRoot lam ↔ (Polynomial.X - Polynomial.C lam) ∣ p :=
  Polynomial.dvd_iff_isRoot.symm

/-- Axler's quantitative form of 4.6: {lit}`p(λ) = 0` iff there exists
{lit}`q` of degree {lit}`(natDegree p) − 1` with {lit}`p = (X − λ) · q`. -/
theorem isRoot_iff_eq_mul (p : Polynomial F) (lam : F) (m : ℕ) (hm : 1 ≤ m)
    (hp_deg : p.natDegree = m) :
    p.IsRoot lam ↔
      ∃ q : Polynomial F, q.natDegree = m - 1 ∧
        p = (Polynomial.X - Polynomial.C lam) * q := by
  have hp_ne : p ≠ 0 := by
    intro hpz; rw [hpz, Polynomial.natDegree_zero] at hp_deg; omega
  have hxc_ne : (Polynomial.X - Polynomial.C lam : Polynomial F) ≠ 0 :=
    Polynomial.X_sub_C_ne_zero lam
  constructor
  · intro hroot
    have hdvd : (Polynomial.X - Polynomial.C lam) ∣ p :=
      Polynomial.dvd_iff_isRoot.mpr hroot
    obtain ⟨q, hpeq⟩ := hdvd
    have hq_ne : q ≠ 0 := by
      intro hqz; rw [hqz, mul_zero] at hpeq; exact hp_ne hpeq
    refine ⟨q, ?_, hpeq⟩
    have hnd : p.natDegree =
        (Polynomial.X - Polynomial.C lam).natDegree + q.natDegree := by
      rw [hpeq, Polynomial.natDegree_mul hxc_ne hq_ne]
    rw [Polynomial.natDegree_X_sub_C] at hnd
    omega
  · rintro ⟨q, _, hpeq⟩
    rw [Polynomial.IsRoot.def, hpeq]
    simp

/-! 4.8 Degree {lit}`m` implies at most {lit}`m` zeros -/

theorem card_roots_le_natDegree (p : Polynomial F) :
    p.roots.card ≤ p.natDegree :=
  Polynomial.card_roots' p

/-! Division Algorithm for Polynomials. -/

/-! 4.9 For {lit}`p, s ∈ 𝒫(F)` with {lit}`s ≠ 0`, there exist unique
{lit}`q, r ∈ 𝒫(F)` with {lit}`p = s · q + r` and {lit}`deg r < deg s`. -/

theorem division_algorithm (p s : Polynomial F) (hs : s ≠ 0) :
    ∃! qr : Polynomial F × Polynomial F,
      p = s * qr.1 + qr.2 ∧ qr.2.degree < s.degree := by
  refine ⟨⟨p / s, p % s⟩, ?_, ?_⟩
  · refine ⟨?_, Polynomial.degree_mod_lt p hs⟩
    exact (EuclideanDomain.div_add_mod p s).symm
  · rintro ⟨q, r⟩ ⟨hpeq, hrdeg⟩
    -- {lit}`s · (q − p/s) = p%s − r`, but RHS has degree {lit}`< deg s`,
    -- forcing {lit}`q = p/s`, hence {lit}`r = p%s`.
    have hpmod := EuclideanDomain.div_add_mod p s
    have hdiff : s * (q - p / s) = (p % s) - r := by
      have h : s * q + r = s * (p / s) + (p % s) := by rw [← hpeq, hpmod]
      linear_combination h
    have hrhs_lt : ((p % s) - r).degree < s.degree :=
      lt_of_le_of_lt (Polynomial.degree_sub_le _ _)
        (max_lt (Polynomial.degree_mod_lt p hs) hrdeg)
    have hsub_zero : q - p / s = 0 := by
      by_contra hne
      have h_nonneg : (0 : WithBot ℕ) ≤ (q - p / s).degree :=
        Polynomial.zero_le_degree_iff.mpr hne
      have h_lhs_deg : s.degree ≤ (s * (q - p / s)).degree := by
        rw [Polynomial.degree_mul]
        exact le_add_of_nonneg_right h_nonneg
      rw [hdiff] at h_lhs_deg
      exact absurd hrhs_lt (not_lt.mpr h_lhs_deg)
    have hq : q = p / s := sub_eq_zero.mp hsub_zero
    have hr : r = p % s := by
      rw [hq, sub_self, mul_zero] at hdiff
      exact (sub_eq_zero.mp hdiff.symm).symm
    simp [hq, hr]

/-! Factorization of Polynomials over ℂ. -/

/-! 4.12 Fundamental theorem of algebra, first version. mathlib provides
this as {name}`Complex.exists_root`. -/

theorem fundamental_theorem_of_algebra (p : Polynomial ℂ) (hp : 0 < p.degree) :
    ∃ z : ℂ, p.IsRoot z :=
  Complex.exists_root hp

/-! 4.13 Fundamental theorem of algebra, second version: factorization into
linear factors over {lit}`ℂ`. Stated using a {name}`Multiset` of roots
(closer to Axler's "list of zeros λ₁, …, λₘ"). -/

theorem fta_factorization (p : Polynomial ℂ) :
    Polynomial.C p.leadingCoeff *
      (Multiset.map (fun a => Polynomial.X - Polynomial.C a) p.roots).prod
        = p := by
  by_cases hp : p = 0
  · subst hp; simp
  apply Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C
  exact (Polynomial.splits_iff_card_roots.mp (IsAlgClosed.splits p))

/-! Factorization of Polynomials over ℝ. -/

/-! 4.14 Polynomials with real coefficients have nonreal zeros in pairs -/

theorem real_coeffs_nonreal_zero_pair
    (p : Polynomial ℂ) (hp_real : ∀ k, (p.coeff k).im = 0) (lam : ℂ)
    (hlam : p.IsRoot lam) : p.IsRoot (starRingEnd ℂ lam) := by
  rw [Polynomial.IsRoot.def] at hlam ⊢
  -- {lit}`p(λ̄) = conj (p(λ)) = conj 0 = 0`.
  have hcoeff_conj : ∀ k, starRingEnd ℂ (p.coeff k) = p.coeff k := by
    intro k
    apply Complex.ext
    · simp
    · simp [hp_real k]
  have h : p.eval (starRingEnd ℂ lam) = starRingEnd ℂ (p.eval lam) := by
    rw [Polynomial.eval_eq_sum, Polynomial.eval_eq_sum]
    rw [Polynomial.sum_def, Polynomial.sum_def, map_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [map_mul, map_pow, hcoeff_conj]
  rw [h, hlam, map_zero]

/-! 4.15 {lit}`x² + bx + c` factors over {lit}`ℝ` iff {lit}`b² ≥ 4c`. -/

theorem quadratic_factor (b c : ℝ) :
    (∃ lam₁ lam₂ : ℝ,
      Polynomial.X ^ 2 + Polynomial.C b * Polynomial.X + Polynomial.C c =
        (Polynomial.X - Polynomial.C lam₁) *
        (Polynomial.X - Polynomial.C lam₂)) ↔ b ^ 2 ≥ 4 * c := by
  constructor
  · rintro ⟨lam₁, lam₂, heq⟩
    -- Evaluate at 0 and 1 to extract {lit}`c = lam₁ lam₂` and
    -- {lit}`b = -(lam₁ + lam₂)`. Then
    -- {lit}`b² − 4c = (lam₁ − lam₂)² ≥ 0`.
    have h0 := congrArg (Polynomial.eval 0) heq
    have h1 := congrArg (Polynomial.eval 1) heq
    simp at h0 h1
    have h_sum_lam : lam₁ + lam₂ = -b := by nlinarith
    have h_sq_diff : (lam₁ - lam₂) ^ 2 = b ^ 2 - 4 * c := by
      have h_id : (lam₁ - lam₂) ^ 2 =
          (lam₁ + lam₂) ^ 2 - 4 * (lam₁ * lam₂) := by ring
      rw [h_id, h_sum_lam, ← h0]; ring
    linarith [sq_nonneg (lam₁ - lam₂), h_sq_diff]
  · intro hbc
    have hpos : 0 ≤ b ^ 2 / 4 - c := by linarith
    set d := Real.sqrt (b ^ 2 / 4 - c)
    refine ⟨-b / 2 + d, -b / 2 - d, ?_⟩
    have hd_sq : d * d = b ^ 2 / 4 - c := Real.mul_self_sqrt hpos
    have h_sum_lam : (-b / 2 + d) + (-b / 2 - d) = -b := by ring
    have h_prod_lam : (-b / 2 + d) * (-b / 2 - d) = c := by nlinarith
    have h_sum_C : Polynomial.C (-b / 2 + d) + Polynomial.C (-b / 2 - d) =
        -Polynomial.C b := by
      rw [← Polynomial.C_add, h_sum_lam, Polynomial.C_neg]
    have h_prod_C : Polynomial.C (-b / 2 + d) * Polynomial.C (-b / 2 - d) =
        Polynomial.C c := by
      rw [← Polynomial.C_mul, h_prod_lam]
    linear_combination Polynomial.X * h_sum_C - h_prod_C

/-! 4.16 Factorization of a polynomial over {lit}`ℝ`.

Strong induction on {lit}`p.natDegree`. Base case: {lit}`natDegree 0`
gives {lit}`p = C c`. Inductive step splits on whether {lit}`p` has a
real root: if yes, peel off {lit}`(X − λ)` and recurse; if no, by FTA
{lit}`p` has a nonreal complex root {lit}`z`, and the quadratic
{lit}`X² − (2 Re z) X + |z|²` divides {lit}`p` (mathlib's
{name}`Polynomial.quadratic_dvd_of_aeval_eq_zero_im_ne_zero`); peel that
off and recurse. The discriminant is
{lit}`(2 Re z)² − 4|z|² = −4(Im z)² < 0`. -/

/-- Helper for 4.16: a quadratic {lit}`X² - C(2α) X + C β` has natDegree 2. -/
private lemma natDegree_quadratic_aux (α β : ℝ) :
    (Polynomial.X ^ 2 - Polynomial.C (2 * α) * Polynomial.X +
      Polynomial.C β).natDegree = 2 := by
  have hform :
      Polynomial.X ^ 2 - Polynomial.C (2 * α) * Polynomial.X + Polynomial.C β =
      Polynomial.C 1 * Polynomial.X ^ 2 +
        Polynomial.C (-(2 * α)) * Polynomial.X + Polynomial.C β := by
    rw [Polynomial.C_neg, Polynomial.C_1]; ring
  rw [hform]
  exact Polynomial.natDegree_quadratic one_ne_zero

/-- Helper for 4.16: if {lit}`p : ℝ[X]` has no real root and {lit}`z : ℂ`
is a root of the lift of {lit}`p` to {lit}`ℂ[X]`, then {lit}`z.im ≠ 0`. -/
private lemma complex_root_nonreal_of_no_real_root (p : Polynomial ℝ)
    (hreal : ∀ x : ℝ, ¬ p.IsRoot x) {z : ℂ}
    (hz : (p.map (algebraMap ℝ ℂ)).eval z = 0) :
    z.im ≠ 0 := by
  intro hzim
  -- {lit}`z = z.re` (as a complex number with zero imaginary part).
  have hz_eq : (z.re : ℂ) = z := by apply Complex.ext <;> simp [hzim]
  -- Evaluate the lift at {lit}`z.re`.
  refine hreal z.re ?_
  rw [Polynomial.IsRoot.def]
  have hpC_eval : (p.map (algebraMap ℝ ℂ)).eval ((z.re : ℂ)) = 0 := by
    rw [hz_eq]; exact hz
  rw [Polynomial.eval_map] at hpC_eval
  -- {lit}`eval₂ (algebraMap ℝ ℂ) (z.re : ℂ) p = (algebraMap ℝ ℂ) (p.eval z.re)`.
  rw [show ((z.re : ℝ) : ℂ) = (algebraMap ℝ ℂ) z.re from rfl,
      Polynomial.eval₂_at_apply] at hpC_eval
  -- {lit}`algebraMap ℝ ℂ = Complex.ofReal`, which is injective.
  have hcast : ((Polynomial.eval z.re p : ℝ) : ℂ) = 0 := hpC_eval
  exact_mod_cast hcast

/-- Helper for 4.16: the discriminant {lit}`(2 Re z)² - 4|z|²` is negative
when {lit}`z.im ≠ 0`. -/
private lemma discriminant_neg_of_im_ne_zero {z : ℂ} (hz : z.im ≠ 0) :
    (-(2 * z.re)) ^ 2 < 4 * ‖z‖ ^ 2 := by
  have hsq : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  rw [hsq]
  have him_pos : 0 < z.im ^ 2 := by positivity
  nlinarith

/-! 4.16 Factorization of a polynomial over {lit}`ℝ`.

Strong induction on {lit}`p.natDegree`. Base case: {lit}`natDegree 0`
gives {lit}`p = C c`. Inductive step splits on whether {lit}`p` has a
real root: if yes, peel off {lit}`(X − λ)` and recurse; if no, by FTA
{lit}`p` has a nonreal complex root {lit}`z`, and the quadratic
{lit}`X² − (2 Re z) X + |z|²` divides {lit}`p` (mathlib's
{name}`Polynomial.quadratic_dvd_of_aeval_eq_zero_im_ne_zero`); peel that
off and recurse. -/

theorem real_polynomial_factorization (p : Polynomial ℝ) (hp : p ≠ 0) :
    ∃ (c : ℝ) (m M : ℕ) (lams : Fin m → ℝ) (bs cs : Fin M → ℝ),
      (∀ k, bs k ^ 2 < 4 * cs k) ∧
      p = Polynomial.C c *
        (∏ k, (Polynomial.X - Polynomial.C (lams k))) *
        (∏ k, (Polynomial.X ^ 2 + Polynomial.C (bs k) * Polynomial.X +
          Polynomial.C (cs k))) := by
  induction hn : p.natDegree using Nat.strong_induction_on generalizing p with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with hn_zero | hn_pos
    · -- Base case: {lit}`natDegree p = 0`, so {lit}`p = C (p.coeff 0)`.
      subst hn_zero
      refine ⟨p.coeff 0, 0, 0, Fin.elim0, Fin.elim0, Fin.elim0, ?_, ?_⟩
      · intro k; exact k.elim0
      · simp
        exact Polynomial.eq_C_of_natDegree_eq_zero hn
    · classical
      by_cases hreal : ∃ lam : ℝ, p.IsRoot lam
      · -- Peel off a real root: {lit}`p = (X − λ) q`, recurse on q.
        obtain ⟨lam, hlam⟩ := hreal
        obtain ⟨q, hpq⟩ : (Polynomial.X - Polynomial.C lam) ∣ p :=
          Polynomial.dvd_iff_isRoot.mpr hlam
        have hxc_ne : (Polynomial.X - Polynomial.C lam : Polynomial ℝ) ≠ 0 :=
          Polynomial.X_sub_C_ne_zero lam
        have hq_ne : q ≠ 0 := fun hqz => by
          rw [hqz, mul_zero] at hpq; exact hp hpq
        have hq_deg : q.natDegree = n - 1 := by
          have := Polynomial.natDegree_mul hxc_ne hq_ne
          rw [← hpq, Polynomial.natDegree_X_sub_C] at this
          omega
        have hq_lt : q.natDegree < n := by omega
        obtain ⟨c, m', M, lams', bs, cs, hdisc, hfact⟩ :=
          ih q.natDegree hq_lt q hq_ne rfl
        refine ⟨c, m' + 1, M, Fin.cons lam lams', bs, cs, hdisc, ?_⟩
        rw [hpq, hfact]
        have h_prod : ∏ k : Fin (m' + 1),
            (Polynomial.X - Polynomial.C (Fin.cons lam lams' k)) =
            (Polynomial.X - Polynomial.C lam) *
              ∏ i : Fin m', (Polynomial.X - Polynomial.C (lams' i)) := by
          rw [Fin.prod_univ_succ]
          simp only [Fin.cons_zero, Fin.cons_succ]
        rw [h_prod]
        ring
      · -- No real root: peel off a real quadratic from a nonreal root.
        push Not at hreal
        have hpC_ne : p.map (algebraMap ℝ ℂ) ≠ 0 := by
          rw [Ne, Polynomial.map_eq_zero_iff
            (Complex.ofReal_injective : Function.Injective (algebraMap ℝ ℂ))]
          exact hp
        have hpC_deg : 0 < (p.map (algebraMap ℝ ℂ)).degree := by
          rw [← Polynomial.natDegree_pos_iff_degree_pos,
              Polynomial.natDegree_map]
          omega
        obtain ⟨z, hz⟩ := Complex.exists_root hpC_deg
        rw [Polynomial.IsRoot.def] at hz
        have hz_im : z.im ≠ 0 :=
          complex_root_nonreal_of_no_real_root p hreal hz
        have h_aeval_zero : Polynomial.aeval z p = 0 := by
          rw [Polynomial.aeval_def, ← Polynomial.eval_map]
          exact hz
        obtain ⟨q, hpq⟩ :=
          Polynomial.quadratic_dvd_of_aeval_eq_zero_im_ne_zero p h_aeval_zero
            hz_im
        set s : Polynomial ℝ := Polynomial.X ^ 2 -
            Polynomial.C (2 * z.re) * Polynomial.X + Polynomial.C (‖z‖ ^ 2)
            with hs_def
        have hs_deg : s.natDegree = 2 := natDegree_quadratic_aux z.re (‖z‖ ^ 2)
        have hs_ne : s ≠ 0 := fun hsz => by
          rw [hsz, Polynomial.natDegree_zero] at hs_deg; omega
        have hq_ne : q ≠ 0 := fun hqz => by
          rw [hqz, mul_zero] at hpq; exact hp hpq
        have hq_deg : q.natDegree = n - 2 := by
          have h_mul := Polynomial.natDegree_mul hs_ne hq_ne
          rw [← hpq, hs_deg, hn] at h_mul
          omega
        have hq_lt : q.natDegree < n := by omega
        obtain ⟨c, m', M', lams', bs, cs, hdisc, hfact⟩ :=
          ih q.natDegree hq_lt q hq_ne rfl
        refine ⟨c, m', M' + 1, lams',
          Fin.cons (-(2 * z.re)) bs, Fin.cons (‖z‖ ^ 2) cs, ?_, ?_⟩
        · intro k
          induction k using Fin.cases with
          | zero => exact discriminant_neg_of_im_ne_zero hz_im
          | succ k => exact hdisc k
        · rw [hpq, hfact]
          have hs_form : s = Polynomial.X ^ 2 +
              Polynomial.C (-(2 * z.re)) * Polynomial.X +
              Polynomial.C (‖z‖ ^ 2) := by
            show Polynomial.X ^ 2 - Polynomial.C (2 * z.re) * Polynomial.X +
                  Polynomial.C (‖z‖ ^ 2) =
                Polynomial.X ^ 2 + Polynomial.C (-(2 * z.re)) * Polynomial.X +
                  Polynomial.C (‖z‖ ^ 2)
            rw [Polynomial.C_neg]; ring
          have h_prod :
            ∏ k : Fin (M' + 1), (Polynomial.X ^ 2 +
              Polynomial.C (Fin.cons (-(2 * z.re)) bs k) * Polynomial.X +
              Polynomial.C (Fin.cons (‖z‖ ^ 2) cs k)) =
            s * ∏ i : Fin M', (Polynomial.X ^ 2 +
              Polynomial.C (bs i) * Polynomial.X + Polynomial.C (cs i)) := by
            rw [Fin.prod_univ_succ]
            simp only [Fin.cons_zero, Fin.cons_succ]
            rw [hs_form]
          rw [h_prod]
          ring

/-! # Exercises -/

/-- 4.1 (a) -/
theorem exercise_4_1a (z : ℂ) : z + starRingEnd ℂ z = 2 * z.re := by
  sorry

/-- 4.1 (b) -/
theorem exercise_4_1b (z : ℂ) :
    z - starRingEnd ℂ z = 2 * z.im * Complex.I := by
  sorry

/-- 4.1 (c) -/
theorem exercise_4_1c (z : ℂ) : z * starRingEnd ℂ z = (‖z‖ : ℂ) ^ 2 := by
  sorry

/-- 4.1 (d) -/
theorem exercise_4_1d (w z : ℂ) :
    starRingEnd ℂ (w + z) = starRingEnd ℂ w + starRingEnd ℂ z ∧
    starRingEnd ℂ (w * z) = starRingEnd ℂ w * starRingEnd ℂ z := by
  sorry

/-- 4.1 (e) -/
theorem exercise_4_1e (z : ℂ) : starRingEnd ℂ (starRingEnd ℂ z) = z := by
  sorry

/-- 4.1 (f) -/
theorem exercise_4_1f (z : ℂ) : |z.re| ≤ ‖z‖ ∧ |z.im| ≤ ‖z‖ := by
  sorry

/-- 4.1 (g) -/
theorem exercise_4_1g (z : ℂ) : ‖starRingEnd ℂ z‖ = ‖z‖ := by
  sorry

/-- 4.1 (h) -/
theorem exercise_4_1h (w z : ℂ) : ‖w * z‖ = ‖w‖ * ‖z‖ := by
  sorry

/-- 4.2 Reverse triangle inequality. -/
theorem exercise_4_2 (w z : ℂ) : |‖w‖ - ‖z‖| ≤ ‖w - z‖ := by
  sorry

/-- 4.3 Suppose {lit}`V` is a complex vector space and {lit}`φ ∈ V'`. Define
{lit}`σ(v) = Re φ(v)`. Show {lit}`φ(v) = σ(v) − i σ(iv)`. -/
theorem exercise_4_3 {V : Type*} [AddCommGroup V] [Module ℂ V]
    (phi : V →ₗ[ℂ] ℂ) (v : V) :
    phi v = (phi v).re - Complex.I * (phi (Complex.I • v)).re := by
  sorry

/-- 4.4 Is {lit}`{0} ∪ {p : deg p = m}` a subspace of {lit}`𝒫(F)`? -/
def exercise_4_4 (m : ℕ) (_hm : 1 ≤ m) :
    Decidable (∃ (U : Submodule F (Polynomial F)),
      ∀ p : Polynomial F, p ∈ U ↔ p = 0 ∨ p.natDegree = m) := by
  -- first line should be `apply isTrue` or `apply isFalse`
  sorry

/-- 4.5 Is {lit}`{0} ∪ {p : deg p is even}` a subspace of {lit}`𝒫(F)`? -/
def exercise_4_5 :
    Decidable (∃ (U : Submodule F (Polynomial F)),
      ∀ p : Polynomial F, p ∈ U ↔ p = 0 ∨ Even p.natDegree) := by
  -- first line should be `apply isTrue` or `apply isFalse`
  sorry

/-- 4.6 -/
theorem exercise_4_6 (m n : ℕ) (_hmn : m ≤ n) (lams : Fin m → F) :
    ∃ p : Polynomial F, p.natDegree = n ∧
      (∀ k, p.IsRoot (lams k)) ∧
      (∀ x : F, p.IsRoot x → ∃ k, x = lams k) := by
  sorry

/-- 4.7 Lagrange interpolation. -/
theorem exercise_4_7 {m : ℕ} (z : Fin (m + 1) → F) (_hz : Function.Injective z)
    (w : Fin (m + 1) → F) :
    ∃! p : Polynomial.degreeLT F (m + 1),
      ∀ k, (p : Polynomial F).eval (z k) = w k := by
  sorry

/-- 4.8 -/
theorem exercise_4_8 (p : Polynomial ℂ) (_hp : 0 < p.natDegree) :
    p.roots.card = p.natDegree ↔
      ∀ z : ℂ, p.IsRoot z → ¬ p.derivative.IsRoot z := by
  sorry

/-- 4.9 Every odd-degree real polynomial has a real zero. -/
theorem exercise_4_9 (p : Polynomial ℝ) (_hp : Odd p.natDegree) :
    ∃ x : ℝ, p.IsRoot x := by
  sorry

/-- 4.10 The difference-quotient linear map
{lit}`(Tp)(x) = (p(x) − p(3))/(x − 3)`. The map is stated for the underlying
function; mathlib representation is left to the solver. -/
noncomputable def exercise_4_10_T : Polynomial ℝ →ₗ[ℝ] Polynomial ℝ := sorry

theorem exercise_4_10 (p : Polynomial ℝ) (x : ℝ) (hx : x ≠ 3) :
    (exercise_4_10_T p).eval x = (p.eval x - p.eval 3) / (x - 3) := by
  sorry

/-- 4.11 If {lit}`p ∈ 𝒫(ℂ)`, define {lit}`q(z) = p(z) · p̄(z̄)`. Then
{lit}`q` is a polynomial with real coefficients. -/
theorem exercise_4_11 (p : Polynomial ℂ) :
    ∃ q : Polynomial ℝ, ∀ z : ℂ,
      p.eval z * starRingEnd ℂ (p.eval z) = (q.eval z.re : ℝ) := by
  sorry

/-- 4.12 -/
theorem exercise_4_12 {m : ℕ} (p : Polynomial.degreeLT ℂ (m + 1))
    (x : Fin (m + 1) → ℝ) (_hx : Function.Injective x)
    (_hpx : ∀ k, ((p : Polynomial ℂ).eval ((x k : ℝ) : ℂ)).im = 0) :
    ∀ k : ℕ, ((p : Polynomial ℂ).coeff k).im = 0 := by
  sorry

/-- 4.13 Let {lit}`U = {p · q : q ∈ 𝒫(F)}`. (a) {lit}`dim 𝒫(F)/U = deg p`.
(b) Find a basis. We state (a). -/
theorem exercise_4_13a (p : Polynomial F) (_hp : p ≠ 0) :
    finrank F (Polynomial F ⧸
      Submodule.span F (Set.range (fun q : Polynomial F => p * q))) =
      p.natDegree := by
  sorry

/-- 4.14 (a) The map {lit}`T(r, s) = rp + sq` from
{lit}`𝒫_{n−1}(ℂ) × 𝒫_{m−1}(ℂ) → 𝒫_{m+n−1}(ℂ)` is injective. -/
noncomputable def exercise_4_14_T (m n : ℕ) (p q : Polynomial ℂ) :
    Polynomial.degreeLT ℂ n × Polynomial.degreeLT ℂ m →ₗ[ℂ]
      Polynomial.degreeLT ℂ (m + n) := sorry

theorem exercise_4_14a (p q : Polynomial ℂ) (_hp : ¬ p.IsRoot 0)
    (_hq : ¬ q.IsRoot 0) (_hpq : ∀ z, ¬ (p.IsRoot z ∧ q.IsRoot z))
    (m n : ℕ) (_hm : 0 < m) (_hn : 0 < n)
    (_hpdeg : p.natDegree = m) (_hqdeg : q.natDegree = n) :
    Function.Injective (exercise_4_14_T m n p q) := by
  sorry

/-- 4.14 (b) The same map is surjective. -/
theorem exercise_4_14b (p q : Polynomial ℂ) (_hp : ¬ p.IsRoot 0)
    (_hq : ¬ q.IsRoot 0) (_hpq : ∀ z, ¬ (p.IsRoot z ∧ q.IsRoot z))
    (m n : ℕ) (_hm : 0 < m) (_hn : 0 < n)
    (_hpdeg : p.natDegree = m) (_hqdeg : q.natDegree = n) :
    Function.Surjective (exercise_4_14_T m n p q) := by
  sorry

/-- 4.14 (c) Bezout: there exist {lit}`r ∈ 𝒫_{n−1}(ℂ)`, {lit}`s ∈ 𝒫_{m−1}(ℂ)`
with {lit}`rp + sq = 1`. -/
theorem exercise_4_14c (p q : Polynomial ℂ) (_hp : p.natDegree ≠ 0)
    (_hq : q.natDegree ≠ 0) (_hpq : ∀ z, ¬ (p.IsRoot z ∧ q.IsRoot z)) :
    ∃ r s : Polynomial ℂ, r.natDegree < q.natDegree ∧
      s.natDegree < p.natDegree ∧ r * p + s * q = 1 := by
  sorry

end LADR.Chapter_4
