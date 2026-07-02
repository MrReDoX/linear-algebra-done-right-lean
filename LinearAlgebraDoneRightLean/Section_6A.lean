import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.RCLike.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Recall
import CompanionHelper

/-!
# Axler, *Linear Algebra Done Right* (4e) — Section 6A: Inner Products and Norms
-/

namespace LADR.Section_6A

/-! # The field and the inner product convention

Axler's inner product spaces are over {lit}`𝔽`, which is always {lit}`ℝ` or
{lit}`ℂ`. mathlib captures exactly "{lit}`ℝ` or {lit}`ℂ`" with the typeclass
{name}`RCLike`, so throughout this chapter our scalar field is {lit}`𝕜` with
{lit}`[RCLike 𝕜]`. An inner product space is {name}`InnerProductSpace`, built on
top of a {name}`NormedAddCommGroup` (the norm and the inner product are packaged
together — see 6.7). The inner product {lit}`⟨u, v⟩` is written {lit}`⟪u, v⟫_𝕜`
(after {lit}`open scoped InnerProductSpace`), and {name}`inner` is the underlying
function.

**One important divergence.** Axler's inner product (6.2) is *linear in the first
slot* and conjugate-linear in the second. mathlib uses the opposite (physicists')
convention — see Axler's margin remark after 6.2 — so mathlib's inner product is
*conjugate-linear in the first slot* and linear in the second. Concretely,
mathlib's {lit}`⟪u, v⟫_𝕜` equals Axler's {lit}`⟨v, u⟩`. Every numbered *result*
in this section is symmetric under swapping the two slots (Pythagorean theorem,
Cauchy–Schwarz, the triangle and parallelogram identities, …), so the difference
never affects a statement; it only flips which slot carries the conjugate in the
homogeneity axiom. -/

open scoped InnerProductSpace RealInnerProductSpace ComplexConjugate

variable {𝕜 : Type*} [RCLike 𝕜]
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
  {W : Type*} [NormedAddCommGroup W] [InnerProductSpace 𝕜 W]

/-! # Inner Products -/

/-! 6.1 Definition: dot product

For {lit}`x, y ∈ ℝⁿ`, the dot product is {lit}`x · y = x₁y₁ + ⋯ + xₙyₙ`. In
mathlib {lit}`ℝⁿ` as an inner product space is {name}`EuclideanSpace` {lit}`ℝ`
{lit}`(Fin n)`, and its (real) inner product is exactly the dot product. -/

example {n : ℕ} (x y : EuclideanSpace ℝ (Fin n)) :
    ⟪x, y⟫_ℝ = ∑ i, x i * y i := by
  rw [PiLp.inner_apply]
  congr 1; ext i
  exact real_inner_comm (y i) (x i) ▸ rfl

/-- The dot product of a vector with itself is the square of its norm:
{lit}`x · x = ‖x‖²`. -/
example {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) : ⟪x, x⟫_ℝ = ‖x‖ ^ 2 :=
  real_inner_self_eq_norm_sq x

/-! 6.2 Definition: inner product

An inner product on {lit}`V` takes each ordered pair {lit}`(u, v)` to a scalar
{lit}`⟨u, v⟩ ∈ 𝕜` satisfying positivity, definiteness, additivity and
homogeneity in a slot, and conjugate symmetry. The following {lit}`recall`s are
mathlib's axioms; note (per the discussion above) that the additivity and
homogeneity axioms live in the *first* slot in Axler and in whichever slot we
name below in mathlib. -/

/-- Positivity: {lit}`⟨v, v⟩ ≥ 0` (a real, nonnegative number). -/
recall inner_self_nonneg {𝕜 : Type*} {E : Type*} [RCLike 𝕜]
    [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E] {x : E} :
    0 ≤ RCLike.re ⟪x, x⟫_𝕜

/-- Definiteness: {lit}`⟨v, v⟩ = 0` if and only if {lit}`v = 0`. -/
recall inner_self_eq_zero {𝕜 : Type*} {E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] {x : E} :
    ⟪x, x⟫_𝕜 = 0 ↔ x = 0

/-- Additivity (in mathlib's first slot):
{lit}`⟨u + v, w⟩ = ⟨u, w⟩ + ⟨v, w⟩`. -/
recall inner_add_left {𝕜 : Type*} {E : Type*} [RCLike 𝕜]
    [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E] (x y z : E) :
    ⟪x + y, z⟫_𝕜 = ⟪x, z⟫_𝕜 + ⟪y, z⟫_𝕜

/-- Conjugate homogeneity (in mathlib's first slot):
{lit}`⟨λu, v⟩ = λ̄ ⟨u, v⟩`. In Axler's convention the conjugate is instead in the
second slot, and the first slot is genuinely homogeneous. -/
recall inner_smul_left {𝕜 : Type*} {E : Type*} [RCLike 𝕜]
    [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E] (x y : E) (r : 𝕜) :
    ⟪r • x, y⟫_𝕜 = (starRingEnd 𝕜) r * ⟪x, y⟫_𝕜

/-- Conjugate symmetry: {lit}`⟨u, v⟩ = conj ⟨v, u⟩`. -/
example (u v : V) : ⟪u, v⟫_𝕜 = conj ⟪v, u⟫_𝕜 := (inner_conj_symm u v).symm

/-! 6.3 Example: inner products

(a) The Euclidean inner product on {lit}`𝔽ⁿ`, {name}`EuclideanSpace`, is the one
    used above. -/

example {n : ℕ} (w z : EuclideanSpace 𝕜 (Fin n)) :
    ⟪w, z⟫_𝕜 = ∑ i, conj (w i) * z i := by
  rw [PiLp.inner_apply]
  congr 1; ext i
  rw [RCLike.inner_apply']

/-! (b)–(e) The weighted inner product on {lit}`𝔽ⁿ` and the inner products on
spaces of functions built from integrals are not developed here; the integral
examples live outside the linear-algebra core that this companion tracks. -/

/-! 6.4 Definition: inner product space

An inner product space is a vector space together with an inner product; this is
mathlib's {name}`InnerProductSpace`. -/

example : InnerProductSpace 𝕜 V := inferInstance

/-! 6.5 Notation: {lit}`V`, {lit}`W`

For the rest of this chapter and the next, {lit}`V` and {lit}`W` denote inner
product spaces over {lit}`𝕜` — the {lit}`variable` declarations above. -/

/-! 6.6 Basic properties of an inner product -/

/-- (a) For each fixed {lit}`v`, the map {lit}`u ↦ ⟨u, v⟩` is linear. In mathlib's
convention it is the *second* slot that is linear, so we record the linear map
{lit}`u ↦ ⟨v, u⟩`, namely {name}`innerSL`. -/
example (v : V) (u : V) : innerSL 𝕜 v u = ⟪v, u⟫_𝕜 := rfl

example (v : V) (u₁ u₂ : V) : ⟪v, u₁ + u₂⟫_𝕜 = ⟪v, u₁⟫_𝕜 + ⟪v, u₂⟫_𝕜 :=
  inner_add_right v u₁ u₂

example (v u : V) (r : 𝕜) : ⟪v, r • u⟫_𝕜 = r * ⟪v, u⟫_𝕜 := inner_smul_right v u r

/-- (b) {lit}`⟨0, v⟩ = 0`. -/
example (v : V) : ⟪(0 : V), v⟫_𝕜 = 0 := inner_zero_left v

/-- (c) {lit}`⟨v, 0⟩ = 0`. -/
example (v : V) : ⟪v, (0 : V)⟫_𝕜 = 0 := inner_zero_right v

/-- (d) {lit}`⟨u, v + w⟩ = ⟨u, v⟩ + ⟨u, w⟩`. -/
example (u v w : V) : ⟪u, v + w⟫_𝕜 = ⟪u, v⟫_𝕜 + ⟪u, w⟫_𝕜 := inner_add_right u v w

/-- (e) {lit}`⟨u, λv⟩ = λ⟨u, v⟩` (with the conjugate on the other slot in Axler's
convention). -/
example (u v : V) (r : 𝕜) : ⟪u, r • v⟫_𝕜 = r * ⟪u, v⟫_𝕜 := inner_smul_right u v r

/-! # Norms -/

/-! 6.7 Definition: norm, {lit}`‖v‖`

The norm of {lit}`v` is {lit}`‖v‖ = √⟨v, v⟩`. In mathlib the norm comes first (as
part of the {name}`NormedAddCommGroup`) and the inner product is compatible with
it; this compatibility is exactly Axler's defining equation. -/

example (v : V) : ‖v‖ = Real.sqrt (RCLike.re ⟪v, v⟫_𝕜) :=
  norm_eq_sqrt_re_inner (𝕜 := 𝕜) v

/-- Over a real inner product space the conjugate/real-part bookkeeping drops
away: {lit}`‖v‖ = √⟨v, v⟩`. -/
example (w : W) : ⟪w, w⟫_𝕜 = (‖w‖ : 𝕜) ^ 2 := inner_self_eq_norm_sq_to_K w

/-! 6.8 Example: norms

(a) {lit}`‖(z₁, …, zₙ)‖ = √(|z₁|² + ⋯ + |zₙ|²)` for {lit}`𝔽ⁿ` with the Euclidean
inner product. -/

example {n : ℕ} (z : EuclideanSpace 𝕜 (Fin n)) :
    ‖z‖ = Real.sqrt (∑ i, ‖z i‖ ^ 2) := by
  rw [EuclideanSpace.norm_eq]

/-! 6.9 Basic properties of the norm

Suppose {lit}`v ∈ V`. -/

/-- (a) {lit}`‖v‖ = 0` if and only if {lit}`v = 0`. -/
example (v : V) : ‖v‖ = 0 ↔ v = 0 := norm_eq_zero

/-- (b) {lit}`‖λv‖ = |λ| ‖v‖` for all {lit}`λ ∈ 𝕜`. -/
example (v : V) (r : 𝕜) : ‖r • v‖ = ‖r‖ * ‖v‖ := norm_smul r v

/-! 6.10 Definition: orthogonal

Two vectors {lit}`u, v ∈ V` are *orthogonal* if {lit}`⟨u, v⟩ = 0`. -/

/-- {lit}`u` and {lit}`v` are orthogonal. -/
def Orthogonal (u v : V) : Prop := ⟪u, v⟫_𝕜 = 0

/-- Orthogonality does not depend on the order of the two vectors. -/
theorem orthogonal_comm (u v : V) : Orthogonal (𝕜 := 𝕜) u v ↔ Orthogonal (𝕜 := 𝕜) v u :=
  inner_eq_zero_symm

/-! 6.11 Orthogonality and 0 -/

/-- (a) {lit}`0` is orthogonal to every vector in {lit}`V`. -/
theorem zero_orthogonal (v : V) : Orthogonal (𝕜 := 𝕜) 0 v := inner_zero_left v

/-- (b) {lit}`0` is the only vector in {lit}`V` orthogonal to itself. -/
theorem orthogonal_self_iff (v : V) : Orthogonal (𝕜 := 𝕜) v v ↔ v = 0 :=
  inner_self_eq_zero

/-! 6.12 Pythagorean theorem

If {lit}`u` and {lit}`v` are orthogonal, then {lit}`‖u + v‖² = ‖u‖² + ‖v‖²`. -/

theorem pythagorean (u v : V) (h : Orthogonal (𝕜 := 𝕜) u v) :
    ‖u + v‖ ^ 2 = ‖u‖ ^ 2 + ‖v‖ ^ 2 := by
  have := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero u v h
  rw [sq, sq, sq]; linarith

/-! 6.13 An orthogonal decomposition

Suppose {lit}`u, v ∈ V` with {lit}`v ≠ 0`. Writing {lit}`c = ⟨u, v⟩ / ‖v‖²` and
{lit}`w = u − cv`, we get {lit}`u = cv + w` with {lit}`w` orthogonal to {lit}`v`.
(Again reading Axler's {lit}`⟨u, v⟩` as mathlib's {lit}`⟪v, u⟫`.) -/

theorem orthogonal_decomposition (u v : V) (hv : v ≠ 0) :
    ∃ (c : 𝕜) (w : V), u = c • v + w ∧ Orthogonal (𝕜 := 𝕜) v w := by
  have hvv : ⟪v, v⟫_𝕜 ≠ 0 := fun h => hv (inner_self_eq_zero.mp h)
  refine ⟨⟪v, u⟫_𝕜 / ⟪v, v⟫_𝕜, u - (⟪v, u⟫_𝕜 / ⟪v, v⟫_𝕜) • v, by abel, ?_⟩
  unfold Orthogonal
  rw [inner_sub_right, inner_smul_right, div_mul_cancel₀ _ hvv, sub_self]

/-! 6.14 Cauchy–Schwarz inequality

For {lit}`u, v ∈ V`, {lit}`|⟨u, v⟩| ≤ ‖u‖ ‖v‖`, with equality if and only if one
of {lit}`u, v` is a scalar multiple of the other. -/

theorem cauchy_schwarz (u v : V) : ‖⟪u, v⟫_𝕜‖ ≤ ‖u‖ * ‖v‖ := norm_inner_le_norm u v

/-- The equality case (stated, as in mathlib, for nonzero vectors; the case where
one vector is {lit}`0` makes both sides {lit}`0`). -/
theorem cauchy_schwarz_eq_iff {u v : V} (hu : u ≠ 0) (hv : v ≠ 0) :
    ‖⟪u, v⟫_𝕜‖ = ‖u‖ * ‖v‖ ↔ ∃ r : 𝕜, r ≠ 0 ∧ v = r • u :=
  norm_inner_eq_norm_iff hu hv

/-! 6.16 Example: Cauchy–Schwarz inequality

(a) {lit}`(x₁y₁ + ⋯ + xₙyₙ)² ≤ (x₁² + ⋯ + xₙ²)(y₁² + ⋯ + yₙ²)` for reals, from
applying 6.14 to {lit}`ℝⁿ`. -/

example {n : ℕ} (x y : EuclideanSpace ℝ (Fin n)) :
    (∑ i, x i * y i) ^ 2 ≤ (∑ i, x i ^ 2) * (∑ i, y i ^ 2) := by
  have hcs := cauchy_schwarz (𝕜 := ℝ) x y
  have hxy : ⟪x, y⟫_ℝ = ∑ i, x i * y i := by
    rw [PiLp.inner_apply]; congr 1; ext i; exact real_inner_comm (y i) (x i) ▸ rfl
  have hxx : ‖x‖ ^ 2 = ∑ i, x i ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, PiLp.inner_apply]
    congr 1; ext i; rw [real_inner_comm]; exact (real_inner_self_eq_norm_sq (x i)).trans (by
      rw [Real.norm_eq_abs, sq_abs])
  have hyy : ‖y‖ ^ 2 = ∑ i, y i ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, PiLp.inner_apply]
    congr 1; ext i; rw [real_inner_comm]; exact (real_inner_self_eq_norm_sq (y i)).trans (by
      rw [Real.norm_eq_abs, sq_abs])
  rw [hxy] at hcs
  have h2 : (∑ i, x i * y i) ^ 2 ≤ (‖x‖ * ‖y‖) ^ 2 := by
    rw [Real.norm_eq_abs] at hcs
    nlinarith [abs_nonneg (∑ i, x i * y i), sq_abs (∑ i, x i * y i)]
  rw [mul_pow, hxx, hyy] at h2
  exact h2

/-! 6.17 Triangle inequality

{lit}`‖u + v‖ ≤ ‖u‖ + ‖v‖`, with equality if and only if one of {lit}`u, v` is a
nonnegative real multiple of the other. -/

theorem triangle_inequality (u v : V) : ‖u + v‖ ≤ ‖u‖ + ‖v‖ := norm_add_le u v

/-! 6.21 Parallelogram equality

{lit}`‖u + v‖² + ‖u − v‖² = 2(‖u‖² + ‖v‖²)`. -/

theorem parallelogram {𝕜 : Type*} [RCLike 𝕜] {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace 𝕜 V] (u v : V) :
    ‖u + v‖ ^ 2 + ‖u - v‖ ^ 2 = 2 * (‖u‖ ^ 2 + ‖v‖ ^ 2) :=
  parallelogram_law_with_norm 𝕜 u v

/-! # Exercises 6A -/

/-- 6A.1 Prove or give a counterexample: if {lit}`v₁, …, vₘ ∈ V`, then
{lit}`∑ⱼ ∑ₖ ⟨vⱼ, vₖ⟩ ≥ 0`. -/
theorem exercise_6A_1 {m : ℕ} (v : Fin m → V) :
    0 ≤ RCLike.re (∑ j, ∑ k, ⟪v j, v k⟫_𝕜) := by
  sorry

/-- 6A.2 For {lit}`S ∈ ℒ(V)`, define {lit}`⟨u, v⟩₁ = ⟨Su, Sv⟩`. Then {lit}`⟨·, ·⟩₁`
is an inner product on {lit}`V` if and only if {lit}`S` is injective. (Here we
capture "is an inner product" by its definiteness clause, the only axiom that can
fail; the other axioms hold for any {lit}`S`.) -/
theorem exercise_6A_2 (S : V →ₗ[𝕜] V) :
    (∀ v : V, (⟪S v, S v⟫_𝕜 = 0 ↔ v = 0)) ↔ Function.Injective S := by
  sorry

/-- 6A.4 If {lit}`T ∈ ℒ(V)` satisfies {lit}`‖Tv‖ ≤ ‖v‖` for every {lit}`v`, then
{lit}`T − √2 I` is injective. -/
theorem exercise_6A_4 (T : V →ₗ[𝕜] V) (h : ∀ v : V, ‖T v‖ ≤ ‖v‖) :
    Function.Injective (T - (Real.sqrt 2 : 𝕜) • (LinearMap.id : V →ₗ[𝕜] V)) := by
  sorry

/-- 6A.5 (a) In a real inner product space, {lit}`⟨u + v, u − v⟩ = ‖u‖² − ‖v‖²`. -/
theorem exercise_6A_5a {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (u v : V) : ⟪u + v, u - v⟫_ℝ = ‖u‖ ^ 2 - ‖v‖ ^ 2 := by
  sorry

/-- 6A.5 (b) If {lit}`u, v` have the same norm, then {lit}`u + v` is orthogonal to
{lit}`u − v`. -/
theorem exercise_6A_5b {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (u v : V) (h : ‖u‖ = ‖v‖) : Orthogonal (𝕜 := ℝ) (u + v) (u - v) := by
  sorry

/-- 6A.6 {lit}`⟨u, v⟩ = 0` if and only if {lit}`‖u‖ ≤ ‖u + av‖` for all {lit}`a`. -/
theorem exercise_6A_6 (u v : V) :
    ⟪u, v⟫_𝕜 = 0 ↔ ∀ a : 𝕜, ‖u‖ ≤ ‖u + a • v‖ := by
  sorry

/-- 6A.7 {lit}`‖au + bv‖ = ‖bu + av‖` for all real {lit}`a, b` if and only if
{lit}`‖u‖ = ‖v‖`. -/
theorem exercise_6A_7 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (u v : V) :
    (∀ a b : ℝ, ‖a • u + b • v‖ = ‖b • u + a • v‖) ↔ ‖u‖ = ‖v‖ := by
  sorry

/-- 6A.8 If {lit}`a² + b² + c² + x² + y² ≤ 1`, then
{lit}`a + b + c + 4x + 9y ≤ 10`. -/
theorem exercise_6A_8 (a b c x y : ℝ) (h : a^2 + b^2 + c^2 + x^2 + y^2 ≤ 1) :
    a + b + c + 4*x + 9*y ≤ 10 := by
  sorry

/-- 6A.9 If {lit}`‖u‖ = ‖v‖ = 1` and {lit}`⟨u, v⟩ = 1`, then {lit}`u = v`. -/
theorem exercise_6A_9 (u v : V) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : ⟪u, v⟫_𝕜 = 1) :
    u = v := by
  sorry

/-- 6A.10 If {lit}`‖u‖ ≤ 1` and {lit}`‖v‖ ≤ 1`, then
{lit}`√(1 − ‖u‖²) √(1 − ‖v‖²) ≤ 1 − |⟨u, v⟩|`. -/
theorem exercise_6A_10 (u v : V) (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) :
    Real.sqrt (1 - ‖u‖ ^ 2) * Real.sqrt (1 - ‖v‖ ^ 2) ≤ 1 - ‖⟪u, v⟫_𝕜‖ := by
  sorry

/-- 6A.11 Find {lit}`u, v ∈ ℝ²` such that {lit}`u` is a scalar multiple of
{lit}`(1, 3)`, {lit}`v` is orthogonal to {lit}`(1, 3)`, and {lit}`(1, 2) = u + v`. -/
theorem exercise_6A_11 :
    ∃ u v : EuclideanSpace ℝ (Fin 2),
      (∃ c : ℝ, u = c • (!₂[1, 3] : EuclideanSpace ℝ (Fin 2))) ∧
      Orthogonal (𝕜 := ℝ) v (!₂[1, 3] : EuclideanSpace ℝ (Fin 2)) ∧
      (!₂[1, 2] : EuclideanSpace ℝ (Fin 2)) = u + v := by
  sorry

/-- 6A.12 (a) For positive {lit}`a, b, c, d`,
{lit}`(a + b + c + d)(1/a + 1/b + 1/c + 1/d) ≥ 16`. -/
theorem exercise_6A_12a (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : 0 < d) : 16 ≤ (a + b + c + d) * (1/a + 1/b + 1/c + 1/d) := by
  sorry

/-- 6A.13 The square of an average is at most the average of the squares. -/
theorem exercise_6A_13 {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) :
    ((∑ i, a i) / n) ^ 2 ≤ (∑ i, (a i) ^ 2) / n := by
  sorry

/-- 6A.14 For {lit}`v ≠ 0`, {lit}`v/‖v‖` is the unique closest element on the unit
sphere to {lit}`v`. -/
theorem exercise_6A_14 (v : V) (hv : v ≠ 0) (u : V) (hu : ‖u‖ = 1) :
    ‖v - (‖v‖⁻¹ : 𝕜) • v‖ ≤ ‖v - u‖ := by
  sorry

/-- 6A.17 {lit}`(∑ₖ aₖbₖ)² ≤ (∑ₖ k aₖ²)(∑ₖ bₖ²/k)` for reals. -/
theorem exercise_6A_17 {n : ℕ} (a b : Fin n → ℝ) :
    (∑ k : Fin n, a k * b k) ^ 2 ≤
      (∑ k : Fin n, ((k : ℝ) + 1) * a k ^ 2) *
        (∑ k : Fin n, b k ^ 2 / ((k : ℝ) + 1)) := by
  sorry

/-- 6A.19 If {lit}`v₁, …, vₙ` is a basis of {lit}`V`, {lit}`T ∈ ℒ(V)`, and
{lit}`λ` is an eigenvalue of {lit}`T`, then {lit}`|λ|² ≤ ∑ⱼ ∑ₖ |ℳ(T)ⱼ,ₖ|²`. -/
theorem exercise_6A_19 {n : ℕ} (b : Module.Basis (Fin n) 𝕜 V) (T : V →ₗ[𝕜] V)
    (lam : 𝕜) (h : ∃ v : V, v ≠ 0 ∧ T v = lam • v) :
    ‖lam‖ ^ 2 ≤ ∑ j, ∑ k, ‖LinearMap.toMatrix b b T j k‖ ^ 2 := by
  sorry

/-- 6A.20 Reverse triangle inequality: {lit}`| ‖u‖ − ‖v‖ | ≤ ‖u − v‖`. -/
@[avoiding abs_norm_sub_norm_le, norm_sub_norm_le]
theorem exercise_6A_20 (u v : V) : |‖u‖ - ‖v‖| ≤ ‖u - v‖ := by
  sorry

/-- 6A.21 If {lit}`‖u‖ = 3`, {lit}`‖u + v‖ = 4`, {lit}`‖u − v‖ = 6`, find
{lit}`‖v‖`. -/
theorem exercise_6A_21 (u v : V) (h1 : ‖u‖ = 3) (h2 : ‖u + v‖ = 4)
    (h3 : ‖u - v‖ = 6) : ‖v‖ = Real.sqrt (43 / 2) := by
  sorry

/-- 6A.22 {lit}`‖u + v‖ ‖u − v‖ ≤ ‖u‖² + ‖v‖²`. -/
theorem exercise_6A_22 (u v : V) : ‖u + v‖ * ‖u - v‖ ≤ ‖u‖ ^ 2 + ‖v‖ ^ 2 := by
  sorry

/-- 6A.23 If {lit}`‖vₖ‖ ≤ 1` for each {lit}`k`, then there exist signs
{lit}`aₖ ∈ {1, −1}` with {lit}`‖a₁v₁ + ⋯ + aₘvₘ‖ ≤ √m`. -/
theorem exercise_6A_23 {m : ℕ} (v : Fin m → V) (h : ∀ k, ‖v k‖ ≤ 1) :
    ∃ a : Fin m → 𝕜, (∀ k, a k = 1 ∨ a k = -1) ∧
      ‖∑ k, a k • v k‖ ≤ Real.sqrt m := by
  sorry

/-- 6A.24 Prove or give a counterexample: if {lit}`‖·‖` is the norm from an inner
product on {lit}`ℝ²`, then there is {lit}`(x, y)` with
{lit}`‖(x, y)‖ ≠ max{|x|, |y|}`. -/
theorem exercise_6A_24 :
    ∃ x y : ℝ, ‖(!₂[x, y] : EuclideanSpace ℝ (Fin 2))‖ ≠ max |x| |y| := by
  sorry

/-- 6A.26 In a real inner product space,
{lit}`⟨u, v⟩ = (‖u + v‖² − ‖u − v‖²)/4`. -/
theorem exercise_6A_26 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (u v : V) : ⟪u, v⟫_ℝ = (‖u + v‖ ^ 2 - ‖u - v‖ ^ 2) / 4 := by
  sorry

/-- 6A.29 If {lit}`V₁, …, Vₘ` are inner product spaces, the equation
{lit}`⟨(u₁, …), (v₁, …)⟩ = ⟨u₁, v₁⟩ + ⋯` defines an inner product on the product.
mathlib provides this via the {name}`PiLp` (ℓ²) structure; the exercise is to
verify the defining formula. -/
theorem exercise_6A_29 {m : ℕ} (E : Fin m → Type*)
    [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace 𝕜 (E i)]
    (u v : PiLp 2 E) : ⟪u, v⟫_𝕜 = ∑ i, ⟪u i, v i⟫_𝕜 := by
  sorry

end LADR.Section_6A
