import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Linter.Style
import CompanionHelper

/-!
# Axler, *Linear Algebra Done Right* (4e) — Section 6C: Orthogonal Complements and Minimization Problems
-/

namespace LADR.Section_6C

open scoped InnerProductSpace RealInnerProductSpace ComplexConjugate
open Module (finrank)

variable {𝕜 : Type*} [RCLike 𝕜]
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]

/-! # Orthogonal Complements -/

/-! 6.46 Definition: orthogonal complement, {lit}`U⟂`

The orthogonal complement of a subset {lit}`U` of {lit}`V` is the set of all
vectors orthogonal to every vector in {lit}`U`. For a subspace {lit}`U`, this is
mathlib's {name}`Submodule.orthogonal`, written {lit}`Uᗮ`. -/

example (U : Submodule 𝕜 V) (v : V) : v ∈ Uᗮ ↔ ∀ u ∈ U, ⟪u, v⟫_𝕜 = 0 :=
  Submodule.mem_orthogonal U v

/-! 6.48 Properties of orthogonal complement -/

/-- (a) {lit}`U⟂` is a subspace of {lit}`V` — in mathlib it is by construction a
{name}`Submodule`. -/
example (U : Submodule 𝕜 V) : Submodule 𝕜 V := Uᗮ

/-- (b) {lit}`{0}⟂ = V`. -/
theorem bot_orthogonal : (⊥ : Submodule 𝕜 V)ᗮ = ⊤ := Submodule.bot_orthogonal_eq_top

/-- (c) {lit}`V⟂ = {0}`. -/
theorem top_orthogonal : (⊤ : Submodule 𝕜 V)ᗮ = ⊥ := Submodule.top_orthogonal_eq_bot

/-- (d) {lit}`U ∩ U⟂ = {0}`. -/
theorem inf_orthogonal_eq_bot (U : Submodule 𝕜 V) : U ⊓ Uᗮ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  rintro x ⟨hxU, hxU'⟩
  exact inner_self_eq_zero.mp (hxU' x hxU)

/-- (e) If {lit}`G ⊆ H`, then {lit}`H⟂ ⊆ G⟂`. -/
theorem orthogonal_le {G H : Submodule 𝕜 V} (h : G ≤ H) : Hᗮ ≤ Gᗮ :=
  Submodule.orthogonal_le h

/-! 6.49 Direct sum of a subspace and its orthogonal complement

If {lit}`U` is a finite-dimensional subspace of {lit}`V`, then
{lit}`V = U ⊕ U⟂`. In mathlib this is {name}`IsCompl`. -/

theorem isCompl_orthogonal (U : Submodule 𝕜 V) [FiniteDimensional 𝕜 U] :
    IsCompl U Uᗮ :=
  U.isCompl_orthogonal_of_hasOrthogonalProjection

/-! 6.51 Dimension of orthogonal complement

If {lit}`V` is finite-dimensional, then {lit}`dim U⟂ = dim V − dim U`. -/

theorem finrank_orthogonal [FiniteDimensional 𝕜 V] (U : Submodule 𝕜 V) :
    finrank 𝕜 Uᗮ = finrank 𝕜 V - finrank 𝕜 U := by
  have := U.finrank_add_finrank_orthogonal (𝕜 := 𝕜)
  omega

/-! 6.52 Orthogonal complement of the orthogonal complement

If {lit}`U` is a finite-dimensional subspace, then {lit}`U = (U⟂)⟂`. -/

theorem orthogonal_orthogonal (U : Submodule 𝕜 V) [FiniteDimensional 𝕜 U] :
    Uᗮᗮ = U :=
  U.orthogonal_orthogonal

/-! 6.54 {lit}`U⟂ = {0} ⟺ U = V` (for a finite-dimensional subspace). -/

theorem orthogonal_eq_bot_iff (U : Submodule 𝕜 V) [FiniteDimensional 𝕜 U] :
    Uᗮ = ⊥ ↔ U = ⊤ :=
  U.orthogonal_eq_bot_iff

/-! # Orthogonal projection -/

/-! 6.55 Definition: orthogonal projection, {lit}`P_U`

For a finite-dimensional subspace {lit}`U`, the orthogonal projection of
{lit}`V` onto {lit}`U` sends {lit}`v = u + w` (with {lit}`u ∈ U`, {lit}`w ∈ U⟂`)
to {lit}`u`. mathlib's {name}`Submodule.starProjection` {lit}`U : V →L[𝕜] V` is
this operator {lit}`P_U`. -/

/-- {lit}`P_U v ∈ U` for every {lit}`v`. -/
example (U : Submodule 𝕜 V) [U.HasOrthogonalProjection] (v : V) :
    U.starProjection v ∈ U :=
  U.starProjection_apply_mem v

/-! 6.56 Example: orthogonal projection onto a one-dimensional subspace.
For {lit}`u ≠ 0` and {lit}`U = span(u)`, {lit}`P_U v = (⟨v, u⟩ / ‖u‖²) u`
(reading Axler's {lit}`⟨v, u⟩` as mathlib's {lit}`⟪u, v⟫`). -/

/-! 6.57 Properties of orthogonal projection {lit}`P_U`

Suppose {lit}`U` is a finite-dimensional subspace of {lit}`V`. -/

variable (U : Submodule 𝕜 V) [U.HasOrthogonalProjection]

/-- (b) {lit}`P_U u = u` for {lit}`u ∈ U`; and more precisely {lit}`P_U v = v ↔
v ∈ U`. -/
theorem starProjection_eq_self_iff (v : V) : U.starProjection v = v ↔ v ∈ U :=
  Submodule.starProjection_eq_self_iff

/-- (f) {lit}`v − P_U v ∈ U⟂` for every {lit}`v`. -/
theorem sub_starProjection_mem_orthogonal (v : V) :
    v - U.starProjection v ∈ Uᗮ :=
  U.sub_starProjection_mem_orthogonal v

/-- (g) {lit}`P_U² = P_U`. -/
theorem starProjection_idem : U.starProjection ∘L U.starProjection = U.starProjection :=
  (Submodule.isIdempotentElem_starProjection U)

/-- (h) {lit}`‖P_U v‖ ≤ ‖v‖` for every {lit}`v`. -/
theorem norm_starProjection_le (v : V) : ‖U.starProjection v‖ ≤ ‖v‖ :=
  U.norm_starProjection_apply_le v

variable {U}

/-- (c) {lit}`P_U w = 0` for {lit}`w ∈ U⟂`. -/
theorem starProjection_eq_zero_of_mem_orthogonal {w : V} (hw : w ∈ Uᗮ) :
    U.starProjection w = 0 := by
  have h1 : U.starProjection w ∈ U := U.starProjection_apply_mem w
  have h2 : U.starProjection w ∈ Uᗮ := by
    have heq : U.starProjection w = w - (w - U.starProjection w) := by abel
    rw [heq]
    exact Uᗮ.sub_mem hw (U.sub_starProjection_mem_orthogonal w)
  have hbot := inf_orthogonal_eq_bot U
  rw [Submodule.eq_bot_iff] at hbot
  exact hbot _ ⟨h1, h2⟩

/-! 6.61 Minimizing distance to a subspace

If {lit}`U` is finite-dimensional, {lit}`v ∈ V`, and {lit}`u ∈ U`, then
{lit}`‖v − P_U v‖ ≤ ‖v − u‖`, with equality iff {lit}`u = P_U v`. Thus
{lit}`P_U v` is the point of {lit}`U` closest to {lit}`v`. -/

theorem minimizing_distance (v : V) (u : V) (hu : u ∈ U) :
    ‖v - U.starProjection v‖ ≤ ‖v - u‖ := by
  have hmem : U.starProjection v - u ∈ U :=
    U.sub_mem (U.starProjection_apply_mem v) hu
  have horth : ⟪v - U.starProjection v, U.starProjection v - u⟫_𝕜 = 0 :=
    (Submodule.mem_orthogonal' U _).mp (U.sub_starProjection_mem_orthogonal v) _ hmem
  have hpyth : ‖v - u‖ ^ 2 =
      ‖v - U.starProjection v‖ ^ 2 + ‖U.starProjection v - u‖ ^ 2 := by
    have hsum : v - u = (v - U.starProjection v) + (U.starProjection v - u) := by abel
    rw [hsum]; simp only [pow_two]
    exact norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horth
  nlinarith [norm_nonneg (v - U.starProjection v), norm_nonneg (v - u),
    sq_nonneg ‖U.starProjection v - u‖, hpyth]

/-! 6.58 Riesz representation theorem, revisited.

Axler gives a second proof of the Riesz representation theorem using orthogonal
complements (6.58); the theorem itself is
{lit}`LADR.Section_6B.riesz_representation`. -/

/-! # Pseudoinverse -/

section Pseudoinverse

variable [FiniteDimensional 𝕜 V]
  {W : Type*} [NormedAddCommGroup W] [InnerProductSpace 𝕜 W] [FiniteDimensional 𝕜 W]

/-! 6.67 The restriction of {lit}`T` to {lit}`(null T)⟂` is an injective map of
{lit}`(null T)⟂` onto {lit}`range T`. -/

/-- {lit}`T` restricted to {lit}`(null T)⟂`, with codomain {lit}`range T`. -/
noncomputable def restr (T : V →ₗ[𝕜] W) : (Submodule.orthogonal (LinearMap.ker T)) →ₗ[𝕜] (LinearMap.range T) :=
  LinearMap.codRestrict (LinearMap.range T) (T ∘ₗ (Submodule.orthogonal (LinearMap.ker T)).subtype)
    (fun x => ⟨x, rfl⟩)

@[simp] theorem restr_coe (T : V →ₗ[𝕜] W) (x : (Submodule.orthogonal (LinearMap.ker T))) :
    (restr T x : W) = T (x : V) := rfl

theorem restr_injective (T : V →ₗ[𝕜] W) : Function.Injective (restr T) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro x hx
  rw [LinearMap.mem_ker] at hx
  have hx0 : T (x : V) = 0 := by have := congrArg (Subtype.val) hx; simpa using this
  have : (x : V) ∈ LinearMap.ker T ⊓ (Submodule.orthogonal (LinearMap.ker T)) := ⟨hx0, x.2⟩
  rw [Submodule.inf_orthogonal_eq_bot] at this
  ext; simpa using this

theorem restr_surjective (T : V →ₗ[𝕜] W) : Function.Surjective (restr T) := by
  rintro ⟨w, v, rfl⟩
  have hsup : (LinearMap.ker T) ⊔ (Submodule.orthogonal (LinearMap.ker T)) = ⊤ :=
    ((LinearMap.ker T).isCompl_orthogonal_of_hasOrthogonalProjection).sup_eq_top
  have hv : v ∈ (LinearMap.ker T) ⊔ (Submodule.orthogonal (LinearMap.ker T)) := hsup ▸ Submodule.mem_top
  rw [Submodule.mem_sup] at hv
  obtain ⟨u, hu, x, hx, rfl⟩ := hv
  refine ⟨⟨x, hx⟩, ?_⟩
  ext
  simp [LinearMap.mem_ker.mp hu]

/-- The isomorphism {lit}`(null T)⟂ ≃ range T` induced by {lit}`T`. -/
noncomputable def restrEquiv (T : V →ₗ[𝕜] W) : (Submodule.orthogonal (LinearMap.ker T)) ≃ₗ[𝕜] (LinearMap.range T) :=
  LinearEquiv.ofBijective (restr T) ⟨restr_injective T, restr_surjective T⟩

@[simp] theorem restrEquiv_coe (T : V →ₗ[𝕜] W) (x) : (restrEquiv T) x = restr T x := rfl

/-! 6.68 Definition: pseudoinverse, {lit}`T†`. For {lit}`T ∈ ℒ(V, W)`,
{lit}`T† w = (T|_(null T)⟂)⁻¹ (P_(range T) w)`. -/

/-- The pseudoinverse {lit}`T† ∈ ℒ(W, V)`. -/
noncomputable def pinv (T : V →ₗ[𝕜] W) : W →ₗ[𝕜] V :=
  (Submodule.orthogonal (LinearMap.ker T)).subtype ∘ₗ (restrEquiv T).symm.toLinearMap ∘ₗ
    ((LinearMap.range T).orthogonalProjection : W →L[𝕜] (LinearMap.range T))

/-- 6.69 (b) {lit}`T T† = P_(range T)`. -/
theorem T_comp_pinv (T : V →ₗ[𝕜] W) :
    T ∘ₗ pinv T = ((LinearMap.range T).starProjection : W →ₗ[𝕜] W) := by
  ext w
  simp only [LinearMap.comp_apply, pinv, LinearMap.coe_comp, Function.comp_apply,
    Submodule.coe_subtype, ContinuousLinearMap.coe_coe, LinearEquiv.coe_coe,
    LinearEquiv.coe_toLinearMap]
  rw [← restr_coe, ← restrEquiv_coe, LinearEquiv.apply_symm_apply,
    Submodule.starProjection_apply]

/-- 6.69 (c) {lit}`T† T = P_(null T)⟂`. -/
theorem pinv_comp_T (T : V →ₗ[𝕜] W) :
    pinv T ∘ₗ T = ((Submodule.orthogonal (LinearMap.ker T)).starProjection : V →ₗ[𝕜] V) := by
  ext v
  simp only [LinearMap.comp_apply, pinv, LinearMap.coe_comp, Function.comp_apply,
    Submodule.coe_subtype, ContinuousLinearMap.coe_coe, LinearEquiv.coe_coe,
    LinearEquiv.coe_toLinearMap]
  set x := (Submodule.orthogonal (LinearMap.ker T)).orthogonalProjection v with hx
  have hTx : T ((x : V)) = T v := by
    have hmem : v - (x : V) ∈ LinearMap.ker T := by
      have h1 : (x : V) = (Submodule.orthogonal (LinearMap.ker T)).starProjection v :=
        (Submodule.starProjection_apply _ v).symm
      rw [h1]
      have h2 := (LinearMap.ker T).starProjection_add_starProjection_orthogonal v
      have h3 : v - (Submodule.orthogonal (LinearMap.ker T)).starProjection v = (LinearMap.ker T).starProjection v := by
        rw [eq_comm, eq_sub_iff_add_eq]; exact h2
      rw [h3]; exact (LinearMap.ker T).starProjection_apply_mem v
    rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at hmem
    exact hmem.symm
  have hproj : (LinearMap.range T).orthogonalProjection (T v) = restr T x := by
    apply Subtype.ext
    rw [restr_coe, hTx]
    exact congrArg Subtype.val
      (Submodule.orthogonalProjection_mem_subspace_eq_self (⟨T v, ⟨v, rfl⟩⟩ : LinearMap.range T))
  rw [hproj, ← restrEquiv_coe, LinearEquiv.symm_apply_apply, Submodule.starProjection_apply]

/-! 6.69 (a) ({lit}`T† = T⁻¹` when {lit}`T` is invertible) and 6.70 (the
pseudoinverse gives the best approximate / minimal-norm solution) are not yet
developed here; their formalization is deferred. -/

end Pseudoinverse

/-! # Exercises 6C -/

/-- 6C.1 {lit}`{v₁, …, vₘ}⟂ = (span(v₁, …, vₘ))⟂`. -/
theorem exercise_6C_1 {m : ℕ} (v : Fin m → V) :
    (Submodule.span 𝕜 (Set.range v))ᗮ = (⨅ i, (𝕜 ∙ v i)ᗮ) := by
  sorry

/-- 6C.4 Converse to 6.30(b): if {lit}`‖eₖ‖ = 1` for each {lit}`k` and Parseval's
equality {lit}`‖v‖² = ∑ |⟨v, eₖ⟩|²` holds for all {lit}`v`, then {lit}`e₁, …, eₙ`
is an orthonormal basis. -/
theorem exercise_6C_4 [FiniteDimensional 𝕜 V] {n : ℕ} (e : Fin n → V)
    (hnorm : ∀ k, ‖e k‖ = 1)
    (hpar : ∀ v : V, ‖v‖ ^ 2 = ∑ k, ‖⟪e k, v⟫_𝕜‖ ^ 2) :
    Orthonormal 𝕜 e ∧ Submodule.span 𝕜 (Set.range e) = ⊤ := by
  sorry

/-- 6C.5 {lit}`P_(U⟂) = I − P_U`. -/
theorem exercise_6C_5 (U : Submodule 𝕜 V) [FiniteDimensional 𝕜 U] :
    Uᗮ.starProjection = 1 - U.starProjection := by
  sorry

/-- 6C.7 For finite-dimensional subspaces {lit}`X, Y`, {lit}`P_X P_Y = 0` iff
{lit}`⟨x, y⟩ = 0` for all {lit}`x ∈ X`, {lit}`y ∈ Y`. -/
theorem exercise_6C_7 (X Y : Submodule 𝕜 V) [FiniteDimensional 𝕜 X]
    [FiniteDimensional 𝕜 Y] :
    X.starProjection ∘L Y.starProjection = 0 ↔
      ∀ x ∈ X, ∀ y ∈ Y, ⟪x, y⟫_𝕜 = 0 := by
  sorry

/-- 6C.8 With {lit}`φ(u) = ⟨u, v⟩` on a finite-dimensional subspace {lit}`U` and
{lit}`w ∈ U` the Riesz vector, {lit}`w = P_U v`. -/
theorem exercise_6C_8 (U : Submodule 𝕜 V) [FiniteDimensional 𝕜 U] (v : V)
    (w : U) (hw : ∀ u : U, ⟪(u : V), v⟫_𝕜 = ⟪(u : V), (w : V)⟫_𝕜) :
    (w : V) = U.starProjection v := by
  sorry

/-- 6C.9 If {lit}`P² = P` and {lit}`null P ⟂ range P`, then {lit}`P = P_U` for
some subspace {lit}`U`. -/
theorem exercise_6C_9 [FiniteDimensional 𝕜 V] (P : V →ₗ[𝕜] V) (hP : P ∘ₗ P = P)
    (horth : ∀ x ∈ LinearMap.ker P, ∀ y ∈ LinearMap.range P, ⟪x, y⟫_𝕜 = 0) :
    ∃ (U : Submodule 𝕜 V) (_ : U.HasOrthogonalProjection),
      (U.starProjection : V →ₗ[𝕜] V) = P := by
  sorry

/-- 6C.11 For {lit}`T ∈ ℒ(V)` and a finite-dimensional subspace {lit}`U`,
{lit}`U` is invariant under {lit}`T` iff {lit}`P_U T P_U = T P_U`. -/
theorem exercise_6C_11 (T : V →ₗ[𝕜] V) (U : Submodule 𝕜 V)
    [FiniteDimensional 𝕜 U] :
    (∀ u ∈ U, T u ∈ U) ↔
      (U.starProjection : V →ₗ[𝕜] V) ∘ₗ T ∘ₗ (U.starProjection : V →ₗ[𝕜] V) =
        T ∘ₗ (U.starProjection : V →ₗ[𝕜] V) := by
  sorry

/-- 6C.12 For finite-dimensional {lit}`V`, {lit}`T ∈ ℒ(V)`, and a subspace
{lit}`U`: both {lit}`U` and {lit}`U⟂` are invariant under {lit}`T` iff
{lit}`P_U T = T P_U`. -/
theorem exercise_6C_12 [FiniteDimensional 𝕜 V] (T : V →ₗ[𝕜] V)
    (U : Submodule 𝕜 V) :
    ((∀ u ∈ U, T u ∈ U) ∧ ∀ w ∈ Uᗮ, T w ∈ Uᗮ) ↔
      (U.starProjection : V →ₗ[𝕜] V) ∘ₗ T = T ∘ₗ (U.starProjection : V →ₗ[𝕜] V) := by
  sorry

/-- 6C.15 In {lit}`ℝ⁴`, with {lit}`U = span((1,1,0,0), (1,1,1,2))`, find
{lit}`u ∈ U` minimizing {lit}`‖u − (1,2,3,4)‖`. The minimizer is {lit}`P_U` of
the target. -/
theorem exercise_6C_15 :
    ∃ u ∈ Submodule.span ℝ {(!₂[1, 1, 0, 0] : EuclideanSpace ℝ (Fin 4)),
        !₂[1, 1, 1, 2]},
      ∀ u' ∈ Submodule.span ℝ {(!₂[1, 1, 0, 0] : EuclideanSpace ℝ (Fin 4)),
        !₂[1, 1, 1, 2]},
        ‖u - !₂[1, 2, 3, 4]‖ ≤ ‖u' - !₂[1, 2, 3, 4]‖ := by
  sorry

end LADR.Section_6C
