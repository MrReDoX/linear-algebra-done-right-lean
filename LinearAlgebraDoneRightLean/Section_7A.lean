import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Linter.Style
import CompanionHelper

/-!
# Axler, *Linear Algebra Done Right* (4e) — Section 7A: Self-Adjoint and Normal Operators
-/

namespace LADR.Section_7A

open scoped InnerProductSpace RealInnerProductSpace ComplexConjugate
open Module (finrank)
open Module.End (HasEigenvalue HasEigenvector)

/-! From now on (Axler's standing assumption for Chapters 7–9) {lit}`V` and
{lit}`W` are finite-dimensional inner product spaces over {lit}`𝕜` ({lit}`ℝ` or
{lit}`ℂ`). Finite-dimensionality is what lets mathlib form the adjoint. -/

variable {𝕜 : Type*} [RCLike 𝕜]
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [FiniteDimensional 𝕜 V]
  {W : Type*} [NormedAddCommGroup W] [InnerProductSpace 𝕜 W] [FiniteDimensional 𝕜 W]

/-! # Adjoints -/

/-! 7.1 Definition: adjoint, {lit}`T*`

For {lit}`T ∈ ℒ(V, W)`, the adjoint {lit}`T*` is the unique map {lit}`W → V`
with {lit}`⟨Tv, w⟩ = ⟨v, T*w⟩`. This is mathlib's {name}`LinearMap.adjoint`; the
defining property is {name}`LinearMap.adjoint_inner_right`. -/

theorem adjoint_inner (T : V →ₗ[𝕜] W) (v : V) (w : W) :
    ⟪T v, w⟫_𝕜 = ⟪v, LinearMap.adjoint T w⟫_𝕜 :=
  (LinearMap.adjoint_inner_right T v w).symm

/-! 7.3 Example: for fixed {lit}`u ∈ V`, {lit}`x ∈ W`, the map {lit}`T v = ⟨v, u⟩ x`
has adjoint {lit}`T* w = ⟨w, x⟩ u`. -/

/-! 7.4 The adjoint of a linear map is a linear map: {lit}`T* ∈ ℒ(W, V)`. In
mathlib {name}`LinearMap.adjoint` is already a (conjugate-linear) isomorphism of
linear maps, so {lit}`T*` is a {lit}`LinearMap` by construction. -/

noncomputable example (T : V →ₗ[𝕜] W) : W →ₗ[𝕜] V := LinearMap.adjoint T

/-! 7.5 Properties of the adjoint -/

/-- (a) {lit}`(S + T)* = S* + T*`. -/
theorem adjoint_add (S T : V →ₗ[𝕜] W) :
    LinearMap.adjoint (S + T) = LinearMap.adjoint S + LinearMap.adjoint T :=
  map_add _ _ _

/-- (c) {lit}`(T*)* = T`. -/
theorem adjoint_adjoint (T : V →ₗ[𝕜] W) :
    LinearMap.adjoint (LinearMap.adjoint T) = T :=
  LinearMap.adjoint_adjoint T

/-- (d) {lit}`(ST)* = T* S*`. -/
theorem adjoint_comp {U : Type*} [NormedAddCommGroup U] [InnerProductSpace 𝕜 U]
    [FiniteDimensional 𝕜 U] (S : W →ₗ[𝕜] U) (T : V →ₗ[𝕜] W) :
    LinearMap.adjoint (S ∘ₗ T) = LinearMap.adjoint T ∘ₗ LinearMap.adjoint S :=
  LinearMap.adjoint_comp S T

/-- (e) {lit}`I* = I`. -/
theorem adjoint_id : LinearMap.adjoint (LinearMap.id : V →ₗ[𝕜] V) = LinearMap.id :=
  LinearMap.adjoint_id

/-! 7.6 Null space and range of {lit}`T*` -/

/-- (a) {lit}`null T* = (range T)⟂`. -/
theorem ker_adjoint (T : V →ₗ[𝕜] W) :
    LinearMap.ker (LinearMap.adjoint T) = (LinearMap.range T)ᗮ := by
  ext w
  rw [LinearMap.mem_ker, Submodule.mem_orthogonal]
  constructor
  · intro h u hu
    obtain ⟨v, rfl⟩ := hu
    rw [adjoint_inner, h, inner_zero_right]
  · intro h
    refine ext_inner_left 𝕜 fun v => ?_
    rw [inner_zero_right, ← adjoint_inner]
    exact h (T v) ⟨v, rfl⟩

/-! # Self-Adjoint Operators -/

/-! 7.10 Definition: self-adjoint

An operator {lit}`T ∈ ℒ(V)` is *self-adjoint* if {lit}`T = T*`. mathlib's
{name}`IsSelfAdjoint` (in the star ring {lit}`ℒ(V)`, whose star is the adjoint)
captures this; equivalently {name}`LinearMap.IsSymmetric`
({lit}`⟨Tv, w⟩ = ⟨v, Tw⟩`). -/

theorem isSelfAdjoint_iff (T : V →ₗ[𝕜] V) :
    LinearMap.IsSymmetric T ↔ LinearMap.adjoint T = T :=
  LinearMap.isSymmetric_iff_isSelfAdjoint T

omit [FiniteDimensional 𝕜 V] in
theorem isSymmetric_iff_inner (T : V →ₗ[𝕜] V) :
    LinearMap.IsSymmetric T ↔ ∀ v w, ⟪T v, w⟫_𝕜 = ⟪v, T w⟫_𝕜 :=
  Iff.rfl

/-! 7.12 Eigenvalues of self-adjoint operators are real. -/

omit [FiniteDimensional 𝕜 V] in
theorem eigenvalue_real (T : V →ₗ[𝕜] V) (hT : LinearMap.IsSymmetric T) {μ : 𝕜}
    (hμ : HasEigenvalue T μ) : conj μ = μ :=
  hT.conj_eigenvalue_eq_self hμ

/-! 7.13 {lit}`⟨Tv, v⟩ = 0` for all {lit}`v` iff {lit}`T = 0` (over {lit}`ℂ`). -/

theorem inner_map_self_eq_zero_iff {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] (T : V →ₗ[ℂ] V) :
    (∀ v, ⟪T v, v⟫_ℂ = 0) ↔ T = 0 :=
  inner_map_self_eq_zero T

/-! # Normal Operators -/

/-! 7.18 Definition: normal

An operator is *normal* if it commutes with its adjoint: {lit}`T T* = T* T`.
This is mathlib's {name}`IsStarNormal` (the star on {lit}`ℒ(V)` being the
adjoint, so {lit}`star T = T*`). -/

example (T : V →ₗ[𝕜] V) : IsStarNormal T ↔ Commute (star T) T :=
  ⟨fun h => h.star_comm_self, fun h => ⟨h⟩⟩

/-- Every self-adjoint operator is normal. -/
theorem symmetric_isStarNormal {T : V →ₗ[𝕜] V} (hT : LinearMap.IsSymmetric T) :
    IsStarNormal T := by
  have h : IsSelfAdjoint T := by
    show star T = T
    rw [LinearMap.star_eq_adjoint]
    exact (isSelfAdjoint_iff T).mp hT
  exact h.isStarNormal

/-! 7.9 (matrix of {lit}`T*` is the conjugate transpose in an orthonormal basis),
7.14 / 7.16 ({lit}`⟨Tv, v⟩` real / zero characterizations of self-adjointness),
7.20 (normal ⟺ {lit}`‖Tv‖ = ‖T*v‖`), 7.21 (null space / range / shared
eigenvectors of a normal operator), 7.22 (orthogonal eigenvectors), and 7.23
(normal ⟺ commuting real and imaginary parts) are not developed here; their
formalizations are deferred. mathlib provides several ingredients — e.g.
{lit}`IsStarNormal.ker_adjoint_eq_ker` for 7.21(a). -/

/-! # Exercises 7A -/

/-- 7A.2 {lit}`T = 0 ⟺ T* = 0 ⟺ T*T = 0 ⟺ TT* = 0`. -/
theorem exercise_7A_2 (T : V →ₗ[𝕜] W) :
    (T = 0 ↔ LinearMap.adjoint T = 0) ∧
    (T = 0 ↔ LinearMap.adjoint T ∘ₗ T = 0) := by
  sorry

/-- 7A.3 {lit}`λ` is an eigenvalue of {lit}`T` iff {lit}`conj λ` is an eigenvalue
of {lit}`T*`. -/
theorem exercise_7A_3 (T : V →ₗ[𝕜] V) (μ : 𝕜) :
    HasEigenvalue T μ ↔ HasEigenvalue (LinearMap.adjoint T) (conj μ) := by
  sorry

/-- 7A.4 {lit}`U` is invariant under {lit}`T` iff {lit}`U⟂` is invariant under
{lit}`T*`. -/
theorem exercise_7A_4 (T : V →ₗ[𝕜] V) (U : Submodule 𝕜 V) :
    (∀ u ∈ U, T u ∈ U) ↔ (∀ w ∈ Uᗮ, LinearMap.adjoint T w ∈ Uᗮ) := by
  sorry

/-- 7A.9 The product of two self-adjoint operators is self-adjoint iff they
commute. -/
theorem exercise_7A_9 (S T : V →ₗ[𝕜] V) (hS : LinearMap.IsSymmetric S)
    (hT : LinearMap.IsSymmetric T) :
    LinearMap.IsSymmetric (S ∘ₗ T) ↔ S ∘ₗ T = T ∘ₗ S := by
  sorry

/-- 7A.15 (a) For invertible {lit}`T`, {lit}`T` is self-adjoint iff {lit}`T⁻¹` is
self-adjoint. -/
theorem exercise_7A_15a (T : V ≃ₗ[𝕜] V) :
    LinearMap.IsSymmetric (T : V →ₗ[𝕜] V) ↔
      LinearMap.IsSymmetric (T.symm : V →ₗ[𝕜] V) := by
  sorry

/-- 7A.19 If {lit}`‖T*v‖ ≤ ‖Tv‖` for every {lit}`v`, then {lit}`T` is normal. -/
theorem exercise_7A_19 (T : V →ₗ[𝕜] V)
    (h : ∀ v, ‖LinearMap.adjoint T v‖ ≤ ‖T v‖) : IsStarNormal T := by
  sorry

/-- 7A.23 If {lit}`T` is normal, {lit}`‖v‖ = ‖w‖ = 2`, {lit}`Tv = 3v`,
{lit}`Tw = 4w`, then {lit}`‖T(v + w)‖ = 10`. -/
theorem exercise_7A_23 {T : V →ₗ[𝕜] V} (hT : IsStarNormal T) {v w : V}
    (hv : ‖v‖ = 2) (hw : ‖w‖ = 2) (hTv : T v = (3 : 𝕜) • v) (hTw : T w = (4 : 𝕜) • w) :
    ‖T (v + w)‖ = 10 := by
  sorry

/-- 7A.27 If {lit}`T` is normal, then {lit}`null Tᵏ = null T` and
{lit}`range Tᵏ = range T` for every positive integer {lit}`k`. -/
theorem exercise_7A_27 {T : V →ₗ[𝕜] V} (hT : IsStarNormal T) (k : ℕ) (hk : 0 < k) :
    LinearMap.ker (T ^ k) = LinearMap.ker T ∧
      LinearMap.range (T ^ k) = LinearMap.range T := by
  sorry

end LADR.Section_7A
