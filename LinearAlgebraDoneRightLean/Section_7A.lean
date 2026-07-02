import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Symmetric
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.LinearAlgebra.Matrix.ToLin
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

/-- {lit}`T` is normal iff its adjoint commutes with it (in composition form). -/
theorem normal_iff_comp (T : V →ₗ[𝕜] V) :
    IsStarNormal T ↔ LinearMap.adjoint T ∘ₗ T = T ∘ₗ LinearMap.adjoint T := by
  rw [isStarNormal_iff, LinearMap.star_eq_adjoint, ← Module.End.mul_eq_comp,
    ← Module.End.mul_eq_comp]
  exact commute_iff_eq _ _

/-- The commutator {lit}`T* T − T T*` is self-adjoint. -/
theorem comm_symmetric (T : V →ₗ[𝕜] V) :
    (LinearMap.adjoint T ∘ₗ T - T ∘ₗ LinearMap.adjoint T).IsSymmetric := by
  refine (LinearMap.isSymmetric_iff_isSelfAdjoint _).mpr ?_
  rw [_root_.isSelfAdjoint_iff, LinearMap.star_eq_adjoint]
  simp only [map_sub, LinearMap.adjoint_comp, LinearMap.adjoint_adjoint]

/-- 7.20 {lit}`T` is normal if and only if {lit}`‖Tv‖ = ‖T*v‖` for every {lit}`v`. -/
theorem normal_iff_norm (T : V →ₗ[𝕜] V) :
    IsStarNormal T ↔ ∀ v, ‖T v‖ = ‖LinearMap.adjoint T v‖ := by
  have key : ∀ v, ⟪(LinearMap.adjoint T ∘ₗ T - T ∘ₗ LinearMap.adjoint T) v, v⟫_𝕜
      = (‖T v‖ : 𝕜) ^ 2 - (‖LinearMap.adjoint T v‖ : 𝕜) ^ 2 := by
    intro v
    have e2 : ⟪T (LinearMap.adjoint T v), v⟫_𝕜 = (‖LinearMap.adjoint T v‖ : 𝕜) ^ 2 := by
      rw [← LinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K]
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, inner_sub_left,
      LinearMap.adjoint_inner_left, inner_self_eq_norm_sq_to_K, e2]
  rw [normal_iff_comp, ← sub_eq_zero, ← (comm_symmetric T).inner_map_self_eq_zero]
  constructor
  · intro h v
    have hk := key v
    rw [h v] at hk
    have h4 : (‖T v‖ : 𝕜) ^ 2 = (‖LinearMap.adjoint T v‖ : 𝕜) ^ 2 := sub_eq_zero.mp hk.symm
    have h3 : ‖T v‖ ^ 2 = ‖LinearMap.adjoint T v‖ ^ 2 := by exact_mod_cast h4
    rw [← Real.sqrt_sq (norm_nonneg (T v)),
      ← Real.sqrt_sq (norm_nonneg (LinearMap.adjoint T v)), h3]
  · intro h v
    rw [key v, h v, sub_self]

/-! 7.21 Range, null space, and eigenvectors of a normal operator -/

/-- (a) {lit}`null T = null T*`. -/
theorem ker_eq_ker_adjoint {T : V →ₗ[𝕜] V} (hT : IsStarNormal T) :
    LinearMap.ker T = LinearMap.ker (LinearMap.adjoint T) := by
  ext v
  rw [LinearMap.mem_ker, LinearMap.mem_ker, ← norm_eq_zero,
    ← norm_eq_zero (a := LinearMap.adjoint T v), (normal_iff_norm T).mp hT v]

/-- (b) {lit}`range T = range T*`. -/
theorem range_eq_range_adjoint {T : V →ₗ[𝕜] V} (hT : IsStarNormal T) :
    LinearMap.range T = LinearMap.range (LinearMap.adjoint T) := by
  have h2 : (LinearMap.range T)ᗮ = (LinearMap.range (LinearMap.adjoint T))ᗮ := by
    rw [← ker_adjoint, ← ker_adjoint, LinearMap.adjoint_adjoint, ← ker_eq_ker_adjoint hT]
  rw [← Submodule.orthogonal_orthogonal (LinearMap.range T), h2,
    Submodule.orthogonal_orthogonal]

/-- (c) {lit}`V = null T ⊕ range T`. -/
theorem isCompl_ker_range {T : V →ₗ[𝕜] V} (hT : IsStarNormal T) :
    IsCompl (LinearMap.ker T) (LinearMap.range T) := by
  have h1 : (LinearMap.range T)ᗮ = LinearMap.ker T := by
    rw [← ker_adjoint, ← ker_eq_ker_adjoint hT]
  have := (LinearMap.range T).isCompl_orthogonal_of_hasOrthogonalProjection
  rw [h1] at this
  exact this.symm

/-- The adjoint of the identity is the identity. -/
theorem adjoint_one : LinearMap.adjoint (1 : V →ₗ[𝕜] V) = 1 := by
  rw [Module.End.one_eq_id, LinearMap.adjoint_id]

/-- (d) {lit}`T − λI` is normal for every {lit}`λ`. -/
theorem sub_smul_normal {T : V →ₗ[𝕜] V} (hT : IsStarNormal T) (μ : 𝕜) :
    IsStarNormal (T - μ • (1 : V →ₗ[𝕜] V)) := by
  have hstar : star (T - μ • (1 : V →ₗ[𝕜] V)) = star T - conj μ • 1 := by
    rw [LinearMap.star_eq_adjoint, LinearMap.star_eq_adjoint, map_sub,
      LinearEquiv.map_smulₛₗ, adjoint_one]
  refine ⟨?_⟩
  rw [hstar]
  refine Commute.sub_right
    (Commute.sub_left hT.star_comm_self ((Commute.one_left T).smul_left (conj μ))) ?_
  exact ((Commute.one_left (star T - conj μ • (1 : V →ₗ[𝕜] V))).smul_left μ).symm

/-- (e) For normal {lit}`T`, {lit}`Tv = λv ⟺ T*v = conj λ · v`. -/
theorem eigenvector_adjoint {T : V →ₗ[𝕜] V} (hT : IsStarNormal T) (v : V) (μ : 𝕜) :
    T v = μ • v ↔ LinearMap.adjoint T v = (conj μ) • v := by
  have hnorm := (normal_iff_norm _).mp (sub_smul_normal hT μ) v
  have hadj : LinearMap.adjoint (T - μ • (1 : V →ₗ[𝕜] V)) v
      = LinearMap.adjoint T v - (conj μ) • v := by
    rw [map_sub, LinearEquiv.map_smulₛₗ, adjoint_one]; simp [Module.End.one_apply]
  rw [hadj] at hnorm
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply] at hnorm
  constructor
  · intro h
    have h0 : T v - μ • v = 0 := by rw [h, sub_self]
    rw [h0, norm_zero, eq_comm, norm_eq_zero, sub_eq_zero] at hnorm
    exact hnorm
  · intro h
    have h0 : LinearMap.adjoint T v - (conj μ) • v = 0 := by rw [h, sub_self]
    rw [h0, norm_zero, norm_eq_zero, sub_eq_zero] at hnorm
    exact hnorm

/-! 7.22 Orthogonal eigenvectors for normal operators

Eigenvectors of a normal operator corresponding to distinct eigenvalues are
orthogonal. -/

theorem orthogonal_eigenvectors {T : V →ₗ[𝕜] V} (hT : IsStarNormal T)
    {α β : 𝕜} {u v : V} (hαβ : α ≠ β) (hu : T u = α • u) (hv : T v = β • v) :
    ⟪u, v⟫_𝕜 = 0 := by
  have hstar : LinearMap.adjoint T v = (conj β) • v := (eigenvector_adjoint hT v β).mp hv
  have h1 : conj α * ⟪u, v⟫_𝕜 = conj β * ⟪u, v⟫_𝕜 := by
    calc conj α * ⟪u, v⟫_𝕜 = ⟪α • u, v⟫_𝕜 := (inner_smul_left u v α).symm
    _ = ⟪T u, v⟫_𝕜 := by rw [hu]
    _ = ⟪u, LinearMap.adjoint T v⟫_𝕜 := by rw [LinearMap.adjoint_inner_right]
    _ = ⟪u, (conj β) • v⟫_𝕜 := by rw [hstar]
    _ = conj β * ⟪u, v⟫_𝕜 := inner_smul_right u v (conj β)
  have h2 : (conj α - conj β) * ⟪u, v⟫_𝕜 = 0 := by rw [sub_mul]; linear_combination h1
  rcases mul_eq_zero.mp h2 with h | h
  · exact absurd (RingHom.injective _ (sub_eq_zero.mp h)) hαβ
  · exact h

/-! 7.14 On a complex inner product space, {lit}`T` is self-adjoint iff
{lit}`⟨Tv, v⟩` is real for every {lit}`v`. -/

theorem isSymmetric_iff_inner_real {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] (T : V →ₗ[ℂ] V) :
    LinearMap.IsSymmetric T ↔ ∀ v, conj ⟪T v, v⟫_ℂ = ⟪T v, v⟫_ℂ :=
  LinearMap.isSymmetric_iff_inner_map_self_real T

/-! 7.16 A self-adjoint operator with {lit}`⟨Tv, v⟩ = 0` for all {lit}`v` is
{lit}`0` (over both {lit}`ℝ` and {lit}`ℂ`). -/

omit [FiniteDimensional 𝕜 V] in
theorem symmetric_inner_map_self_eq_zero {T : V →ₗ[𝕜] V}
    (hT : LinearMap.IsSymmetric T) : (∀ v, ⟪T v, v⟫_𝕜 = 0) ↔ T = 0 :=
  hT.inner_map_self_eq_zero

/-! 7.9 Matrix of {lit}`T*` equals the conjugate transpose of the matrix of
{lit}`T`, with respect to an orthonormal basis. -/

theorem toMatrix_adjoint_eq_conjTranspose {n : Type*} [Fintype n] [DecidableEq n]
    (b : OrthonormalBasis n 𝕜 V) (T : V →ₗ[𝕜] V) :
    LinearMap.toMatrix b.toBasis b.toBasis (LinearMap.adjoint T)
      = (LinearMap.toMatrix b.toBasis b.toBasis T).conjTranspose :=
  LinearMap.toMatrix_adjoint b b T

/-! 7.23 Over a complex inner product space, {lit}`T` is normal if and only if
{lit}`T = A + iB` for some commuting self-adjoint operators {lit}`A, B` (the real
and imaginary parts of {lit}`T`). -/

theorem normal_iff_real_imag {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (T : V →ₗ[ℂ] V) :
    IsStarNormal T ↔ ∃ A B : V →ₗ[ℂ] V, LinearMap.IsSymmetric A ∧
      LinearMap.IsSymmetric B ∧ A ∘ₗ B = B ∘ₗ A ∧ T = A + Complex.I • B := by
  constructor
  · intro hT
    set s := LinearMap.adjoint T with hs
    refine ⟨(2⁻¹ : ℂ) • (T + s), (Complex.I / 2) • (s - T), ?_, ?_, ?_, ?_⟩
    · rw [LinearMap.isSymmetric_iff_isSelfAdjoint, _root_.isSelfAdjoint_iff,
        LinearMap.star_eq_adjoint, LinearEquiv.map_smulₛₗ, map_add, hs,
        LinearMap.adjoint_adjoint, show conj (2⁻¹ : ℂ) = 2⁻¹ by rw [map_inv₀, map_ofNat]]
      module
    · rw [LinearMap.isSymmetric_iff_isSelfAdjoint, _root_.isSelfAdjoint_iff,
        LinearMap.star_eq_adjoint, LinearEquiv.map_smulₛₗ, map_sub, hs,
        LinearMap.adjoint_adjoint,
        show conj (Complex.I / 2) = -(Complex.I / 2) by
          norm_num [Complex.ext_iff, Complex.div_re, Complex.div_im, Complex.conj_re,
            Complex.conj_im]]
      module
    · have hident : ((2⁻¹ : ℂ) • (T + s)) ∘ₗ ((Complex.I / 2) • (s - T))
          - ((Complex.I / 2) • (s - T)) ∘ₗ ((2⁻¹ : ℂ) • (T + s))
          = (Complex.I / 2) • (T ∘ₗ s - s ∘ₗ T) := by
        ext x
        simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply,
          map_smul, map_add, map_sub, LinearMap.add_apply]
        module
      rw [← sub_eq_zero, hident, smul_eq_zero]
      right
      rw [sub_eq_zero]
      exact ((normal_iff_comp T).mp hT).symm
    · have hI : Complex.I * (Complex.I / 2) = -(2⁻¹ : ℂ) := by
        rw [mul_div_assoc', Complex.I_mul_I]; norm_num
      rw [smul_smul, hI]
      module
  · rintro ⟨A, B, hA, hB, hAB, rfl⟩
    have hadjA : LinearMap.adjoint A = A := by
      rw [← LinearMap.star_eq_adjoint]; exact (LinearMap.isSymmetric_iff_isSelfAdjoint A).mp hA
    have hadjB : LinearMap.adjoint B = B := by
      rw [← LinearMap.star_eq_adjoint]; exact (LinearMap.isSymmetric_iff_isSelfAdjoint B).mp hB
    rw [normal_iff_comp]
    have hadj : LinearMap.adjoint (A + Complex.I • B) = A - Complex.I • B := by
      rw [map_add, LinearEquiv.map_smulₛₗ, Complex.conj_I, hadjA, hadjB]; module
    rw [hadj]
    ext x
    have hc := LinearMap.congr_fun hAB x
    simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.sub_apply,
      LinearMap.smul_apply, map_add, map_sub, map_smul] at hc ⊢
    rw [hc]
    module

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
