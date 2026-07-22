import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Symmetric
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.Data.List.TFAE
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.RingTheory.Polynomial.Basic
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
has adjoint {lit}`T* w = ⟨w, x⟩ u` (reading Axler's {lit}`⟨v, u⟩` as {lit}`⟪u, v⟫`). -/

example (u x : V) (T : V →ₗ[𝕜] V) (hT : ∀ v, T v = ⟪u, v⟫_𝕜 • x) (w : V) :
    LinearMap.adjoint T w = ⟪x, w⟫_𝕜 • u := by
  refine ext_inner_left 𝕜 fun v => ?_
  rw [← adjoint_inner, hT, inner_smul_left, inner_smul_right, inner_conj_symm]
  ring

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

/-- 7A.1 For the forward shift {lit}`T(z₁, …, zₙ) = (0, z₁, …, zₙ₋₁)` on
{lit}`𝔽ⁿ`, the adjoint is the backward shift
{lit}`T*(z₁, …, zₙ) = (z₂, …, zₙ, 0)`. -/
theorem exercise_7A_1 {n : ℕ}
    (T : EuclideanSpace 𝕜 (Fin (n + 1)) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin (n + 1)))
    (hT : ∀ (z : EuclideanSpace 𝕜 (Fin (n + 1))) (i : Fin (n + 1)),
      T z i = Fin.cons (α := fun _ => 𝕜) 0 (Fin.init fun j => z j) i) :
    ∀ (z : EuclideanSpace 𝕜 (Fin (n + 1))) (i : Fin (n + 1)),
      LinearMap.adjoint T z i =
        Fin.snoc (α := fun _ => 𝕜) (Fin.tail fun j => z j) 0 i := by
  sorry

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

/-- 7A.5 {lit}`∑ ‖Teₖ‖² = ∑ ‖T*fⱼ‖²` for orthonormal bases {lit}`e` of {lit}`V`
and {lit}`f` of {lit}`W` — in particular the left sum is basis-independent. -/
theorem exercise_7A_5 {n m : ℕ} (T : V →ₗ[𝕜] W)
    (e : OrthonormalBasis (Fin n) 𝕜 V) (f : OrthonormalBasis (Fin m) 𝕜 W) :
    ∑ i, ‖T (e i)‖ ^ 2 = ∑ j, ‖LinearMap.adjoint T (f j)‖ ^ 2 := by
  sorry

/-- 7A.6 (a) {lit}`T` injective ⟺ {lit}`T*` surjective; (b) {lit}`T` surjective
⟺ {lit}`T*` injective. -/
theorem exercise_7A_6 (T : V →ₗ[𝕜] W) :
    (Function.Injective T ↔ Function.Surjective (LinearMap.adjoint T)) ∧
      (Function.Surjective T ↔ Function.Injective (LinearMap.adjoint T)) := by
  sorry

/-- 7A.7 (a) {lit}`dim null T* = dim null T + dim W − dim V`; (b)
{lit}`dim range T* = dim range T`. -/
theorem exercise_7A_7 (T : V →ₗ[𝕜] W) :
    finrank 𝕜 (LinearMap.ker (LinearMap.adjoint T)) =
        finrank 𝕜 (LinearMap.ker T) + finrank 𝕜 W - finrank 𝕜 V ∧
      finrank 𝕜 (LinearMap.range (LinearMap.adjoint T)) =
        finrank 𝕜 (LinearMap.range T) := by
  sorry

/-- 7A.8 The row rank of a matrix equals its column rank (via 7A.7(b)). -/
theorem exercise_7A_8 {m n : ℕ} (A : Matrix (Fin m) (Fin n) 𝕜) :
    A.transpose.rank = A.rank := by
  sorry

/-- 7A.9 The product of two self-adjoint operators is self-adjoint iff they
commute. -/
theorem exercise_7A_9 (S T : V →ₗ[𝕜] V) (hS : LinearMap.IsSymmetric S)
    (hT : LinearMap.IsSymmetric T) :
    LinearMap.IsSymmetric (S ∘ₗ T) ↔ S ∘ₗ T = T ∘ₗ S := by
  sorry

/-- 7A.10 For {lit}`𝔽 = ℂ`, {lit}`T` is self-adjoint iff {lit}`⟨Tv, v⟩ = ⟨T*v, v⟩`
for all {lit}`v`. -/
theorem exercise_7A_10 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (T : V →ₗ[ℂ] V) :
    LinearMap.IsSymmetric T ↔
      ∀ v, ⟪T v, v⟫_ℂ = ⟪LinearMap.adjoint T v, v⟫_ℂ := by
  sorry

/-- 7A.11 For {lit}`S(w, z) = (−z, w)` on {lit}`𝔽²`: (a) {lit}`S*(w, z) = (z, −w)`;
(b) {lit}`S` is normal but not self-adjoint. -/
theorem exercise_7A_11 (S : EuclideanSpace 𝕜 (Fin 2) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin 2))
    (hS : ∀ v : EuclideanSpace 𝕜 (Fin 2), S v = !₂[- v 1, v 0]) :
    (∀ v : EuclideanSpace 𝕜 (Fin 2), LinearMap.adjoint S v = !₂[v 1, - v 0]) ∧
      IsStarNormal S ∧ ¬ LinearMap.IsSymmetric S := by
  sorry

/-- 7A.12 {lit}`T` is normal iff {lit}`T = A + B` for commuting {lit}`A, B` with
{lit}`A` self-adjoint and {lit}`B` skew ({lit}`B* = −B`). -/
theorem exercise_7A_12 (T : V →ₗ[𝕜] V) :
    IsStarNormal T ↔ ∃ A B : V →ₗ[𝕜] V, LinearMap.IsSymmetric A ∧
      LinearMap.adjoint B = -B ∧ A ∘ₗ B = B ∘ₗ A ∧ T = A + B := by
  sorry

/-- 7A.13 For {lit}`𝔽 = ℝ`, the operator {lit}`𝒜 T = T*` on {lit}`ℒ(V)` has
(a) eigenvalues {lit}`±1` and (b) minimal polynomial {lit}`z² − 1` (when
{lit}`V ≠ 0`). -/
theorem exercise_7A_13 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [Nontrivial V]
    (𝒜 : (V →ₗ[ℝ] V) →ₗ[ℝ] (V →ₗ[ℝ] V))
    (h𝒜 : ∀ T : V →ₗ[ℝ] V, 𝒜 T = LinearMap.adjoint T) :
    (∀ μ : ℝ, HasEigenvalue 𝒜 μ ↔ μ = 1 ∨ μ = -1) ∧
      minpoly ℝ 𝒜 = Polynomial.X ^ 2 - 1 := by
  sorry

/-! 7A.14 The {lit}`L²` inner product {lit}`⟨p, q⟩ = ∫₀¹ pq` on {lit}`𝒫₂(ℝ)`,
modelled as {name}`Polynomial.degreeLT` {lit}`ℝ 3`. mathlib has no instance for
this, so we build it from an {name}`InnerProductSpace.Core` (the analytic axioms —
symmetry, positivity, definiteness — are left as `sorry`, like the exercises). -/

noncomputable def l2Core_7A14 : InnerProductSpace.Core ℝ (Polynomial.degreeLT ℝ 3) where
  inner p q := ∫ x in (0 : ℝ)..1, ((p : Polynomial ℝ).eval x) * ((q : Polynomial ℝ).eval x)
  conj_inner_symm := by sorry
  re_inner_nonneg := by sorry
  add_left := by sorry
  smul_left := by sorry
  definite := by sorry

noncomputable instance : NormedAddCommGroup (Polynomial.degreeLT ℝ 3) :=
  l2Core_7A14.toNormedAddCommGroup

noncomputable instance : InnerProductSpace ℝ (Polynomial.degreeLT ℝ 3) :=
  InnerProductSpace.ofCore _

noncomputable instance : FiniteDimensional ℝ (Polynomial.degreeLT ℝ 3) :=
  Module.Finite.equiv (Polynomial.degreeLTEquiv ℝ 3).symm

/-- 7A.14 With {lit}`⟨p, q⟩ = ∫₀¹ pq` on {lit}`𝒫₂(ℝ)` and {lit}`T(ax² + bx + c) =
bx`, the operator {lit}`T` is not self-adjoint — even though its matrix with
respect to {lit}`1, x, x²` equals its own conjugate transpose. -/
theorem exercise_7A_14
    (T : (Polynomial.degreeLT ℝ 3) →ₗ[ℝ] (Polynomial.degreeLT ℝ 3))
    (hT : ∀ p : Polynomial.degreeLT ℝ 3,
      (T p : Polynomial ℝ) = Polynomial.C ((p : Polynomial ℝ).coeff 1) * Polynomial.X) :
    ¬ LinearMap.IsSymmetric T := by
  sorry

/-- 7A.15 (a) For invertible {lit}`T`, {lit}`T` is self-adjoint iff {lit}`T⁻¹` is
self-adjoint. -/
theorem exercise_7A_15a (T : V ≃ₗ[𝕜] V) :
    LinearMap.IsSymmetric (T : V →ₗ[𝕜] V) ↔
      LinearMap.IsSymmetric (T.symm : V →ₗ[𝕜] V) := by
  sorry

/-- 7A.15 (b) For invertible {lit}`T`, {lit}`T` is normal iff {lit}`T⁻¹` is
normal. -/
theorem exercise_7A_15b (T : V ≃ₗ[𝕜] V) :
    IsStarNormal (T : V →ₗ[𝕜] V) ↔ IsStarNormal (T.symm : V →ₗ[𝕜] V) := by
  sorry

/-- 7A.16 For {lit}`𝔽 = ℝ`: (a) the self-adjoint operators form a subspace of
{lit}`ℒ(V)`; (b) of dimension {lit}`(dim V)(dim V + 1)/2`. -/
theorem exercise_7A_16 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] :
    ∃ U : Submodule ℝ (V →ₗ[ℝ] V),
      (∀ T, T ∈ U ↔ LinearMap.IsSymmetric T) ∧
        finrank ℝ U = finrank ℝ V * (finrank ℝ V + 1) / 2 := by
  sorry

/-- 7A.17 For {lit}`𝔽 = ℂ` and {lit}`V ≠ 0`, the self-adjoint operators do not
form a subspace of {lit}`ℒ(V)`. -/
theorem exercise_7A_17 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] [Nontrivial V] :
    ¬ ∃ U : Submodule ℂ (V →ₗ[ℂ] V), ∀ T, T ∈ U ↔ LinearMap.IsSymmetric T := by
  sorry

/-- 7A.18 If {lit}`dim V ≥ 2`, the normal operators do not form a subspace of
{lit}`ℒ(V)`. -/
theorem exercise_7A_18 (h : 2 ≤ finrank 𝕜 V) :
    ¬ ∃ U : Submodule 𝕜 (V →ₗ[𝕜] V), ∀ T, T ∈ U ↔ IsStarNormal T := by
  sorry

/-- 7A.19 If {lit}`‖T*v‖ ≤ ‖Tv‖` for every {lit}`v`, then {lit}`T` is normal. -/
theorem exercise_7A_19 (T : V →ₗ[𝕜] V)
    (h : ∀ v, ‖LinearMap.adjoint T v‖ ≤ ‖T v‖) : IsStarNormal T := by
  sorry

/-- 7A.20 If {lit}`P² = P`, the following are equivalent: (a) {lit}`P` self-adjoint;
(b) {lit}`P` normal; (c) {lit}`P = P_U` for some subspace {lit}`U`. -/
theorem exercise_7A_20 (P : V →ₗ[𝕜] V) (hP : P ∘ₗ P = P) :
    [LinearMap.IsSymmetric P, IsStarNormal P,
      ∃ U : Submodule 𝕜 V, (U.starProjection : V →ₗ[𝕜] V) = P].TFAE := by
  sorry

/-! 7A.21 (deferred): for the differentiation operator {lit}`D p = p′` on
{lit}`𝒫₈(ℝ)`, no inner product makes {lit}`D` normal. Faithfully stating this
requires quantifying over all inner-product-space structures on {lit}`𝒫₈(ℝ)`,
which is not expressible with mathlib's typeclass-based inner products; deferred. -/

/-- 7A.22 There is an operator on {lit}`ℝ³` that is normal but not self-adjoint. -/
theorem exercise_7A_22 :
    ∃ T : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3),
      IsStarNormal T ∧ ¬ LinearMap.IsSymmetric T := by
  sorry

/-- 7A.23 If {lit}`T` is normal, {lit}`‖v‖ = ‖w‖ = 2`, {lit}`Tv = 3v`,
{lit}`Tw = 4w`, then {lit}`‖T(v + w)‖ = 10`. -/
theorem exercise_7A_23 {T : V →ₗ[𝕜] V} (hT : IsStarNormal T) {v w : V}
    (hv : ‖v‖ = 2) (hw : ‖w‖ = 2) (hTv : T v = (3 : 𝕜) • v) (hTw : T w = (4 : 𝕜) • w) :
    ‖T (v + w)‖ = 10 := by
  sorry

/-- 7A.24 If the minimal polynomial of {lit}`T` is {lit}`∑ aₖ zᵏ + zᵐ`, then the
minimal polynomial of {lit}`T*` has the conjugated coefficients — i.e. it is
{lit}`(minpoly T)` with {lit}`conj` applied to each coefficient. -/
theorem exercise_7A_24 (T : V →ₗ[𝕜] V) :
    minpoly 𝕜 (LinearMap.adjoint T) = (minpoly 𝕜 T).map (starRingEnd 𝕜) := by
  sorry

/-- 7A.25 {lit}`T` is diagonalizable iff {lit}`T*` is diagonalizable (writing
diagonalizability as the existence of an eigenvector basis). -/
theorem exercise_7A_25 (T : V →ₗ[𝕜] V) :
    (∃ b : Module.Basis (Fin (finrank 𝕜 V)) 𝕜 V, ∀ i, ∃ μ : 𝕜, T (b i) = μ • b i) ↔
      (∃ b : Module.Basis (Fin (finrank 𝕜 V)) 𝕜 V, ∀ i,
        ∃ μ : 𝕜, LinearMap.adjoint T (b i) = μ • b i) := by
  sorry

/-- 7A.26 For {lit}`T v = ⟨v, u⟩ x`, {lit}`T` is normal iff the list {lit}`u, x` is
linearly dependent (part (b); part (a) is the real self-adjoint version). -/
theorem exercise_7A_26 (u x : V) (T : V →ₗ[𝕜] V) (hT : ∀ v, T v = ⟪u, v⟫_𝕜 • x) :
    IsStarNormal T ↔ ¬ LinearIndependent 𝕜 ![u, x] := by
  sorry

/-- 7A.27 If {lit}`T` is normal, then {lit}`null Tᵏ = null T` and
{lit}`range Tᵏ = range T` for every positive integer {lit}`k`. -/
theorem exercise_7A_27 {T : V →ₗ[𝕜] V} (hT : IsStarNormal T) (k : ℕ) (hk : 0 < k) :
    LinearMap.ker (T ^ k) = LinearMap.ker T ∧
      LinearMap.range (T ^ k) = LinearMap.range T := by
  sorry

/-- 7A.28 If {lit}`T` is normal, then for every {lit}`λ` the minimal polynomial of
{lit}`T` is not a polynomial multiple of {lit}`(z − λ)²`. -/
theorem exercise_7A_28 {T : V →ₗ[𝕜] V} (hT : IsStarNormal T) (μ : 𝕜) :
    ¬ (Polynomial.X - Polynomial.C μ) ^ 2 ∣ minpoly 𝕜 T := by
  sorry

/-- 7A.29 Counterexample: {lit}`‖Teₖ‖ = ‖T*eₖ‖` on some orthonormal basis does
*not* imply {lit}`T` normal. -/
theorem exercise_7A_29 :
    ¬ ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
      [FiniteDimensional 𝕜 V] (T : V →ₗ[𝕜] V) (n : ℕ) (e : OrthonormalBasis (Fin n) 𝕜 V),
      (∀ k, ‖T (e k)‖ = ‖LinearMap.adjoint T (e k)‖) → IsStarNormal T := by
  sorry

/-- 7A.30 If {lit}`T ∈ ℒ(𝔽³)` is normal with {lit}`T(1,1,1) = (2,2,2)`, then every
{lit}`(z₁, z₂, z₃) ∈ null T` has {lit}`z₁ + z₂ + z₃ = 0`. -/
theorem exercise_7A_30 (T : EuclideanSpace 𝕜 (Fin 3) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin 3))
    (hT : IsStarNormal T) (h1 : T !₂[1, 1, 1] = !₂[2, 2, 2])
    (z : EuclideanSpace 𝕜 (Fin 3)) (hz : T z = 0) :
    z 0 + z 1 + z 2 = 0 := by
  sorry

/-! 7A.31 (deferred): on {lit}`span(1, cos x, …, cos nx, sin x, …, sin nx)` with
{lit}`⟨f, g⟩ = ∫₋ₚᵢᵖⁱ fg`, show {lit}`D f = f′` satisfies {lit}`D* = −D` (normal,
not self-adjoint) and {lit}`T f = f″` is self-adjoint. Needs the {lit}`L²` inner
product on this trigonometric function space, absent from the pinned mathlib;
deferred. -/

/-! 7A.32 (deferred): under the Riesz identifications of {lit}`V` with {lit}`V′`
and {lit}`W` with {lit}`W′` (6.58), the adjoint {lit}`T*` corresponds to the dual
map {lit}`T′`. Deferred — the statement requires threading the Riesz
identification between the continuous dual and {lit}`Module.Dual`. -/

end LADR.Section_7A
