import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.LinearAlgebra.Matrix.Notation
import LinearAlgebraDoneRightLean.Section_7B
import LinearAlgebraDoneRightLean.Section_7C
import Mathlib.Tactic.Linter.Style
import CompanionHelper

/-!
# Axler, *Linear Algebra Done Right* (4e) — Section 7D: Isometries, Unitary Operators, and Matrix Factorization
-/

namespace LADR.Section_7D

open scoped InnerProductSpace RealInnerProductSpace ComplexConjugate Matrix
open Module (finrank)
open Module.End (HasEigenvalue HasEigenvector)

variable {𝕜 : Type*} [RCLike 𝕜]
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [FiniteDimensional 𝕜 V]
  {W : Type*} [NormedAddCommGroup W] [InnerProductSpace 𝕜 W] [FiniteDimensional 𝕜 W]

/-! # Isometries -/

/-! 7.44 Definition: isometry

A linear map {lit}`S ∈ ℒ(V, W)` is an *isometry* if {lit}`‖S v‖ = ‖v‖` for every
{lit}`v` — i.e. it preserves norms. mathlib packages norm-preserving linear maps
as {name}`LinearIsometry`; here we work with the predicate on ordinary linear
maps to stay close to Axler. -/

def IsIsometry (S : V →ₗ[𝕜] W) : Prop := ∀ v, ‖S v‖ = ‖v‖

omit [FiniteDimensional 𝕜 V] [FiniteDimensional 𝕜 W] in
/-- Every isometry is injective (if {lit}`S v = 0` then {lit}`‖v‖ = ‖S v‖ = 0`). -/
theorem IsIsometry.injective {S : V →ₗ[𝕜] W} (h : IsIsometry S) : Function.Injective S := by
  intro a b hab
  have h0 : ‖a - b‖ = 0 := by rw [← h (a - b), map_sub, hab, sub_self, norm_zero]
  exact sub_eq_zero.mp (norm_eq_zero.mp h0)

/-! 7.45 Example: if {lit}`S` maps an orthonormal basis {lit}`e₁, …, eₙ` of
{lit}`V` to an orthonormal list {lit}`g₁, …, gₙ` in {lit}`W`, then {lit}`S` is an
isometry.

We prove the sharper fact that such an {lit}`S` *preserves inner products*: writing
{lit}`u, v` in the basis {lit}`e` and using the orthonormality of the {lit}`gₖ`
collapses the double sum to {name}`OrthonormalBasis.sum_inner_mul_inner`. This is
also the engine of the equivalences (a) ⟺ (c) ⟺ (d) in 7.49. -/

omit [FiniteDimensional 𝕜 V] [FiniteDimensional 𝕜 W] in
theorem isometry_of_orthonormal_image {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι 𝕜 V) (S : V →ₗ[𝕜] W)
    (h : Orthonormal 𝕜 (fun i => S (b i))) (u v : V) :
    ⟪S u, S v⟫_𝕜 = ⟪u, v⟫_𝕜 := by
  have hSu : S u = ∑ i, ⟪b i, u⟫_𝕜 • S (b i) := by
    conv_lhs => rw [← b.sum_repr' u]
    rw [map_sum]; exact Finset.sum_congr rfl fun i _ => map_smul _ _ _
  have hSv : S v = ∑ i, ⟪b i, v⟫_𝕜 • S (b i) := by
    conv_lhs => rw [← b.sum_repr' v]
    rw [map_sum]; exact Finset.sum_congr rfl fun i _ => map_smul _ _ _
  rw [hSu, hSv, sum_inner, ← b.sum_inner_mul_inner u v]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_sum, Finset.sum_eq_single i]
  · rw [inner_smul_left, inner_smul_right, (orthonormal_iff_ite.mp h) i i, if_pos rfl,
      mul_one, inner_conj_symm]
  · intro j _ hij
    rw [inner_smul_left, inner_smul_right, (orthonormal_iff_ite.mp h) i j,
      if_neg (Ne.symm hij), mul_zero, mul_zero]
  · intro hi; exact absurd (Finset.mem_univ i) hi

omit [FiniteDimensional 𝕜 V] [FiniteDimensional 𝕜 W] in
/-- 7.45, as stated by Axler: the map is an isometry. -/
theorem isometry_of_orthonormal_image_isometry {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι 𝕜 V) (S : V →ₗ[𝕜] W)
    (h : Orthonormal 𝕜 (fun i => S (b i))) : IsIsometry S :=
  (LinearMap.norm_map_iff_inner_map_map S).mpr fun u v =>
    isometry_of_orthonormal_image b S h u v

/-! 7.49 Characterizations of isometries

For {lit}`S ∈ ℒ(V, W)` with orthonormal bases {lit}`e` of {lit}`V` and {lit}`f`
of {lit}`W`, the following are equivalent:
(a) {lit}`S` is an isometry;
(b) {lit}`S* S = I`;
(c) {lit}`⟨S u, S v⟩ = ⟨u, v⟩` for all {lit}`u, v`;
(d) {lit}`S e₁, …, S eₙ` is an orthonormal list;
(e) the columns of {lit}`ℳ(S, e, f)` form an orthonormal list in {lit}`𝔽ᵐ`.

(a) ⟺ (c) is {name}`LinearMap.norm_map_iff_inner_map_map`. We prove (c) ⟺ (b)
and (a) ⟺ (d) below. Condition (e) is the matrix restatement of (d) once the
columns of {lit}`ℳ(S, e, f)` are identified with the coordinate vectors of the
{lit}`S eₖ`; it adds no mathematical content over (d) and is not separately
formalized here. -/

omit [FiniteDimensional 𝕜 V] [FiniteDimensional 𝕜 W] in
/-- (a) ⟺ (c): an isometry is exactly an inner-product-preserving map. -/
theorem isometry_iff_inner (S : V →ₗ[𝕜] W) :
    IsIsometry S ↔ ∀ u v, ⟪S u, S v⟫_𝕜 = ⟪u, v⟫_𝕜 :=
  LinearMap.norm_map_iff_inner_map_map S

/-- (c) ⟺ (b): preserving inner products is equivalent to {lit}`S* S = I`. -/
theorem inner_iff_adjoint_comp (S : V →ₗ[𝕜] W) :
    (∀ u v, ⟪S u, S v⟫_𝕜 = ⟪u, v⟫_𝕜) ↔ LinearMap.adjoint S ∘ₗ S = 1 := by
  constructor
  · intro h; ext u
    refine ext_inner_right 𝕜 fun v => ?_
    rw [LinearMap.comp_apply, LinearMap.adjoint_inner_left, Module.End.one_apply, h]
  · intro h u v
    have hu := LinearMap.congr_fun h u
    rw [LinearMap.comp_apply, Module.End.one_apply] at hu
    rw [← LinearMap.adjoint_inner_left, hu]

/-- (a) ⟺ (b). -/
theorem isometry_iff_adjoint_comp (S : V →ₗ[𝕜] W) :
    IsIsometry S ↔ LinearMap.adjoint S ∘ₗ S = 1 :=
  (isometry_iff_inner S).trans (inner_iff_adjoint_comp S)

omit [FiniteDimensional 𝕜 V] [FiniteDimensional 𝕜 W] in
/-- (a) ⟺ (d): {lit}`S` is an isometry iff it carries some (hence any) orthonormal
basis to an orthonormal list. -/
theorem isometry_iff_orthonormal_image {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι 𝕜 V) (S : V →ₗ[𝕜] W) :
    IsIsometry S ↔ Orthonormal 𝕜 (fun i => S (b i)) := by
  constructor
  · intro h
    rw [orthonormal_iff_ite]
    intro i j
    rw [(isometry_iff_inner S).mp h (b i) (b j)]
    exact (orthonormal_iff_ite.mp b.orthonormal) i j
  · exact isometry_of_orthonormal_image_isometry b S

/-! # Unitary Operators -/

/-! 7.51 Definition: unitary operator

An operator {lit}`S ∈ ℒ(V)` is *unitary* if it is an invertible isometry. Since
{lit}`V` is finite-dimensional, every isometry is already invertible (injective +
finite dimension ⟹ bijective), so the word "invertible" is redundant here; we keep
it for faithfulness to the definition. -/

def IsUnitary (S : V →ₗ[𝕜] V) : Prop := Function.Bijective S ∧ IsIsometry S

/-- On a finite-dimensional space an isometry is automatically bijective. -/
theorem IsIsometry.bijective {S : V →ₗ[𝕜] V} (h : IsIsometry S) : Function.Bijective S :=
  ⟨h.injective, LinearMap.injective_iff_surjective.mp h.injective⟩

/-- Hence on {lit}`ℒ(V)` "unitary" and "isometry" coincide. -/
theorem isUnitary_iff_isometry (S : V →ₗ[𝕜] V) : IsUnitary S ↔ IsIsometry S :=
  ⟨fun h => h.2, fun h => ⟨h.bijective, h⟩⟩

/-! 7.52 Example: rotation of {lit}`ℝ²`

The matrix {lit}`((cos θ, -sin θ), (sin θ, cos θ))` has orthonormal columns, so the
associated operator on {lit}`ℝ²` is an isometry, hence unitary. We record this as
membership of the rotation matrix in mathlib's {name}`Matrix.unitaryGroup`. -/

noncomputable def rotationMatrix (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cos θ, -Real.sin θ; Real.sin θ, Real.cos θ]

theorem rotationMatrix_mem_unitaryGroup (θ : ℝ) :
    rotationMatrix θ ∈ Matrix.unitaryGroup (Fin 2) ℝ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotationMatrix, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.star_eq_conjTranspose] <;>
    ring_nf <;>
    linarith [Real.sin_sq_add_cos_sq θ, Real.cos_sq_add_sin_sq θ]

/-! 7.53 Characterizations of unitary operators

For {lit}`S ∈ ℒ(V)` with orthonormal basis {lit}`e`, the following are equivalent:
(a) {lit}`S` unitary; (b) {lit}`S* S = S S* = I`; (c) {lit}`S` invertible with
{lit}`S⁻¹ = S*`; (d) {lit}`S e₁, …, S eₙ` is an orthonormal basis; (e) the rows of
{lit}`ℳ(S, e)` are orthonormal; (f) {lit}`S*` is unitary.

We prove (a) ⟺ (b), (a) ⟺ (d), and (a) ⟺ (f). Statement (c) is the reading of (b)
as "{lit}`S*` is the two-sided inverse", recorded in {lit}`isUnitary_inverse`; (e) is
the matrix restatement of the columns/rows exchange (Exercise 13) and is not
separately formalized. -/

/-- (a) ⟺ (b). -/
theorem isUnitary_iff_adjoint (S : V →ₗ[𝕜] V) :
    IsUnitary S ↔ LinearMap.adjoint S ∘ₗ S = 1 ∧ S ∘ₗ LinearMap.adjoint S = 1 := by
  constructor
  · rintro ⟨hbij, hiso⟩
    have hSS : LinearMap.adjoint S ∘ₗ S = 1 := (isometry_iff_adjoint_comp S).mp hiso
    refine ⟨hSS, ?_⟩
    ext w
    obtain ⟨x, rfl⟩ := hbij.surjective w
    have hx : LinearMap.adjoint S (S x) = x := by
      have := LinearMap.congr_fun hSS x
      rwa [LinearMap.comp_apply, Module.End.one_apply] at this
    rw [LinearMap.comp_apply, hx, Module.End.one_apply]
  · rintro ⟨h1, h2⟩
    have hiso : IsIsometry S := (isometry_iff_adjoint_comp S).mpr h1
    refine ⟨Function.bijective_iff_has_inverse.mpr
      ⟨LinearMap.adjoint S, fun x => ?_, fun x => ?_⟩, hiso⟩
    · have := LinearMap.congr_fun h1 x
      rwa [LinearMap.comp_apply, Module.End.one_apply] at this
    · have := LinearMap.congr_fun h2 x
      rwa [LinearMap.comp_apply, Module.End.one_apply] at this

/-- (c): for a unitary operator, {lit}`S*` is a two-sided inverse of {lit}`S`. -/
theorem isUnitary_inverse {S : V →ₗ[𝕜] V} (h : IsUnitary S) :
    LinearMap.adjoint S ∘ₗ S = 1 ∧ S ∘ₗ LinearMap.adjoint S = 1 :=
  (isUnitary_iff_adjoint S).mp h

/-- (a) ⟺ (d). -/
theorem isUnitary_iff_orthonormal_image {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι 𝕜 V) (S : V →ₗ[𝕜] V) :
    IsUnitary S ↔ Orthonormal 𝕜 (fun i => S (b i)) :=
  (isUnitary_iff_isometry S).trans (isometry_iff_orthonormal_image b S)

/-- (a) ⟺ (f): {lit}`S` is unitary iff {lit}`S*` is unitary. -/
theorem isUnitary_adjoint_iff (S : V →ₗ[𝕜] V) :
    IsUnitary S ↔ IsUnitary (LinearMap.adjoint S) := by
  rw [isUnitary_iff_adjoint, isUnitary_iff_adjoint, LinearMap.adjoint_adjoint, and_comm]

/-! 7.54 Eigenvalues of unitary operators have absolute value 1.

If {lit}`S v = λ v` with {lit}`v ≠ 0`, then
{lit}`|λ| ‖v‖ = ‖λ v‖ = ‖S v‖ = ‖v‖`, so {lit}`|λ| = 1`. -/

omit [FiniteDimensional 𝕜 V] in
theorem unitary_eigenvalue_abs_one {S : V →ₗ[𝕜] V} (h : IsUnitary S) {μ : 𝕜}
    (hμ : HasEigenvalue S μ) : ‖μ‖ = 1 := by
  obtain ⟨v, hv, hv0⟩ := hμ.exists_hasEigenvector
  have hmem : S v = μ • v := Module.End.mem_eigenspace_iff.mp hv
  have hn : ‖v‖ = ‖μ‖ * ‖v‖ := by
    have hsv : ‖S v‖ = ‖μ‖ * ‖v‖ := by rw [hmem, norm_smul]
    rw [← hsv, h.2 v]
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv0
  have h1 : ‖μ‖ * ‖v‖ = 1 * ‖v‖ := by rw [one_mul]; linarith [hn]
  exact mul_right_cancel₀ (ne_of_gt hvpos) h1

/-! 7.55 Description of unitary operators on complex inner product spaces.

Over {lit}`ℂ`, {lit}`S` is unitary iff there is an orthonormal basis of eigenvectors
whose eigenvalues all have absolute value 1. Forward: a unitary operator is normal
({lit}`S* S = S S* = I`), so the complex spectral theorem
({module -checked}`LinearAlgebraDoneRightLean.Section_7B`) supplies an orthonormal
eigenbasis, and 7.54 gives {lit}`|λ| = 1`. Backward: such a basis makes
{lit}`S e₁, …, S eₙ` orthonormal, so {lit}`S` is an isometry, hence unitary. -/

theorem unitary_iff_orthonormal_eigenbasis
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (S : E →ₗ[ℂ] E) :
    IsUnitary S ↔ ∃ (n : ℕ) (e : OrthonormalBasis (Fin n) ℂ E),
      ∀ i, ∃ μ : ℂ, S (e i) = μ • e i ∧ ‖μ‖ = 1 := by
  constructor
  · intro hS
    obtain ⟨h1, h2⟩ := (isUnitary_iff_adjoint S).mp hS
    have hnorm : IsStarNormal S :=
      (LADR.Section_7A.normal_iff_comp S).mpr (by rw [h1, h2])
    obtain ⟨n, e, he⟩ := LADR.Section_7B.complex_spectral S hnorm
    refine ⟨n, e, fun i => ⟨⟪e i, S (e i)⟫_ℂ, he i, ?_⟩⟩
    have hnormeq : ‖S (e i)‖ = ‖e i‖ := hS.2 (e i)
    rw [he i, norm_smul, e.orthonormal.1 i, mul_one] at hnormeq
    exact hnormeq
  · rintro ⟨n, e, he⟩
    have horth : Orthonormal ℂ (fun i => S (e i)) := by
      rw [orthonormal_iff_ite]
      intro i j
      rcases eq_or_ne i j with hEq | hNe
      · subst hEq
        obtain ⟨μi, hi, hni⟩ := he i
        have he1 : ⟪e i, e i⟫_ℂ = 1 := by
          rw [(orthonormal_iff_ite.mp e.orthonormal) i i, if_pos rfl]
        rw [hi, inner_smul_left, inner_smul_right, he1, mul_one, RCLike.conj_mul, hni, if_pos rfl]
        norm_num
      · obtain ⟨μi, hi, hni⟩ := he i
        obtain ⟨μj, hj, hnj⟩ := he j
        rw [hi, hj, inner_smul_left, inner_smul_right, (orthonormal_iff_ite.mp e.orthonormal) i j]
        simp only [if_neg hNe, mul_zero]
    have hiso : IsIsometry S := isometry_of_orthonormal_image_isometry e S horth
    exact ⟨hiso.bijective, hiso⟩

/-! # QR Factorization -/

/-! 7.56 Definition: unitary matrix

An {lit}`n`-by-{lit}`n` matrix is *unitary* if its columns form an orthonormal list
in {lit}`𝔽ⁿ`. Equivalently (Euclidean inner product of columns {lit}`k, r` equals
{lit}`(Q* Q)ₖᵣ`), {lit}`Q* Q = I`. This is mathlib's {name}`Matrix.unitaryGroup`. -/

section Matrices

variable {n : Type*} [Fintype n] [DecidableEq n]

def IsUnitaryMatrix (Q : Matrix n n 𝕜) : Prop := Q ∈ Matrix.unitaryGroup n 𝕜

/-! 7.57 Characterizations of unitary matrices

For a square matrix {lit}`Q`: (a) {lit}`Q` unitary (columns orthonormal); (b) rows
orthonormal; (c) {lit}`‖Q v‖ = ‖v‖`; (d) {lit}`Q* Q = Q Q* = I`. Axler leaves the
proof as Exercise 17. The core equivalence (a) ⟺ (d) is immediate from mathlib's
{name}`Matrix.mem_unitaryGroup_iff` / {name}`Matrix.mem_unitaryGroup_iff'`, using
{lit}`star Q = Q*` (the conjugate transpose). -/

theorem isUnitaryMatrix_iff_conjTranspose (Q : Matrix n n 𝕜) :
    IsUnitaryMatrix Q ↔ Qᴴ * Q = 1 ∧ Q * Qᴴ = 1 := by
  rw [IsUnitaryMatrix, ← Matrix.star_eq_conjTranspose]
  constructor
  · intro h
    exact ⟨(Matrix.mem_unitaryGroup_iff').mp h, (Matrix.mem_unitaryGroup_iff).mp h⟩
  · rintro ⟨h, _⟩
    exact (Matrix.mem_unitaryGroup_iff').mpr h

/-! 7.58 QR factorization

If {lit}`A` is a square matrix with linearly independent columns, then
{lit}`A = QR` with {lit}`Q` unitary and {lit}`R` upper triangular with positive
diagonal, uniquely. The existence uses Gram–Schmidt applied to the columns of
{lit}`A` (mathlib: {lit}`gramSchmidtOrthonormalBasis`), reading off
{lit}`Rⱼₖ = ⟨vₖ, eⱼ⟩`; uniqueness uses the uniqueness of the Gram–Schmidt lists.

This result is **deferred**: mathlib pins no packaged QR factorization, and
assembling it here — the change of basis to the Gram–Schmidt orthonormal basis, the
upper-triangularity of the coefficient matrix, positivity of the diagonal, and the
uniqueness argument — is a substantial development beyond the scope of this section.
It is stated here without a Lean declaration to avoid a `sorry` on a numbered
theorem. -/

/-! 7.60 Example: QR factorization of a 3-by-3 matrix.

A concrete numeric illustration of 7.58 (with entries involving {lit}`√10`). It is
**deferred** together with the QR factorization it illustrates. -/

/-! # Cholesky Factorization -/

end Matrices

/-! 7.61 Positive invertible operator

A self-adjoint {lit}`T ∈ ℒ(V)` is a positive invertible operator iff
{lit}`⟨T v, v⟩ > 0` for every nonzero {lit}`v`. Using a positive square root
{lit}`R` of {lit}`T` (7.39, from
{module -checked}`LinearAlgebraDoneRightLean.Section_7C`), we have
{lit}`⟨T v, v⟩ = ‖R v‖²`, so positivity of {lit}`⟨T v, v⟩` for nonzero {lit}`v` is
exactly injectivity of {lit}`R`, equivalently of {lit}`T`. On a finite-dimensional
space injectivity is invertibility. -/

theorem positive_invertible_iff {T : V →ₗ[𝕜] V} (hT : T.IsPositive) :
    Function.Injective T ↔ ∀ v : V, v ≠ 0 → 0 < RCLike.re ⟪T v, v⟫_𝕜 := by
  obtain ⟨R, hR, hRT⟩ := LADR.Section_7C.exists_positive_sqrt hT
  have hval : ∀ v, RCLike.re ⟪T v, v⟫_𝕜 = ‖R v‖ ^ 2 := by
    intro v
    rw [← hRT]
    simp only [LinearMap.comp_apply]
    rw [hR.isSymmetric (R v) v, inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow, RCLike.ofReal_re]
  have hRinj : Function.Injective T → Function.Injective R := by
    intro hinj a b hab
    apply hinj
    rw [← hRT]
    simp only [LinearMap.comp_apply, hab]
  constructor
  · intro hinj v hv
    rw [hval]
    have hRv : R v ≠ 0 := fun h => hv (hRinj hinj (h.trans (map_zero R).symm))
    exact pow_pos (norm_pos_iff.mpr hRv) 2
  · intro hpos a b hab
    by_contra hne
    have hd : a - b ≠ 0 := sub_ne_zero.mpr hne
    have hgt := hpos (a - b) hd
    have hTz : ⟪T (a - b), a - b⟫_𝕜 = 0 := by
      rw [map_sub, hab, sub_self, inner_zero_left]
    rw [hTz, map_zero] at hgt
    exact lt_irrefl 0 hgt

/-! 7.62 Definition: positive definite matrix

A matrix {lit}`B ∈ 𝔽ⁿ'ⁿ` is *positive definite* if {lit}`B* = B` and
{lit}`⟨B x, x⟩ > 0` for every nonzero {lit}`x ∈ 𝔽ⁿ` (Euclidean inner product). -/

def IsPositiveDefinite {n : Type*} [Fintype n] (B : Matrix n n 𝕜) : Prop :=
  Bᴴ = B ∧ ∀ x : n → 𝕜, x ≠ 0 → 0 < RCLike.re (∑ i, conj (B.mulVec x i) * x i)

/-! 7.63 Cholesky factorization

Every positive definite matrix {lit}`B` factors uniquely as {lit}`B = R* R` with
{lit}`R` upper triangular with positive diagonal. Axler's proof takes an invertible
{lit}`A` with {lit}`B = A* A` (7.38) and a QR factorization {lit}`A = QR`, giving
{lit}`B = R* Q* Q R = R* R`.

This result is **deferred**: it is built directly on top of the QR factorization
(7.58), which is itself deferred (no packaged QR factorization in mathlib). It is
stated here without a Lean declaration to avoid a `sorry` on a numbered theorem. -/

/-! # Exercises 7D -/

/-- 7D.1 Suppose {lit}`dim V ≥ 2`. Then {lit}`S` is an isometry iff it maps every
orthonormal list of length two to an orthonormal list. -/
theorem exercise_1 (S : V →ₗ[𝕜] W) :
    IsIsometry S ↔ ∀ e : Fin 2 → V, Orthonormal 𝕜 e → Orthonormal 𝕜 (fun i => S (e i)) := by
  sorry

/-- 7D.3(a) The product of two unitary operators is unitary. -/
theorem exercise_3a {S T : V →ₗ[𝕜] V} (hS : IsUnitary S) (hT : IsUnitary T) :
    IsUnitary (S ∘ₗ T) := by
  sorry

/-- 7D.3(b) The adjoint (inverse) of a unitary operator is unitary. -/
theorem exercise_3b {S : V →ₗ[𝕜] V} (hS : IsUnitary S) :
    IsUnitary (LinearMap.adjoint S) := by
  sorry

/-- 7D.4 Over {lit}`ℂ`, for self-adjoint {lit}`A, B`, the operator {lit}`A + iB` is
unitary iff {lit}`AB = BA` and {lit}`A² + B² = I`. -/
theorem exercise_4 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] {A B : E →ₗ[ℂ] E}
    (hA : LinearMap.IsSymmetric A) (hB : LinearMap.IsSymmetric B) :
    IsUnitary (A + Complex.I • B) ↔
      (A ∘ₗ B = B ∘ₗ A ∧ A ∘ₗ A + B ∘ₗ B = 1) := by
  sorry

/-- 7D.9 Over {lit}`ℂ`, if every eigenvalue of {lit}`T` has absolute value 1 and
{lit}`‖T v‖ ≤ ‖v‖` for all {lit}`v`, then {lit}`T` is unitary. -/
theorem exercise_9 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (T : E →ₗ[ℂ] E)
    (h1 : ∀ μ : ℂ, HasEigenvalue T μ → ‖μ‖ = 1) (h2 : ∀ v, ‖T v‖ ≤ ‖v‖) :
    IsUnitary T := by
  sorry

/-- 7D.13 For a square complex matrix, the columns form an orthonormal list iff the
rows do (equivalently {lit}`Q* Q = I ⟺ Q Q* = I`). -/
theorem exercise_13 {n : Type*} [Fintype n] [DecidableEq n] (Q : Matrix n n 𝕜) :
    Qᴴ * Q = 1 ↔ Q * Qᴴ = 1 := by
  sorry

end LADR.Section_7D
