import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Dual
import LinearAlgebraDoneRightLean.Section_5C
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Recall
import CompanionHelper

/-!
# Axler, *Linear Algebra Done Right* (4e) — Section 6B: Orthonormal Bases
-/

namespace LADR.Section_6B

open scoped InnerProductSpace RealInnerProductSpace ComplexConjugate
open Module (finrank)

variable {𝕜 : Type*} [RCLike 𝕜]
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]

/-! # Orthonormal Lists and the Gram–Schmidt Procedure -/

/-! 6.22 Definition: orthonormal

A list {lit}`e₁, …, eₘ` is *orthonormal* if each vector has norm 1 and distinct
vectors are orthogonal, i.e. {lit}`⟨eⱼ, eₖ⟩ = 1` if {lit}`j = k` and {lit}`0`
otherwise. This is mathlib's {name}`Orthonormal` (indexing the list by a type
{lit}`ι`; for a length-{lit}`m` list take {lit}`ι = Fin m`). -/

recall orthonormal_iff_ite {𝕜 : Type*} {E : Type*} [RCLike 𝕜]
    [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E] {ι : Type*} [DecidableEq ι]
    {v : ι → E} :
    Orthonormal 𝕜 v ↔ ∀ i j, ⟪v i, v j⟫_𝕜 = if i = j then (1 : 𝕜) else (0 : 𝕜)

/-! 6.23 Example: the standard basis of {lit}`𝔽ⁿ` is orthonormal. -/

example {n : ℕ} : Orthonormal 𝕜 (EuclideanSpace.basisFun (Fin n) 𝕜) :=
  (EuclideanSpace.basisFun (Fin n) 𝕜).orthonormal

/-! 6.24 Norm of an orthonormal linear combination

If {lit}`e₁, …, eₘ` is orthonormal, then
{lit}`‖a₁e₁ + ⋯ + aₘeₘ‖² = |a₁|² + ⋯ + |aₘ|²`. -/

theorem norm_sq_sum_orthonormal {ι : Type*} [Fintype ι] {e : ι → V}
    (he : Orthonormal 𝕜 e) (a : ι → 𝕜) :
    ‖∑ i, a i • e i‖ ^ 2 = ∑ i, ‖a i‖ ^ 2 := by
  have key : (‖∑ i, a i • e i‖ : 𝕜) ^ 2 = ∑ i, (‖a i‖ : 𝕜) ^ 2 := by
    rw [← inner_self_eq_norm_sq_to_K, he.inner_sum a a Finset.univ]
    exact Finset.sum_congr rfl fun i _ => by simp [RCLike.conj_mul]
  have := congrArg RCLike.re key
  push_cast at this
  simpa using this

/-! 6.25 Orthonormal lists are linearly independent -/

theorem orthonormal_linearIndependent {ι : Type*} {e : ι → V}
    (he : Orthonormal 𝕜 e) : LinearIndependent 𝕜 e :=
  he.linearIndependent

/-! 6.26 Bessel's inequality

If {lit}`e₁, …, eₘ` is orthonormal and {lit}`v ∈ V`, then
{lit}`|⟨v, e₁⟩|² + ⋯ + |⟨v, eₘ⟩|² ≤ ‖v‖²` (recall {lit}`⟨v, eₖ⟩` is mathlib's
{lit}`⟪eₖ, v⟫`). -/

theorem bessel {ι : Type*} {e : ι → V} (he : Orthonormal 𝕜 e) (v : V)
    (s : Finset ι) : ∑ i ∈ s, ‖⟪e i, v⟫_𝕜‖ ^ 2 ≤ ‖v‖ ^ 2 :=
  he.sum_inner_products_le v

/-! # Orthonormal bases -/

/-! 6.27 Definition: orthonormal basis

An orthonormal basis is an orthonormal list that is also a basis; this is
mathlib's {name}`OrthonormalBasis`. The standard basis is an orthonormal basis
of {lit}`𝔽ⁿ`. -/

noncomputable example {n : ℕ} : OrthonormalBasis (Fin n) 𝕜 (EuclideanSpace 𝕜 (Fin n)) :=
  EuclideanSpace.basisFun (Fin n) 𝕜

/-! 6.28 Orthonormal lists of the right length are orthonormal bases

If {lit}`V` is finite-dimensional, every orthonormal list of length {lit}`dim V`
is an orthonormal basis. -/

theorem orthonormalBasis_of_length [FiniteDimensional 𝕜 V] {n : ℕ}
    (e : Fin n → V) (he : Orthonormal 𝕜 e) (hn : n = finrank 𝕜 V) :
    ∃ b : OrthonormalBasis (Fin n) 𝕜 V, ∀ i, b i = e i := by
  have hcard : finrank 𝕜 V = Fintype.card (Fin n) := by rw [Fintype.card_fin]; exact hn.symm
  have hv : Orthonormal 𝕜 (Set.univ.restrict e) :=
    he.comp _ Subtype.val_injective
  obtain ⟨b, hb⟩ := hv.exists_orthonormalBasis_extension_of_card_eq hcard
  exact ⟨b, fun i => hb i (Set.mem_univ i)⟩

/-! 6.30 Writing a vector as a linear combination of an orthonormal basis

Suppose {lit}`e₁, …, eₙ` is an orthonormal basis and {lit}`u, v ∈ V`. Then
(a) {lit}`v = ⟨v, e₁⟩e₁ + ⋯ + ⟨v, eₙ⟩eₙ`;
(b) {lit}`‖v‖² = |⟨v, e₁⟩|² + ⋯ + |⟨v, eₙ⟩|²` (Parseval's identity). -/

theorem orthonormalBasis_repr {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι 𝕜 V)
    (v : V) : v = ∑ i, ⟪b i, v⟫_𝕜 • b i :=
  (b.sum_repr' v).symm

theorem parseval {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι 𝕜 V) (v : V) :
    ‖v‖ ^ 2 = ∑ i, ‖⟪b i, v⟫_𝕜‖ ^ 2 :=
  (b.sum_sq_norm_inner_right v).symm

/-! 6.32 Gram–Schmidt procedure

Given a linearly independent list {lit}`v₁, …, vₘ`, the Gram–Schmidt procedure
produces an orthonormal list {lit}`e₁, …, eₘ` with the same span at each stage.
mathlib's {name}`InnerProductSpace.gramSchmidtNormed` are the {lit}`eₖ`; they are
orthonormal and preserve every initial span {lit}`span(v₁, …, vₖ)`. -/

open InnerProductSpace in
theorem gram_schmidt_orthonormal {ι : Type*} [LinearOrder ι]
    [LocallyFiniteOrderBot ι] [IsWellOrder ι (· < ·)] {f : ι → V}
    (hf : LinearIndependent 𝕜 f) : Orthonormal 𝕜 (gramSchmidtNormed 𝕜 f) :=
  InnerProductSpace.gramSchmidtNormed_orthonormal hf

open InnerProductSpace in
/-- The Gram–Schmidt vectors span each initial segment of the original list. -/
theorem span_gram_schmidt_initial {ι : Type*} [LinearOrder ι]
    [LocallyFiniteOrderBot ι] [IsWellOrder ι (· < ·)] (f : ι → V) (k : ι) :
    Submodule.span 𝕜 (gramSchmidt 𝕜 f '' Set.Iic k) =
      Submodule.span 𝕜 (f '' Set.Iic k) :=
  span_gramSchmidt_Iic 𝕜 f k

/-! 6.35 Existence of an orthonormal basis

Every finite-dimensional inner product space has an orthonormal basis. -/

noncomputable example [FiniteDimensional 𝕜 V] :
    OrthonormalBasis (Fin (finrank 𝕜 V)) 𝕜 V :=
  stdOrthonormalBasis 𝕜 V

/-! 6.36 Every orthonormal list extends to an orthonormal basis

If {lit}`V` is finite-dimensional, every orthonormal list can be extended to an
orthonormal basis. -/

theorem orthonormal_extends [FiniteDimensional 𝕜 V] {s : Set V}
    (hs : Orthonormal 𝕜 ((↑) : s → V)) :
    ∃ (u : Finset V) (b : OrthonormalBasis u 𝕜 V), s ⊆ u ∧ ⇑b = ((↑) : u → V) :=
  hs.exists_orthonormalBasis_extension

/-! 6.37 / 6.38 Upper-triangular matrix with respect to an orthonormal basis,
and Schur's theorem.

An operator is *upper-triangular* with respect to an orthonormal basis
{lit}`e₀, …, eₙ₋₁` when {lit}`T eₖ ∈ span(e₀, …, eₖ)` for each {lit}`k`. Gram–
Schmidt turns any triangularizing basis (from 5.44 in
{module -checked}`LinearAlgebraDoneRightLean.Section_5C`) into an orthonormal one
with the same flag, which stays upper-triangular. -/

section Schur

open Submodule Set InnerProductSpace
open LADR.Section_2B (IsBasis)
open LADR.Section_3C (matrixOf)
open LADR.Section_5C

variable [FiniteDimensional 𝕜 V]

/-- Gram–Schmidt turns a basis into an orthonormal basis with the same flag:
{lit}`span(e₀, …, eₖ) = span(v₀, …, vₖ)` for every {lit}`k`. -/
theorem exists_gramSchmidt_flag {n : ℕ} (v : Fin n → V) (hli : LinearIndependent 𝕜 v)
    (hcard : Module.finrank 𝕜 V = Fintype.card (Fin n)) :
    ∃ e : OrthonormalBasis (Fin n) 𝕜 V,
      ∀ k, span 𝕜 (e '' {i | i ≤ k}) = span 𝕜 (v '' {i | i ≤ k}) := by
  classical
  have hg_ne : ∀ i, gramSchmidt 𝕜 v i ≠ 0 := fun i => gramSchmidt_ne_zero i hli
  have hne : ∀ i, gramSchmidtNormed 𝕜 v i ≠ 0 := by
    intro i
    rw [gramSchmidtNormed]
    exact smul_ne_zero (inv_ne_zero (RCLike.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (hg_ne i))))
      (hg_ne i)
  obtain ⟨e, he_eq⟩ : ∃ e : OrthonormalBasis (Fin n) 𝕜 V,
      ∀ i, e i = (‖gramSchmidt 𝕜 v i‖⁻¹ : 𝕜) • gramSchmidt 𝕜 v i := by
    refine ⟨gramSchmidtOrthonormalBasis hcard v, fun i => ?_⟩
    rw [gramSchmidtOrthonormalBasis_apply hcard (hne i), gramSchmidtNormed]
  refine ⟨e, fun k => ?_⟩
  have hspan_e_g : span 𝕜 (e '' {i | i ≤ k}) = span 𝕜 (gramSchmidt 𝕜 v '' {i | i ≤ k}) := by
    apply le_antisymm <;> rw [span_le]
    · rintro _ ⟨i, hik, rfl⟩
      rw [he_eq i]; exact smul_mem _ _ (subset_span ⟨i, hik, rfl⟩)
    · rintro _ ⟨i, hik, rfl⟩
      have hgi : gramSchmidt 𝕜 v i = (‖gramSchmidt 𝕜 v i‖ : 𝕜) • e i := by
        rw [he_eq i, smul_smul, mul_inv_cancel₀
          (RCLike.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (hg_ne i))), one_smul]
      rw [hgi]; exact smul_mem _ _ (subset_span ⟨i, hik, rfl⟩)
  rw [hspan_e_g]; exact span_gramSchmidt_Iic (𝕜 := 𝕜) (f := v) (c := k)

/-- A flag {lit}`span(v₀, …, vₖ)` on which {lit}`T` acts triangularly is
{lit}`T`-invariant. -/
theorem flag_invariant {n : ℕ} (v : Fin n → V) (T : V →ₗ[𝕜] V)
    (hflag : ∀ k, T (v k) ∈ span 𝕜 (v '' {i | i ≤ k})) (k : Fin n) :
    ∀ x ∈ span 𝕜 (v '' {i | i ≤ k}), T x ∈ span 𝕜 (v '' {i | i ≤ k}) := by
  have hle : span 𝕜 (v '' {i | i ≤ k}) ≤ (span 𝕜 (v '' {i | i ≤ k})).comap T := by
    rw [span_le]
    rintro _ ⟨j, hjk, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap]
    have hsub : (v '' {i : Fin n | i ≤ j}) ⊆ (v '' {i | i ≤ k}) :=
      Set.image_mono fun i (hi : i ≤ j) => le_trans hi hjk
    exact Submodule.span_mono hsub (hflag j)
  exact fun x hx => hle hx

/-- Schur's theorem (6.38, core form): if {lit}`T` has an upper-triangular matrix
with respect to some basis, then it has one with respect to an orthonormal basis. -/
theorem exists_orthonormal_upperTriangular (T : V →ₗ[𝕜] V)
    (h : ∃ (n : ℕ) (v : Fin n → V) (hv : IsBasis 𝕜 v), IsUpperTriangular (matrixOf hv hv T)) :
    ∃ (n : ℕ) (e : OrthonormalBasis (Fin n) 𝕜 V),
      ∀ k, T (e k) ∈ Submodule.span 𝕜 (e '' {i | i ≤ k}) := by
  classical
  obtain ⟨n, v, hv, hA⟩ := h
  have hcoe : (⇑hv.toModuleBasis) = v := funext (IsBasis.toModuleBasis_apply hv)
  have hli : LinearIndependent 𝕜 v := hcoe ▸ hv.toModuleBasis.linearIndependent
  have hcard : Module.finrank 𝕜 V = Fintype.card (Fin n) := by
    rw [Module.finrank_eq_card_basis hv.toModuleBasis, Fintype.card_fin]
  obtain ⟨e, hspan_gs⟩ := exists_gramSchmidt_flag v hli hcard
  have hflag : ∀ k, T (v k) ∈ span 𝕜 (v '' {i | i ≤ k}) :=
    ((tfae_upperTriangular hv T).out 0 2).mp hA
  have hek_mem : ∀ (k : Fin n), e k ∈ span 𝕜 (v '' {i | i ≤ k}) := by
    intro k; rw [← hspan_gs k]; exact subset_span ⟨k, le_refl k, rfl⟩
  refine ⟨n, e, fun k => ?_⟩
  rw [hspan_gs k]
  exact flag_invariant v T hflag k (e k) (hek_mem k)

/-- 6.37 (Schur, one direction): if {lit}`minpoly 𝕜 T` is a product of linear
factors, then {lit}`T` is upper-triangular with respect to an orthonormal basis. -/
theorem exists_orthonormal_upperTriangular_of_minpoly (T : V →ₗ[𝕜] V)
    (h : ∃ (m : ℕ) (γ : Fin m → 𝕜),
      minpoly 𝕜 T = ∏ k, (Polynomial.X - Polynomial.C (γ k))) :
    ∃ (n : ℕ) (e : OrthonormalBasis (Fin n) 𝕜 V),
      ∀ k, T (e k) ∈ Submodule.span 𝕜 (e '' {i | i ≤ k}) :=
  exists_orthonormal_upperTriangular T
    ((exists_upperTriangular_iff_minpoly_eq_prod T).mpr h)

end Schur

/-- 6.38 (Schur's theorem) Every operator on a finite-dimensional complex inner
product space is upper-triangular with respect to some orthonormal basis. -/
theorem exists_orthonormal_upperTriangular_complex {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (T : V →ₗ[ℂ] V) :
    ∃ (n : ℕ) (e : OrthonormalBasis (Fin n) ℂ V),
      ∀ k, T (e k) ∈ Submodule.span ℂ (e '' {i | i ≤ k}) :=
  exists_orthonormal_upperTriangular T (LADR.Section_5C.exists_upperTriangular_complex T)

/-! # Linear Functionals on Inner Product Spaces -/

/-! 6.39 Definition: linear functional, dual space

A linear functional on {lit}`V` is a linear map {lit}`V → 𝕜`; the dual space is
{lit}`V →ₗ[𝕜] 𝕜` (see {module -checked}`LinearAlgebraDoneRightLean.Section_3F`). -/

/-! 6.40 Example: a linear functional such as {lit}`φ(z₁, z₂, z₃) = 2z₁ − 5z₂ + z₃`
on {lit}`𝔽³` can be written in the form {lit}`φ(z) = ⟨z, w⟩` (here {lit}`w =
(2, −5, 1)`). More generally, for any fixed {lit}`w ∈ V` the map {lit}`z ↦ ⟨w, z⟩`
is a (continuous) linear functional — mathlib's {name}`innerSL`. -/

noncomputable example (w : V) : V →L[𝕜] 𝕜 := innerSL 𝕜 w

example (w z : V) : innerSL 𝕜 w z = ⟪w, z⟫_𝕜 := rfl

/-! 6.42 Riesz representation theorem

If {lit}`V` is finite-dimensional and {lit}`φ` is a linear functional on
{lit}`V`, then there is a unique {lit}`v ∈ V` with {lit}`φ(u) = ⟨u, v⟩` for all
{lit}`u`. Reading Axler's {lit}`⟨u, v⟩` as mathlib's {lit}`⟪v, u⟫` (the slot in
which the inner product is genuinely linear — {lit}`u ↦ ⟪u, v⟫` would be
conjugate-linear, not a linear functional), this is mathlib's conjugate-linear
isometric isomorphism {name}`InnerProductSpace.toDual` between {lit}`V` and its
(continuous) dual. -/

theorem riesz_representation [FiniteDimensional 𝕜 V] (φ : V →ₗ[𝕜] 𝕜) :
    ∃! v : V, ∀ u : V, φ u = ⟪v, u⟫_𝕜 := by
  haveI : CompleteSpace V := FiniteDimensional.complete 𝕜 V
  -- On a finite-dimensional space every linear functional is continuous.
  let φ' : V →L[𝕜] 𝕜 := ⟨φ, φ.continuous_of_finiteDimensional⟩
  refine ⟨(InnerProductSpace.toDual 𝕜 V).symm φ', fun u => ?_, ?_⟩
  · have := InnerProductSpace.toDual_apply_apply (𝕜 := 𝕜)
      (x := (InnerProductSpace.toDual 𝕜 V).symm φ') (y := u)
    rw [LinearIsometryEquiv.apply_symm_apply] at this
    exact this
  · intro w hw
    apply (InnerProductSpace.toDual 𝕜 V).injective
    rw [LinearIsometryEquiv.apply_symm_apply]
    ext u
    rw [InnerProductSpace.toDual_apply_apply]
    exact (hw u).symm

/-! # Exercises 6B -/

/-- 6B.1 Converse to 6.24: if {lit}`‖a₁e₁ + ⋯ + aₘeₘ‖² = |a₁|² + ⋯ + |aₘ|²` for
all scalars, then {lit}`e₁, …, eₘ` is orthonormal. -/
theorem exercise_6B_1 {m : ℕ} (e : Fin m → V)
    (h : ∀ a : Fin m → 𝕜, ‖∑ i, a i • e i‖ ^ 2 = ∑ i, ‖a i‖ ^ 2) :
    Orthonormal 𝕜 e := by
  sorry

/-- 6B.2 (a) For {lit}`θ ∈ ℝ`, both {lit}`(cos θ, sin θ), (−sin θ, cos θ)` and
{lit}`(cos θ, sin θ), (sin θ, −cos θ)` are orthonormal bases of {lit}`ℝ²`. -/
theorem exercise_6B_2a (θ : ℝ) :
    Orthonormal ℝ ![((EuclideanSpace.equiv (Fin 2) ℝ).symm ![Real.cos θ, Real.sin θ]),
      ((EuclideanSpace.equiv (Fin 2) ℝ).symm ![-Real.sin θ, Real.cos θ])] := by
  sorry

/-- 6B.3 An orthonormal list {lit}`e₁, …, eₘ` satisfies Parseval's equality for a
vector {lit}`v` iff {lit}`v ∈ span(e₁, …, eₘ)`. -/
theorem exercise_6B_3 {m : ℕ} (e : Fin m → V) (he : Orthonormal 𝕜 e) (v : V) :
    ‖v‖ ^ 2 = ∑ i, ‖⟪e i, v⟫_𝕜‖ ^ 2 ↔
      v ∈ Submodule.span 𝕜 (Set.range e) := by
  sorry

/-- 6B.6 (a) If {lit}`e₁, …, eₙ` is an orthonormal basis and
{lit}`‖eₖ − vₖ‖ < 1/√n` for each {lit}`k`, then {lit}`v₁, …, vₙ` is a basis. -/
theorem exercise_6B_6a [FiniteDimensional 𝕜 V] {n : ℕ} (hn : n = finrank 𝕜 V)
    (b : OrthonormalBasis (Fin n) 𝕜 V) (v : Fin n → V)
    (h : ∀ k, ‖b k - v k‖ < 1 / Real.sqrt n) :
    LinearIndependent 𝕜 v := by
  sorry

/-- 6B.9 If {lit}`e₁, …, eₘ` results from Gram–Schmidt applied to a linearly
independent list {lit}`v₁, …, vₘ`, then {lit}`⟨vₖ, eₖ⟩ > 0` for each {lit}`k`. -/
theorem exercise_6B_9 {m : ℕ} (v : Fin m → V) (hv : LinearIndependent 𝕜 v) (k : Fin m) :
    0 < RCLike.re ⟪v k, InnerProductSpace.gramSchmidtNormed 𝕜 v k⟫_𝕜 := by
  sorry

/-- 6B.13 A list {lit}`v₁, …, vₘ` is linearly dependent iff Gram–Schmidt produces
{lit}`fₖ = 0` for some {lit}`k`. -/
theorem exercise_6B_13 {m : ℕ} (v : Fin m → V) :
    ¬ LinearIndependent 𝕜 v ↔ ∃ k, InnerProductSpace.gramSchmidt 𝕜 v k = 0 := by
  sorry

/-- 6B.15 If {lit}`⟨·, ·⟩₁` and {lit}`⟨·, ·⟩₂` are inner products with the same
orthogonal pairs, then one is a positive scalar multiple of the other. (Stated
for two inner-product structures {lit}`i₁, i₂` on the same space.) -/
theorem exercise_6B_15 {V : Type*} [AddCommGroup V] [Module 𝕜 V]
    (i₁ i₂ : InnerProductSpace.Core 𝕜 V)
    (h : ∀ u w : V, i₁.inner u w = 0 ↔ i₂.inner u w = 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ u w : V, i₁.inner u w = (c : 𝕜) * i₂.inner u w := by
  sorry

/-- 6B.18 If {lit}`u₁, …, uₘ` is linearly independent, there exists {lit}`v` with
{lit}`⟨uₖ, v⟩ = 1` for all {lit}`k`. -/
theorem exercise_6B_18 {m : ℕ} (u : Fin m → V) (hu : LinearIndependent 𝕜 u) :
    ∃ v : V, ∀ k, ⟪u k, v⟫_𝕜 = 1 := by
  sorry

/-- 6B.19 If {lit}`v₁, …, vₙ` is a basis of {lit}`V`, there is a basis
{lit}`u₁, …, uₙ` with {lit}`⟨vⱼ, uₖ⟩ = δⱼₖ` (a dual/biorthogonal basis). -/
theorem exercise_6B_19 [FiniteDimensional 𝕜 V] {n : ℕ}
    (v : Module.Basis (Fin n) 𝕜 V) :
    ∃ u : Module.Basis (Fin n) 𝕜 V, ∀ j k, ⟪v j, u k⟫_𝕜 = if j = k then 1 else 0 := by
  sorry

/-- 6B.21 Over {lit}`ℂ`, if all eigenvalues of {lit}`T` have absolute value less
than 1, then for every {lit}`ε > 0` there is {lit}`m` with {lit}`‖Tᵐv‖ ≤ ε‖v‖`
for all {lit}`v`. -/
theorem exercise_6B_21 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (T : V →ₗ[ℂ] V)
    (h : ∀ μ : ℂ, (∃ v : V, v ≠ 0 ∧ T v = μ • v) → ‖μ‖ < 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ m : ℕ, ∀ v : V, ‖(T ^ m) v‖ ≤ ε * ‖v‖ := by
  sorry

end LADR.Section_6B
