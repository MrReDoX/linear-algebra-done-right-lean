import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Tactic.Linter.Style
import CompanionHelper

/-!
# Axler, *Linear Algebra Done Right* (4e) — Section 8D: Trace
-/

namespace LADR.Section_8D

open scoped InnerProductSpace
open Module (finrank)

section Field

variable {F : Type*} [Field F]
  {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]

/-! 8.50 The trace of the matrix of an operator does not depend on the basis.

For any two bases {lit}`b`, {lit}`c` of {lit}`V`, the matrices {lit}`ℳ(T, b)`
and {lit}`ℳ(T, c)` have the same trace — both equal the basis-independent
{name}`LinearMap.trace`. -/
theorem trace_toMatrix_indep {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    [DecidableEq κ] (b : Module.Basis ι F V) (c : Module.Basis κ F V) (T : V →ₗ[F] V) :
    (LinearMap.toMatrix b b T).trace = (LinearMap.toMatrix c c T).trace := by
  rw [← LinearMap.trace_eq_matrix_trace F b T, ← LinearMap.trace_eq_matrix_trace F c T]

/-! 8.51 Definition: trace of an operator, {lit}`tr T`.

By 8.50 the definition {lit}`tr T = ` trace of the matrix of {lit}`T` (with
respect to any basis) makes sense; this is mathlib's {name}`LinearMap.trace`. -/

theorem trace_eq_toMatrix_trace {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι F V) (T : V →ₗ[F] V) :
    LinearMap.trace F V T = (LinearMap.toMatrix b b T).trace :=
  LinearMap.trace_eq_matrix_trace F b T

/-! 8.54 Trace and the characteristic polynomial.

For {lit}`n = dim V`, {lit}`tr T` equals the negative of the coefficient of
{lit}`z^{n-1}` in the characteristic polynomial of {lit}`T`. This is the
operator form of {name}`Matrix.trace_eq_neg_charpoly_coeff`. -/
theorem trace_eq_neg_charpoly_coeff [Nontrivial V] (T : V →ₗ[F] V) :
    LinearMap.trace F V T = -(T.charpoly).coeff (finrank F V - 1) := by
  classical
  haveI : Nonempty (Fin (finrank F V)) := ⟨⟨0, Module.finrank_pos⟩⟩
  let b := Module.finBasis F V
  have hcard : Fintype.card (Fin (finrank F V)) = finrank F V := by simp
  rw [trace_eq_toMatrix_trace b, Matrix.trace_eq_neg_charpoly_coeff,
    LinearMap.charpoly_toMatrix T b, hcard]

/-! 8.56 The trace is linear, and {lit}`tr(ST) = tr(TS)`. -/

theorem trace_add (S T : V →ₗ[F] V) :
    LinearMap.trace F V (S + T) = LinearMap.trace F V S + LinearMap.trace F V T :=
  map_add _ _ _

theorem trace_smul (a : F) (T : V →ₗ[F] V) :
    LinearMap.trace F V (a • T) = a • LinearMap.trace F V T :=
  map_smul _ _ _

theorem trace_comp_comm (S T : V →ₗ[F] V) :
    LinearMap.trace F V (S ∘ₗ T) = LinearMap.trace F V (T ∘ₗ S) :=
  LinearMap.trace_mul_comm F S T

/-! 8.57 There is no pair {lit}`S, T ∈ ℒ(V)` with {lit}`ST - TS = I` (when the
dimension of {lit}`V` is nonzero in {lit}`F`, e.g. always in characteristic 0),
because {lit}`tr(ST - TS) = 0` while {lit}`tr I = dim V`. -/
theorem sub_comp_comm_ne_one [Nontrivial V] (hF : (finrank F V : F) ≠ 0)
    (S T : V →ₗ[F] V) : S ∘ₗ T - T ∘ₗ S ≠ LinearMap.id := by
  intro h
  have h0 : LinearMap.trace F V (S ∘ₗ T - T ∘ₗ S) = 0 := by
    rw [map_sub, trace_comp_comm, sub_self]
  rw [h, LinearMap.trace_id] at h0
  exact hF h0

end Field

section Complex

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-! 8.52 On complex vector spaces, the trace equals the sum of the eigenvalues,
each included as many times as its multiplicity.

Axler's "eigenvalues with multiplicity" are the roots of the characteristic
polynomial; over {lit}`ℂ` (algebraically closed) {lit}`tr T` is their sum. This
is the operator form of {name}`Matrix.trace_eq_sum_roots_charpoly`. -/
theorem trace_eq_sum_roots_charpoly (T : V →ₗ[ℂ] V) :
    LinearMap.trace ℂ V T = (T.charpoly).roots.sum := by
  classical
  let b := Module.finBasis ℂ V
  rw [trace_eq_toMatrix_trace b, Matrix.trace_eq_sum_roots_charpoly,
    LinearMap.charpoly_toMatrix T b]

end Complex

section Inner

variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]

/-! 8.55 Trace on an inner product space.

If {lit}`e₁, …, eₙ` is an orthonormal basis of {lit}`V`, then
{lit}`tr T = ∑ₖ ⟨T eₖ, eₖ⟩`. (mathlib conjugates the *first* slot, so the
statement reads {lit}`tr T = ∑ₖ ⟨eₖ, T eₖ⟩`; over a real space the two agree,
and over {lit}`ℂ` they are complex conjugates whose sum equals {lit}`tr T`.) -/
theorem trace_eq_sum_inner {ι : Type*} [Fintype ι] (T : E →ₗ[𝕜] E)
    (b : OrthonormalBasis ι 𝕜 E) :
    LinearMap.trace 𝕜 E T = ∑ i, ⟪b i, T (b i)⟫_𝕜 :=
  T.trace_eq_sum_inner b

end Inner

/-! # Exercises 8D -/

section Exercises

variable {F : Type*} [Field F]
  {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]

/-- 8D.2 If {lit}`P² = P` then {lit}`tr P = dim (range P)`. -/
theorem exercise_8D_2 (P : V →ₗ[F] V) (hP : P ∘ₗ P = P) :
    LinearMap.trace F V P = (finrank F (LinearMap.range P) : F) := by
  sorry

/-- 8D.7 If {lit}`tr (S ∘ₗ T) = 0` for all {lit}`S ∈ ℒ(V)`, then {lit}`T = 0`. -/
theorem exercise_8D_7 (T : V →ₗ[F] V)
    (h : ∀ S : V →ₗ[F] V, LinearMap.trace F V (S ∘ₗ T) = 0) : T = 0 := by
  sorry

end Exercises

end LADR.Section_8D
