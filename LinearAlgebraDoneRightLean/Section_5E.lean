import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.IsDiag
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Ring
import LinearAlgebraDoneRightLean.Section_2A
import LinearAlgebraDoneRightLean.Section_2B
import LinearAlgebraDoneRightLean.Section_2C
import LinearAlgebraDoneRightLean.Section_3C
import LinearAlgebraDoneRightLean.Section_3D
import LinearAlgebraDoneRightLean.Section_3E
import LinearAlgebraDoneRightLean.Section_5A
import LinearAlgebraDoneRightLean.Section_5B
import LinearAlgebraDoneRightLean.Section_5C
import LinearAlgebraDoneRightLean.Section_5D
import CompanionHelper

/-!
# Axler, *Linear Algebra Done Right* (4e) — Section 5E: Commuting Operators
-/

namespace LADR.Section_5E

open LADR.Section_2A (Spans)
open LADR.Section_2B (IsBasis exists_basis exists_basis_of_spans)
open LADR.Section_2C (isBasis_of_linearIndependent_of_card_eq
  isBasis_card_eq_finrank)
open LADR.Section_3C (matrixOf matrixOf_apply matrixOf_spec matrixOf_comp)
open LADR.Section_3D (IsInvertible)
open LADR.Section_5A (InvariantUnder IsEigenvalue IsEigenvector
  exercise_5A_38_quotient_op)
open LADR.Section_5B (quotOp quotOp_mkQ)
open LADR.Section_5C (IsUpperTriangular tfae_upperTriangular
  isEigenvalue_iff_diag)
open LADR.Section_5D (IsDiagonalizable isDiagonalizable_restrict
  apply_eq_smul_of_isDiag isDiag_matrixOf_of_eigenvectors)
open LinearMap (ker range)
open Module (Finite finrank)
open Polynomial (aeval)

universe u

variable {F : Type*} [Field F]
  {V : Type*} [AddCommGroup V] [Module F V]

/-! 5.71 Definition: commute.

Two operators {lit}`S, T ∈ ℒ(V)` *commute* if {lit}`ST = TS`; two square
matrices {lit}`A, B` commute if {lit}`AB = BA`. In mathlib this is the
general {name}`Commute` (for the multiplication of {name}`Module.End`
resp. of matrices). -/

example (S T : V →ₗ[F] V) : (S ∘ₗ T = T ∘ₗ S) ↔ Commute S T := by
  rw [Commute, SemiconjBy]
  exact Iff.rfl

-- {lit}`λI` commutes with every operator, and {lit}`p(T)` commutes with
-- {lit}`q(T)` (5.17).
example (T : V →ₗ[F] V) (lam : F) :
    (lam • LinearMap.id : V →ₗ[F] V) ∘ₗ T = T ∘ₗ (lam • LinearMap.id) := by
  ext v
  simp

example (T : V →ₗ[F] V) (p q : Polynomial F) :
    aeval T p ∘ₗ aeval T q = aeval T q ∘ₗ aeval T p :=
  LADR.Section_5A.aeval_comp_comm T p q

/-! 5.72/5.73 Example (not formalized): the partial differentiation
operators {lit}`∂/∂x` and {lit}`∂/∂y` on {lit}`𝒫ₘ(ℝ²)` commute, since mixed
partial derivatives of polynomials agree. (See Exercise 5E.8.) -/

/-! 5.74 Commuting operators correspond to commuting matrices. -/

theorem commute_iff_matrixOf_commute {n : ℕ} {v : Fin n → V}
    (hv : IsBasis F v) (S T : V →ₗ[F] V) :
    S ∘ₗ T = T ∘ₗ S ↔
      matrixOf hv hv S * matrixOf hv hv T =
        matrixOf hv hv T * matrixOf hv hv S := by
  constructor
  · intro h
    rw [← matrixOf_comp hv hv hv S T, ← matrixOf_comp hv hv hv T S, h]
  · intro h
    have hinj : Function.Injective
        (LinearMap.toMatrix hv.toModuleBasis hv.toModuleBasis) :=
      (LinearMap.toMatrix hv.toModuleBasis hv.toModuleBasis).injective
    apply hinj
    have h1 : LinearMap.toMatrix hv.toModuleBasis hv.toModuleBasis (S ∘ₗ T) =
        matrixOf hv hv S * matrixOf hv hv T := matrixOf_comp hv hv hv S T
    have h2 : LinearMap.toMatrix hv.toModuleBasis hv.toModuleBasis (T ∘ₗ S) =
        matrixOf hv hv T * matrixOf hv hv S := matrixOf_comp hv hv hv T S
    rw [h1, h2, h]

/-! 5.75 Eigenspaces are invariant under commuting operators. -/

theorem eigenspace_invariant_of_commute (S T : V →ₗ[F] V)
    (hcomm : S ∘ₗ T = T ∘ₗ S) (lam : F) :
    InvariantUnder T (Module.End.eigenspace S lam) := by
  intro v hv
  rw [Module.End.mem_eigenspace_iff] at hv ⊢
  -- {lit}`S(Tv) = T(Sv) = T(λv) = λ(Tv)`.
  have h := LinearMap.congr_fun hcomm v
  rw [LinearMap.comp_apply, LinearMap.comp_apply, hv, map_smul] at h
  exact h

/-! 5.76 Simultaneous diagonalizability is equivalent to commutativity (for
two diagonalizable operators). -/

private lemma mul_comm_of_isDiag {n : ℕ} {A B : Matrix (Fin n) (Fin n) F}
    (hA : A.IsDiag) (hB : B.IsDiag) : A * B = B * A := by
  ext i j
  rw [Matrix.mul_apply, Matrix.mul_apply]
  rcases eq_or_ne i j with rfl | hij
  · refine Finset.sum_congr rfl fun k _ => ?_
    rcases eq_or_ne k i with rfl | hki
    · exact mul_comm _ _
    · rw [hA (Ne.symm hki), hB (Ne.symm hki), zero_mul, zero_mul]
  · have h1 : ∀ k ∈ Finset.univ, A i k * B k j = 0 := by
      intro k _
      rcases eq_or_ne i k with rfl | hik
      · rw [hB hij, mul_zero]
      · rw [hA hik, zero_mul]
    have h2 : ∀ k ∈ Finset.univ, B i k * A k j = 0 := by
      intro k _
      rcases eq_or_ne i k with rfl | hik
      · rw [hA hij, mul_zero]
      · rw [hB hik, zero_mul]
    rw [Finset.sum_eq_zero h1, Finset.sum_eq_zero h2]

theorem commute_iff_simultaneously_diagonalizable [Finite F V]
    (S T : V →ₗ[F] V) (hS : IsDiagonalizable S) (hT : IsDiagonalizable T) :
    S ∘ₗ T = T ∘ₗ S ↔
      ∃ (n : ℕ) (v : Fin n → V) (hv : IsBasis F v),
        (matrixOf hv hv S).IsDiag ∧ (matrixOf hv hv T).IsDiag := by
  constructor
  · -- {lit}`V` is the sum of the eigenspaces of {lit}`S` (5.55); each is
    -- invariant under {lit}`T` (5.75), and {lit}`T` restricted there is
    -- diagonalizable (5.65). Concatenating bases of {lit}`T`-eigenvectors
    -- of the eigenspaces of {lit}`S` and extracting a basis (2.30) gives a
    -- basis of simultaneous eigenvectors.
    intro hcomm
    classical
    obtain ⟨nS, vS, hvS, hAS⟩ := hS
    set s : Finset F := Finset.univ.image fun k => matrixOf hvS hvS S k k
      with hs_def
    set mu : Fin s.card → F := fun k => (s.equivFin.symm k : F) with hmu_def
    have htop : (⨆ k, Module.End.eigenspace S (mu k)) = ⊤ := by
      rw [eq_top_iff, ← hvS.2, Submodule.span_le]
      rintro x ⟨j, rfl⟩
      have hj_mem : matrixOf hvS hvS S j j ∈ s :=
        Finset.mem_image_of_mem _ (Finset.mem_univ j)
      refine Submodule.mem_iSup_of_mem (s.equivFin ⟨_, hj_mem⟩) ?_
      have hval : mu (s.equivFin ⟨_, hj_mem⟩) = matrixOf hvS hvS S j j := by
        simp only [hmu_def, Equiv.symm_apply_apply]
      rw [hval]
      exact Module.End.mem_eigenspace_iff.mpr
        (apply_eq_smul_of_isDiag hvS S hAS j)
    have hinv : ∀ k, InvariantUnder T (Module.End.eigenspace S (mu k)) :=
      fun k => eigenspace_invariant_of_commute S T hcomm (mu k)
    have hrestr : ∀ k, IsDiagonalizable (hinv k).restrict :=
      fun k => isDiagonalizable_restrict T hT _ (hinv k)
    choose M u hu hdiag using hrestr
    set w : Fin (∑ k, M k) → V :=
      (fun p : (k : Fin s.card) × Fin (M k) => ((u p.1 p.2 : _) : V)) ∘
        ⇑finSigmaFinEquiv.symm with hw_def
    have hw_spans : Spans F w := by
      show Submodule.span F (Set.range w) = ⊤
      rw [hw_def, Set.range_comp, Equiv.range_eq_univ, Set.image_univ]
      rw [Set.range_sigma_eq_iUnion_range, Submodule.span_iUnion]
      rw [← htop]
      refine iSup_congr fun k => ?_
      have h1 : Submodule.span F
          (Set.range fun i => ((u k i : _) : V)) =
          Submodule.map (Module.End.eigenspace S (mu k)).subtype
            (Submodule.span F (Set.range (u k))) := by
        rw [Submodule.map_span, ← Set.range_comp]
        rfl
      have h2 : Submodule.span F (Set.range (u k)) = ⊤ := (hu k).2
      rw [h1, h2, Submodule.map_subtype_top]
    obtain ⟨n, v, hv, hsub⟩ := exists_basis_of_spans w hw_spans
    refine ⟨n, v, hv, isDiag_matrixOf_of_eigenvectors hv S ?_,
      isDiag_matrixOf_of_eigenvectors hv T ?_⟩
    · intro j
      obtain ⟨p, hp⟩ := hsub ⟨j, rfl⟩
      refine ⟨mu (finSigmaFinEquiv.symm p).1, ?_⟩
      have hmem : v j ∈ Module.End.eigenspace S
          (mu (finSigmaFinEquiv.symm p).1) := by
        rw [← hp]
        exact (u _ _).2
      exact Module.End.mem_eigenspace_iff.mp hmem
    · intro j
      obtain ⟨p, hp⟩ := hsub ⟨j, rfl⟩
      refine ⟨matrixOf (hu (finSigmaFinEquiv.symm p).1)
        (hu (finSigmaFinEquiv.symm p).1)
        (hinv (finSigmaFinEquiv.symm p).1).restrict
        (finSigmaFinEquiv.symm p).2 (finSigmaFinEquiv.symm p).2, ?_⟩
      have h1 := apply_eq_smul_of_isDiag (hu (finSigmaFinEquiv.symm p).1)
        (hinv (finSigmaFinEquiv.symm p).1).restrict
        (hdiag (finSigmaFinEquiv.symm p).1) (finSigmaFinEquiv.symm p).2
      have h2 := congrArg Subtype.val h1
      rw [Submodule.coe_smul,
        (hinv (finSigmaFinEquiv.symm p).1).restrict_apply] at h2
      rw [← hp]
      exact h2
  · -- Conversely, diagonal matrices commute, so {lit}`S` and {lit}`T`
    -- commute by 5.74.
    rintro ⟨n, v, hv, hAS, hAT⟩
    rw [commute_iff_matrixOf_commute hv S T]
    exact mul_comm_of_isDiag hAS hAT

/-! 5.78 Common eigenvector for commuting operators: every pair of
commuting operators on a finite-dimensional nonzero complex vector space
has a common eigenvector. -/

theorem exists_common_eigenvector {V : Type*} [AddCommGroup V] [Module ℂ V]
    [Finite ℂ V] [Nontrivial V] (S T : V →ₗ[ℂ] V)
    (hcomm : S ∘ₗ T = T ∘ₗ S) :
    ∃ v : V, v ≠ 0 ∧ (∃ lam : ℂ, S v = lam • v) ∧
      ∃ mu : ℂ, T v = mu • v := by
  -- {lit}`S` has an eigenvalue {lit}`λ` (5.19); the eigenspace
  -- {lit}`E(λ, S)` is invariant under {lit}`T` (5.75), so {lit}`T`
  -- restricted to it has an eigenvector (5.19 again).
  obtain ⟨lam, hlam⟩ := LADR.Section_5B.exists_eigenvalue S
  have hE_ne : Nontrivial (Module.End.eigenspace S lam) := by
    obtain ⟨x, hx_ne, hx_eq⟩ := hlam
    exact ⟨⟨x, Module.End.mem_eigenspace_iff.mpr hx_eq⟩, 0,
      fun h => hx_ne (by simpa using congrArg Subtype.val h)⟩
  have hinv : InvariantUnder T (Module.End.eigenspace S lam) :=
    eigenspace_invariant_of_commute S T hcomm lam
  obtain ⟨nu, u, hu_ne, hu_eq⟩ :=
    LADR.Section_5B.exists_eigenvalue hinv.restrict
  refine ⟨(u : V), fun h => hu_ne (Subtype.ext h),
    ⟨lam, Module.End.mem_eigenspace_iff.mp u.2⟩, ⟨nu, ?_⟩⟩
  have h := congrArg Subtype.val hu_eq
  rwa [Submodule.coe_smul, hinv.restrict_apply] at h

/-! 5.79 Example (not formalized): the partial differentiation operators on
{lit}`𝒫ₘ(ℝ², ℂ)` have the nonzero constant functions as their common
eigenvectors, as promised by 5.78. -/

/-! 5.80 Commuting operators are simultaneously upper triangularizable
(over {lit}`ℂ`). Proof by induction on {lit}`dim V`, using a common
eigenvector (5.78) and the quotient by its span. -/

private lemma simul_upperTriangular_aux :
    ∀ (N : ℕ) (W : Type u) (_ : AddCommGroup W),
      ∀ (_ : Module ℂ W) (_ : Module.Finite ℂ W), finrank ℂ W = N →
      ∀ S T : W →ₗ[ℂ] W, S ∘ₗ T = T ∘ₗ S →
      ∃ (n : ℕ) (v : Fin n → W) (hv : IsBasis ℂ v),
        IsUpperTriangular (matrixOf hv hv S) ∧
          IsUpperTriangular (matrixOf hv hv T) := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro W _ _ _ hW S T hcomm
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · -- {lit}`W = {0}`: the empty basis works.
      have hsub : Subsingleton W := by
        rw [← Module.finrank_zero_iff (R := ℂ)]
        exact hW
      refine ⟨0, Fin.elim0, ⟨linearIndependent_empty_type, ?_⟩, ?_, ?_⟩
      · show Submodule.span ℂ (Set.range Fin.elim0) = ⊤
        rw [Set.range_eq_empty, Submodule.span_empty, eq_top_iff]
        intro x _
        rw [Subsingleton.elim x 0]
        exact Submodule.zero_mem _
      · intro j _ _
        exact j.elim0
      · intro j _ _
        exact j.elim0
    · have : Nontrivial W :=
        Module.nontrivial_of_finrank_pos (R := ℂ) (by omega)
      obtain ⟨v₁, hv₁_ne, ⟨lamS, hlamS⟩, ⟨lamT, hlamT⟩⟩ :=
        exists_common_eigenvector S T hcomm
      set U : Submodule ℂ W := Submodule.span ℂ {v₁} with hU_def
      have hU_rank : finrank ℂ U = 1 := finrank_span_singleton hv₁_ne
      have hUS_inv : InvariantUnder S U := by
        intro x hx
        obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
        rw [map_smul, hlamS, smul_smul]
        exact Submodule.mem_span_singleton.mpr ⟨a * lamS, rfl⟩
      have hUT_inv : InvariantUnder T U := by
        intro x hx
        obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
        rw [map_smul, hlamT, smul_smul]
        exact Submodule.mem_span_singleton.mpr ⟨a * lamT, rfl⟩
      -- The quotient operators commute, and {lit}`dim(W/U) = N − 1`.
      have hcomm_q : quotOp S U hUS_inv ∘ₗ quotOp T U hUT_inv =
          quotOp T U hUT_inv ∘ₗ quotOp S U hUS_inv := by
        apply LinearMap.ext
        intro x
        obtain ⟨y, rfl⟩ := U.mkQ_surjective x
        rw [LinearMap.comp_apply, LinearMap.comp_apply, quotOp_mkQ,
          quotOp_mkQ, quotOp_mkQ, quotOp_mkQ]
        have h := LinearMap.congr_fun hcomm y
        simp only [LinearMap.comp_apply] at h
        rw [h]
      have hquot_rank : finrank ℂ (W ⧸ U) = N - 1 := by
        rw [LADR.Section_3E.finrank_quotient U, hW, hU_rank]
      obtain ⟨M, wq, hwq, hAS, hAT⟩ := ih (N - 1) (by omega) (W ⧸ U)
        inferInstance inferInstance inferInstance hquot_rank
        (quotOp S U hUS_inv) (quotOp T U hUT_inv) hcomm_q
      -- Lift the quotient basis and prepend the common eigenvector.
      choose wl hwl using fun i => U.mkQ_surjective (wq i)
      set v : Fin (M + 1) → W := Fin.cons v₁ wl with hv_def
      have hM : M = N - 1 := by
        rw [← hquot_rank]
        exact isBasis_card_eq_finrank wq hwq
      have hmkQ_v₁ : U.mkQ v₁ = 0 :=
        (Submodule.Quotient.mk_eq_zero U).mpr
          (Submodule.mem_span_singleton_self v₁)
      have hv_li : LinearIndependent ℂ v := by
        rw [Fintype.linearIndependent_iff]
        intro g hg
        have hg' : g 0 • v₁ + ∑ i : Fin M, g i.succ • wl i = 0 := by
          rw [Fin.sum_univ_succ] at hg
          exact hg
        -- Push to the quotient: the {lit}`wq` coefficients vanish.
        have hq : ∑ i : Fin M, g i.succ • wq i = 0 := by
          have h1 := congrArg U.mkQ hg'
          rw [map_add, map_smul, hmkQ_v₁, smul_zero, zero_add, map_sum,
            map_zero] at h1
          rw [← h1]
          exact Finset.sum_congr rfl fun i _ => by rw [map_smul, hwl i]
        have hzero_succ : ∀ i : Fin M, g i.succ = 0 :=
          Fintype.linearIndependent_iff.mp hwq.1 _ hq
        have hzero_0 : g 0 = 0 := by
          rw [Finset.sum_eq_zero (fun i _ => by
            rw [hzero_succ i, zero_smul]), add_zero] at hg'
          rcases smul_eq_zero.mp hg' with h | h
          · exact h
          · exact absurd h hv₁_ne
        intro j
        induction j using Fin.cases with
        | zero => exact hzero_0
        | succ i => exact hzero_succ i
      have hv_basis : IsBasis ℂ v :=
        isBasis_of_linearIndependent_of_card_eq v hv_li (by omega)
      -- Verify condition 5.39(c) for both operators.
      have hmain : ∀ (R : W →ₗ[ℂ] W) (hR_inv : InvariantUnder R U)
          (lamR : ℂ) (_ : R v₁ = lamR • v₁)
          (_ : IsUpperTriangular (matrixOf hwq hwq (quotOp R U hR_inv))),
          IsUpperTriangular (matrixOf hv_basis hv_basis R) := by
        intro R hR_inv lamR hlamR hAR
        apply ((tfae_upperTriangular hv_basis R).out 2 0).mp
        intro k
        induction k using Fin.cases with
        | zero =>
          -- {lit}`R v₁ = λ v₁ ∈ span(v₁)`.
          have h0 : v 0 = v₁ := rfl
          rw [h0, hlamR]
          exact Submodule.smul_mem _ _
            (Submodule.subset_span ⟨0, le_refl 0, h0⟩)
        | succ i =>
          -- Use the upper-triangular structure of the quotient operator.
          have hq30 := (tfae_upperTriangular hwq (quotOp R U hR_inv)).out 0 2
          have hq3 := hq30.mp hAR i
          have hsucc : v i.succ = wl i := rfl
          have hmkQ : U.mkQ (R (wl i)) ∈
              Submodule.map U.mkQ
                (Submodule.span ℂ (wl '' {j | j ≤ i})) := by
            rw [Submodule.map_span]
            have himg : ⇑U.mkQ '' (wl '' {j | j ≤ i}) =
                wq '' {j | j ≤ i} := by
              rw [← Set.image_comp]
              exact Set.image_congr fun j _ => by
                rw [Function.comp_apply, hwl j]
            rw [himg]
            have hRwl : U.mkQ (R (wl i)) =
                quotOp R U hR_inv (wq i) := by
              rw [← hwl i, quotOp_mkQ]
            rw [hRwl]
            exact hq3
          have hcomap := Submodule.mem_comap.mpr hmkQ
          rw [Submodule.comap_map_mkQ] at hcomap
          rw [hsucc]
          -- {lit}`U ⊔ span(wl '' {j ≤ i}) ⊆ span(v '' {j ≤ i+1})`.
          have hle : U ⊔ Submodule.span ℂ (wl '' {j | j ≤ i}) ≤
              Submodule.span ℂ (v '' {j | j ≤ i.succ}) := by
            apply sup_le
            · rw [hU_def, Submodule.span_le]
              rintro x rfl
              exact Submodule.subset_span ⟨0, Fin.zero_le _, rfl⟩
            · rw [Submodule.span_le]
              rintro x ⟨j, hj, rfl⟩
              refine Submodule.subset_span ⟨j.succ, ?_, rfl⟩
              rw [Set.mem_setOf_eq]
              exact Fin.succ_le_succ_iff.mpr hj
          exact hle hcomap
      exact ⟨M + 1, v, hv_basis,
        hmain S hUS_inv lamS hlamS hAS, hmain T hUT_inv lamT hlamT hAT⟩

theorem exists_simultaneous_upperTriangular {V : Type u} [AddCommGroup V]
    [Module ℂ V] [Finite ℂ V] (S T : V →ₗ[ℂ] V)
    (hcomm : S ∘ₗ T = T ∘ₗ S) :
    ∃ (n : ℕ) (v : Fin n → V) (hv : IsBasis ℂ v),
      IsUpperTriangular (matrixOf hv hv S) ∧
        IsUpperTriangular (matrixOf hv hv T) :=
  simul_upperTriangular_aux (finrank ℂ V) V inferInstance inferInstance
    inferInstance rfl S T hcomm

/-! 5.81 Eigenvalues of sums and products of commuting operators (over
{lit}`ℂ`): every eigenvalue of {lit}`S + T` is an eigenvalue of {lit}`S`
plus an eigenvalue of {lit}`T`, and every eigenvalue of {lit}`ST` is an
eigenvalue of {lit}`S` times an eigenvalue of {lit}`T`. -/

private lemma isUpperTriangular_add {n : ℕ}
    {A B : Matrix (Fin n) (Fin n) F} (hA : IsUpperTriangular A)
    (hB : IsUpperTriangular B) : IsUpperTriangular (A + B) := by
  intro j k hkj
  rw [Matrix.add_apply, hA j k hkj, hB j k hkj, add_zero]

private lemma isUpperTriangular_mul {n : ℕ}
    {A B : Matrix (Fin n) (Fin n) F} (hA : IsUpperTriangular A)
    (hB : IsUpperTriangular B) : IsUpperTriangular (A * B) := by
  intro j k hkj
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro i _
  by_cases hij : i < j
  · rw [hA j i hij, zero_mul]
  · rw [hB i k (lt_of_lt_of_le hkj (le_of_not_gt hij)), mul_zero]

private lemma mul_diag_of_isUpperTriangular {n : ℕ}
    {A B : Matrix (Fin n) (Fin n) F} (hA : IsUpperTriangular A)
    (hB : IsUpperTriangular B) (k : Fin n) :
    (A * B) k k = A k k * B k k := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_single k
  · intro i _ hik
    rcases lt_or_gt_of_ne hik with h | h
    · rw [hA k i h, zero_mul]
    · rw [hB i k h, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ k) h

private lemma matrixOf_add {n : ℕ} {v : Fin n → V} (hv : IsBasis F v)
    (S T : V →ₗ[F] V) :
    matrixOf hv hv (S + T) = matrixOf hv hv S + matrixOf hv hv T :=
  map_add (LinearMap.toMatrix hv.toModuleBasis hv.toModuleBasis) S T

theorem eigenvalue_add_of_commute {V : Type u} [AddCommGroup V]
    [Module ℂ V] [Finite ℂ V] (S T : V →ₗ[ℂ] V)
    (hcomm : S ∘ₗ T = T ∘ₗ S) (alpha : ℂ)
    (h : IsEigenvalue (S + T) alpha) :
    ∃ lam mu : ℂ, IsEigenvalue S lam ∧ IsEigenvalue T mu ∧
      alpha = lam + mu := by
  obtain ⟨n, v, hv, hAS, hAT⟩ := exists_simultaneous_upperTriangular S T hcomm
  have hsum : IsUpperTriangular (matrixOf hv hv (S + T)) := by
    rw [matrixOf_add hv S T]
    exact isUpperTriangular_add hAS hAT
  obtain ⟨k, hk⟩ := (isEigenvalue_iff_diag hv (S + T) hsum alpha).mp h
  rw [matrixOf_add hv S T, Matrix.add_apply] at hk
  exact ⟨matrixOf hv hv S k k, matrixOf hv hv T k k,
    (isEigenvalue_iff_diag hv S hAS _).mpr ⟨k, rfl⟩,
    (isEigenvalue_iff_diag hv T hAT _).mpr ⟨k, rfl⟩, hk.symm⟩

theorem eigenvalue_mul_of_commute {V : Type u} [AddCommGroup V]
    [Module ℂ V] [Finite ℂ V] (S T : V →ₗ[ℂ] V)
    (hcomm : S ∘ₗ T = T ∘ₗ S) (alpha : ℂ)
    (h : IsEigenvalue (S ∘ₗ T) alpha) :
    ∃ lam mu : ℂ, IsEigenvalue S lam ∧ IsEigenvalue T mu ∧
      alpha = lam * mu := by
  obtain ⟨n, v, hv, hAS, hAT⟩ := exists_simultaneous_upperTriangular S T hcomm
  have hprod_eq : matrixOf hv hv (S ∘ₗ T) =
      matrixOf hv hv S * matrixOf hv hv T := matrixOf_comp hv hv hv S T
  have hprod : IsUpperTriangular (matrixOf hv hv (S ∘ₗ T)) := by
    rw [hprod_eq]
    exact isUpperTriangular_mul hAS hAT
  obtain ⟨k, hk⟩ := (isEigenvalue_iff_diag hv (S ∘ₗ T) hprod alpha).mp h
  rw [hprod_eq, mul_diag_of_isUpperTriangular hAS hAT] at hk
  exact ⟨matrixOf hv hv S k k, matrixOf hv hv T k k,
    (isEigenvalue_iff_diag hv S hAS _).mpr ⟨k, rfl⟩,
    (isEigenvalue_iff_diag hv T hAT _).mpr ⟨k, rfl⟩, hk.symm⟩

/-! # Exercises -/

/-- 5E.1 -/
theorem exercise_5E_1 :
    ∃ S T : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ), S ∘ₗ T = T ∘ₗ S ∧
      (∃ U : Submodule ℝ (Fin 4 → ℝ),
        InvariantUnder S U ∧ ¬ InvariantUnder T U) ∧
      (∃ W : Submodule ℝ (Fin 4 → ℝ),
        InvariantUnder T W ∧ ¬ InvariantUnder S W) := by
  sorry

/-- 5E.2 A family of diagonalizable operators is simultaneously
diagonalizable iff its members pairwise commute. -/
theorem exercise_5E_2 [Finite F V] (𝒮 : Set (V →ₗ[F] V))
    (hdiag : ∀ E ∈ 𝒮, IsDiagonalizable E) :
    (∃ (n : ℕ) (v : Fin n → V) (hv : IsBasis F v),
      ∀ E ∈ 𝒮, (matrixOf hv hv E).IsDiag) ↔
    (∀ E ∈ 𝒮, ∀ E' ∈ 𝒮, E ∘ₗ E' = E' ∘ₗ E) := by
  sorry

/-- 5E.3 -/
theorem exercise_5E_3 (S T : V →ₗ[F] V) (hcomm : S ∘ₗ T = T ∘ₗ S)
    (p : Polynomial F) :
    InvariantUnder T (ker (aeval S p)) ∧
      InvariantUnder T (range (aeval S p)) := by
  sorry

/-- 5E.4 Prove or give a counterexample: if {lit}`A` is diagonal and
{lit}`B` is upper triangular (of the same size), then {lit}`A` and {lit}`B`
commute. (Stated for {lit}`2 × 2` real matrices.) -/
def exercise_5E_4 :
    Decidable (∀ A B : Matrix (Fin 2) (Fin 2) ℝ,
      A.IsDiag → IsUpperTriangular B → A * B = B * A) := by
  -- first line should be `apply isTrue` or `apply isFalse`
  sorry

/-- 5E.5 A pair of operators commutes iff their dual operators commute. -/
theorem exercise_5E_5 [Finite F V] (S T : V →ₗ[F] V) :
    S ∘ₗ T = T ∘ₗ S ↔
      S.dualMap ∘ₗ T.dualMap = T.dualMap ∘ₗ S.dualMap := by
  sorry

/-- 5E.6 -/
theorem exercise_5E_6 {V : Type*} [AddCommGroup V] [Module ℂ V]
    [Finite ℂ V] [Nontrivial V] (S T : V →ₗ[ℂ] V)
    (hcomm : S ∘ₗ T = T ∘ₗ S) :
    ∃ alpha lam : ℂ,
      range (S - alpha • (LinearMap.id : V →ₗ[ℂ] V)) ⊔
        range (T - lam • (LinearMap.id : V →ₗ[ℂ] V)) ≠ ⊤ := by
  sorry

/-- 5E.7 If {lit}`S` is diagonalizable and {lit}`T` commutes with {lit}`S`,
then there is a basis with respect to which {lit}`S` is diagonal and
{lit}`T` is upper triangular. -/
theorem exercise_5E_7 {V : Type*} [AddCommGroup V] [Module ℂ V]
    [Finite ℂ V] (S T : V →ₗ[ℂ] V) (hS : IsDiagonalizable S)
    (hcomm : S ∘ₗ T = T ∘ₗ S) :
    ∃ (n : ℕ) (v : Fin n → V) (hv : IsBasis ℂ v),
      (matrixOf hv hv S).IsDiag ∧ IsUpperTriangular (matrixOf hv hv T) := by
  sorry

/-- 5E.8 A basis of {lit}`𝒫₃(ℝ²)` with respect to which the two partial
differentiation operators both have upper-triangular matrices. (Stated for
any pair of operators implementing {lit}`∂/∂x` and {lit}`∂/∂y` on the space
of polynomials in two variables of total degree at most {lit}`3`.) -/
theorem exercise_5E_8
    (Dx Dy : MvPolynomial.restrictTotalDegree (Fin 2) ℝ 3 →ₗ[ℝ]
      MvPolynomial.restrictTotalDegree (Fin 2) ℝ 3)
    (hDx : ∀ p, (Dx p : MvPolynomial (Fin 2) ℝ) =
      MvPolynomial.pderiv 0 (p : MvPolynomial (Fin 2) ℝ))
    (hDy : ∀ p, (Dy p : MvPolynomial (Fin 2) ℝ) =
      MvPolynomial.pderiv 1 (p : MvPolynomial (Fin 2) ℝ)) :
    ∃ (n : ℕ) (v : Fin n → MvPolynomial.restrictTotalDegree (Fin 2) ℝ 3)
      (hv : IsBasis ℝ v),
      IsUpperTriangular (matrixOf hv hv Dx) ∧
        IsUpperTriangular (matrixOf hv hv Dy) := by
  sorry

/-- 5E.9 (a) For a (possibly infinite) family of pairwise commuting
operators on a finite-dimensional nonzero complex vector space, there is a
common eigenvector. -/
theorem exercise_5E_9a {V : Type*} [AddCommGroup V] [Module ℂ V]
    [Finite ℂ V] [Nontrivial V] (𝒮 : Set (V →ₗ[ℂ] V))
    (hcomm : ∀ S ∈ 𝒮, ∀ T ∈ 𝒮, S ∘ₗ T = T ∘ₗ S) :
    ∃ v : V, v ≠ 0 ∧ ∀ S ∈ 𝒮, ∃ lam : ℂ, S v = lam • v := by
  sorry

/-- 5E.9 (b) …and a basis with respect to which every member of the family
has an upper-triangular matrix. -/
theorem exercise_5E_9b {V : Type*} [AddCommGroup V] [Module ℂ V]
    [Finite ℂ V] (𝒮 : Set (V →ₗ[ℂ] V))
    (hcomm : ∀ S ∈ 𝒮, ∀ T ∈ 𝒮, S ∘ₗ T = T ∘ₗ S) :
    ∃ (n : ℕ) (v : Fin n → V) (hv : IsBasis ℂ v),
      ∀ S ∈ 𝒮, IsUpperTriangular (matrixOf hv hv S) := by
  sorry

/-- 5E.10 5.81 fails on real vector spaces. -/
theorem exercise_5E_10 :
    ∃ S T : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ), S ∘ₗ T = T ∘ₗ S ∧
      (∃ alpha : ℝ, IsEigenvalue (S + T) alpha ∧
        ¬ ∃ lam mu : ℝ, IsEigenvalue S lam ∧ IsEigenvalue T mu ∧
          alpha = lam + mu) ∧
      (∃ beta : ℝ, IsEigenvalue (S ∘ₗ T) beta ∧
        ¬ ∃ lam mu : ℝ, IsEigenvalue S lam ∧ IsEigenvalue T mu ∧
          beta = lam * mu) := by
  sorry

end LADR.Section_5E
