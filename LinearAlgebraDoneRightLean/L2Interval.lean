import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.Topology.ContinuousMap.Compact

/-!
# Skippable infrastructure: the L² inner product space `C[a,b]`

**A reader of the companion can skip this file entirely.** It contains no Axler
content — it exists only so that the function-space exercises (6C.16, 7A.31,
7C.25, …) have an inner product space to be stated in.

The obstruction it works around: mathlib puts the *supremum* norm on
`C(Set.Icc a b, ℝ)` and provides no measure on the interval subtype, whereas Axler
uses the `L²` inner product `⟨f, g⟩ = ∫ₐᵇ f g`. So we (i) equip the interval
subtype with its Lebesgue measure and (ii) introduce a type synonym `L2C a b`
carrying the `L²` inner product instead of the sup norm. The three analytic axioms
of the inner product (symmetry, positivity, definiteness) are left as `sorry`, in
the same spirit as the exercises themselves.
-/

open MeasureTheory

noncomputable instance instMeasureSpaceIcc {a b : ℝ} : MeasureSpace (Set.Icc a b) :=
  Measure.Subtype.measureSpace

/-- `C[a, b]` carrying the `L²` inner product — a type synonym for
`C(Set.Icc a b, ℝ)` that avoids mathlib's sup-norm instance. -/
def L2C (a b : ℝ) : Type := C(Set.Icc a b, ℝ)

namespace L2C

variable {a b : ℝ}

instance : AddCommGroup (L2C a b) := inferInstanceAs (AddCommGroup C(Set.Icc a b, ℝ))
noncomputable instance : Module ℝ (L2C a b) := inferInstanceAs (Module ℝ C(Set.Icc a b, ℝ))

/-- View an element of `L2C a b` as an ordinary continuous function. -/
def toCont (f : L2C a b) : C(Set.Icc a b, ℝ) := f

/-- The `L²` inner product `⟨f, g⟩ = ∫ₐᵇ f g` on `C[a, b]`. -/
noncomputable def core : InnerProductSpace.Core ℝ (L2C a b) where
  inner f g := ∫ x, f.toCont x * g.toCont x
  conj_inner_symm := by sorry
  re_inner_nonneg := by sorry
  add_left := by sorry
  smul_left := by sorry
  definite := by sorry

noncomputable instance : NormedAddCommGroup (L2C a b) := core.toNormedAddCommGroup
noncomputable instance : InnerProductSpace ℝ (L2C a b) := InnerProductSpace.ofCore _

end L2C

-- sanity: the orthogonal complement of a subspace is available
noncomputable example {a b : ℝ} (U : Submodule ℝ (L2C a b)) : Submodule ℝ (L2C a b) := Uᗮ
