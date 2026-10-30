import OrbitComplexity.GroupActions.Rosenlicht.FunctionFields
import Mathlib.AlgebraicGeometry.AffineSpace

/-!
# Common affine domains for rational functions

A finite family of rational functions is represented by regular functions on one
affine open neighborhood of the generic point. This provides a common domain for
rational maps defined by finitely many coefficients.

## Main results

* `exists_affine_rationalChart`: simultaneous affine representatives of rational functions.
* `exists_affine_rationalMap`: the representatives give a morphism to affine space.
-/

namespace GroupActions

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u v

variable (X : Scheme.{u}) [IrreducibleSpace X]

/-- Finitely many rational functions have regular representatives on a common affine
open neighborhood of the generic point. -/
theorem exists_affine_rationalChart {ι : Type v} [Finite ι] (f : ι → X.functionField) :
    ∃ U : X.Opens, IsAffineOpen U ∧ ∃ hU : genericPoint X ∈ U,
      ∃ s : ι → Γ(X, U), ∀ i, X.presheaf.germ U (genericPoint X) hU (s i) = f i := by
  classical
  choose U hU s hs using fun i ↦ X.presheaf.exists_germ_eq (f i)
  have hV : genericPoint X ∈ (⨅ i, U i : X.Opens) := by
    change genericPoint X ∈ ((⨅ i, U i : X.Opens) : Set X)
    rw [TopologicalSpace.Opens.coe_iInf]
    exact Set.mem_iInter.mpr hU
  obtain ⟨V, hVa, hVη, hVU⟩ := exists_isAffineOpen_mem_and_subset hV
  have hle (i : ι) : V ≤ U i := hVU.trans (iInf_le U i)
  refine ⟨V, hVa, hVη, fun i ↦ X.presheaf.map (homOfLE (hle i)).op (s i), ?_⟩
  intro i
  rw [X.presheaf.germ_res_apply]
  exact hs i

end

end GroupActions
