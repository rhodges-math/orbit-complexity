import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Coordinate charts for finite-dimensional relation spaces

A family of separating linear forms on a finite-dimensional vector space contains
a finite family giving a coordinate chart. Applied to coefficient maps, these
charts uniquely normalize vectors in polynomial relation spaces.

## Main results

* `exists_linearCoordinateChart`: separating linear forms give a finite coordinate chart.
-/

namespace GroupActions

noncomputable section

universe v w

variable {F : Type v} [Field F] {ι : Type w}

/-- A family of linear forms separating points of a finite-dimensional space contains
a finite family giving a linear coordinate chart. -/
theorem exists_linearCoordinateChart {V : Type*} [AddCommGroup V] [Module F V]
    [Module.Finite F V] (L : ι → Module.Dual F V)
    (hL : ∀ z : V, z ≠ 0 → ∃ i, L i z ≠ 0) :
    ∃ (s : Set (Module.Dual F V)) (_ : s.Finite) (c : s → ι)
      (e : V ≃ₗ[F] (s → F)), ∀ (z : V) (j : s), e z j = L (c j) z := by
  classical
  have hspan : Submodule.span F (Set.range L) = ⊤ := by
    apply Submodule.span_eq_top_of_ne_zero
    intro z hz
    obtain ⟨i, hi⟩ := hL z hz
    exact ⟨L i, Set.mem_range_self i, hi⟩
  let s : Set (Module.Dual F V) :=
    (linearIndepOn_empty F id).extend (Set.empty_subset (Set.range L))
  let b : Module.Basis s F (Module.Dual F V) := Module.Basis.ofSpan hspan.ge
  have : Finite s := Module.Finite.finite_basis b
  have hc : ∀ j : s, ∃ i, L i = b j := by
    intro j
    exact Module.Basis.ofSpan_subset hspan.ge (Set.mem_range_self j)
  let c : s → ι := fun j ↦ (hc j).choose
  let e : V ≃ₗ[F] (s → F) :=
    (Module.evalEquiv F V).trans b.dualBasis.equivFun
  refine ⟨_, Set.toFinite _, c, e, ?_⟩
  intro z j
  change b.dualBasis.equivFun ((Module.evalEquiv F V) z) j = _
  rw [Module.Basis.dualBasis_equivFun]
  change (b j) z = L (c j) z
  rw [← (hc j).choose_spec]

end

end GroupActions
