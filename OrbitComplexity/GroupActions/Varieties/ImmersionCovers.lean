import OrbitComplexity.GroupActions.Varieties.FullDimension
import OrbitComplexity.GroupActions.Varieties.ClosedCoverDimension
import OrbitComplexity.GroupActions.Varieties.PointImageIso

/-! # Dimension bounds from finite immersion covers

A finite cover by irreducible immersed varieties bounds dimension by their dimensions.
Over an algebraically closed field, a rational-point cover already gives the scheme cover.
-/

open CategoryTheory AlgebraicGeometry Topology TopologicalSpace
namespace GroupActions.Variety
noncomputable section
universe u
variable {K : Type u} [Field K] (X : GroupActions.Variety K)
  {ι : Type*} [Finite ι] (A : ι → GroupActions.Variety K)
  (f : ∀ i, (A i).toOver ⟶ X.toOver)
  [∀ i, IsImmersion (f i).left] [∀ i, IrreducibleSpace (A i).scheme]

/-- A finite immersion cover bounds dimension by any common bound for its sources. -/
theorem dim_le_of_finite_immersion_cover
    (hcover : ∀ x : X.scheme, ∃ i, x ∈ Set.range (f i).left)
    (d : WithBot ℕ∞) (hd : ∀ i, (A i).dim ≤ d) : X.dim ≤ d := by
  change topologicalKrullDim X.scheme ≤ d
  apply topologicalKrullDim_le_closed_cover (fun i => closure (Set.range (f i).left))
    (fun _ => isClosed_closure)
  · intro x
    obtain ⟨i, hi⟩ := hcover x
    exact ⟨i, subset_closure hi⟩
  · intro i
    exact (dim_closure_range_immersion (f i)).le.trans (hd i)

end
end GroupActions.Variety
