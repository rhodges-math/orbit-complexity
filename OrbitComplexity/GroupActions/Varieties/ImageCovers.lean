import OrbitComplexity.GroupActions.Varieties.FullDimension
import OrbitComplexity.GroupActions.Varieties.ClosedCoverDimension

/-! # Dimension bounds from a finite ambient image cover

Pulling back closures of the covering images gives a finite closed cover of the source.
Each member embeds into one image closure, which bounds its dimension.
-/

open CategoryTheory AlgebraicGeometry Topology TopologicalSpace
namespace GroupActions.Variety
noncomputable section
universe u
variable {K : Type u} [Field K] {X Y : GroupActions.Variety K}
  {ι : Type*} [Finite ι] (j : X.toOver ⟶ Y.toOver) [IsImmersion j.left]
  (A : ι → GroupActions.Variety K) (f : ∀ i, (A i).toOver ⟶ Y.toOver)
  [∀ i, IsImmersion (f i).left] [∀ i, IrreducibleSpace (A i).scheme]

/-- A finite cover of an immersed image bounds its dimension by the covering dimensions. -/
theorem dim_le_of_finite_image_cover
    (hcover : Set.range j.left = ⋃ i, Set.range (f i).left)
    (d : WithBot ℕ∞) (hd : ∀ i, (A i).dim ≤ d) : X.dim ≤ d := by
  let C : ι → Set X.scheme := fun i => j.left ⁻¹' closure (Set.range (f i).left)
  change topologicalKrullDim X.scheme ≤ d
  apply topologicalKrullDim_le_closed_cover C
    (fun _ => isClosed_closure.preimage j.left.continuous)
  · intro x
    have hx : j.left x ∈ Set.range j.left := ⟨x, rfl⟩
    rw [hcover] at hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    exact ⟨i, subset_closure hi⟩
  · intro i
    have he : IsEmbedding (Set.codRestrict
        (fun x : C i => j.left x.val) (closure (Set.range (f i).left))
        (fun x => x.property)) :=
      (j.left.isEmbedding.comp IsEmbedding.subtypeVal).codRestrict _ _
    exact he.isInducing.topologicalKrullDim_le.trans
      ((dim_closure_range_immersion (f i)).le.trans (hd i))

end
end GroupActions.Variety
