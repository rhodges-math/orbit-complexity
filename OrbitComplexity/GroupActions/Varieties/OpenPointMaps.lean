import OrbitComplexity.GroupActions.Varieties.OpenPoints
import OrbitComplexity.GroupActions.Varieties.OpenSubvarieties

/-! # Open maps on rational points

An open morphism of varieties maps rational open subsets to rational open subsets.
-/

open CategoryTheory AlgebraicGeometry Topology

namespace GroupActions.Variety
noncomputable section
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] {X Y : GroupActions.Variety K}

/-- An open morphism of varieties induces an open map on rational points. -/
theorem isOpenMap_mapPoints (f : X.toOver ⟶ Y.toOver) (hf : IsOpenMap f.left) :
    IsOpenMap (mapPoints f) := by
  intro U hU
  obtain ⟨V, hV, rfl⟩ := X.isEmbedding_pointMap.isOpen_iff.mp hU
  have he : mapPoints f '' (X.pointMap ⁻¹' V) = Y.pointMap ⁻¹' (f.left '' V) := by
    ext y
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨X.pointMap p, hp, pointMap_mapPoints f p⟩
    · rintro ⟨z, hzV, hzy⟩
      let W : X.scheme.Opens := ⟨V, hV⟩
      let g := X.openInclusion W ≫ f
      have hy : Y.pointMap y ∈ Set.range g.left := ⟨⟨z, hzV⟩, hzy⟩
      obtain ⟨p, hp⟩ := exists_mapPoints_eq g y hy
      refine ⟨mapPoints (X.openInclusion W) p, ?_, ?_⟩
      · change X.pointMap (mapPoints (X.openInclusion W) p) ∈ V
        rw [pointMap_mapPoints]
        exact ((X.openSubvariety W).pointMap p).property
      · exact (mapPoints_comp (X.openInclusion W) f p).symm.trans hp
  rw [he]
  exact (hf V hV).preimage Y.continuous_pointMap

end
end GroupActions.Variety