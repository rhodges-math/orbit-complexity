import OrbitComplexity.SchubertGeometry.FlagVariety.Variety
import OrbitComplexity.SchubertGeometry.FlagVariety.OppositeChart
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Smoothness and dimension of the flag variety

The opposite-unipotent affine chart atlas proves smoothness and computes dimension.
-/

open CategoryTheory AlgebraicGeometry Topology

namespace SchubertGeometry
noncomputable section
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroups.ReductiveGroupData K)

private theorem oppositeUnipotentBaseSmooth :
    Smooth (GroupActions.oppositeUnipotentVariety G).toSpec := by
  change Smooth (Spec.map (CommRingCat.ofHom (algebraMap K G.oppositeUnipotentAlgebra)))
  exact (HasRingHomProperty.Spec_iff (P := @Smooth)).2
    (RingHom.smooth_algebraMap.mpr G.oppositeUnipotent_smooth)

/-- The flag variety is smooth over the base field. -/
instance flagVariety_smooth : Smooth (flagVariety G).toSpec := by
  change Smooth (flagSchemeToSpec G)
  let : ∀ i : (flagSchemeCover G).I₀, IsAffine ((flagSchemeCover G).X i) := fun i => by
    change IsAffine (Spec (CommRingCat.of G.oppositeUnipotentAlgebra))
    infer_instance
  apply HasRingHomProperty.of_source_openCover (P := @Smooth.{u}) (flagSchemeCover G)
  intro g
  change G.points at g
  have hfg : Smooth ((flagSchemeCover G).f g ≫ flagSchemeToSpec G) := by
    change Smooth (flagSchemeChart G g ≫ flagSchemeToSpec G)
    rw [flagSchemeChart_toSpec]
    exact oppositeUnipotentBaseSmooth G
  have : IsAffine ((flagSchemeCover G).X g) := by
    change IsAffine (Spec (CommRingCat.of G.oppositeUnipotentAlgebra))
    infer_instance
  exact HasRingHomProperty.appTop (@Smooth.{u}) _ hfg

/-- The flag variety has dimension the longest Weyl inversion count. -/
theorem flagVariety_dim :
    (flagVariety G).dim =
      ReductiveGroups.rootInversionCount G.rootBase G.longestElement := by
  let U := (flagSchemeChart G 1).opensRange
  have hdim : topologicalKrullDim U = (flagVariety G).dim :=
    (flagVariety G).open_dim U (Set.range_nonempty (flagSchemeChart G 1))
  let e := (flagSchemeChart G 1).isOpenEmbedding.isEmbedding.toHomeomorph
  have hchart : topologicalKrullDim (GroupActions.oppositeUnipotentVariety G).scheme =
      topologicalKrullDim U :=
    e.isHomeomorph.topologicalKrullDim_eq
  exact hdim.symm.trans (hchart.symm.trans (oppositeUnipotentVariety_dim G))

end
end SchubertGeometry