import OrbitComplexity.GroupActions.Varieties.RootSubgroupPoints
import OrbitComplexity.GroupActions.Varieties.AffineMultiplication
import OrbitComplexity.GroupActions.Rosenlicht.TensorDomains
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupRootProductCoordinates

/-! # Multiplication isomorphisms for closed root subgroups

The affine product of two disjoint closed root supports is their union subgroup.
-/

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace GroupActions
noncomputable section
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroups.ReductiveGroupData K)
  (R R₁ R₂ : Set G.rootIndex)
  (hR : ReductiveGroups.IsPositiveRootClosed G.rootBase R)
  (hR₁ : ReductiveGroups.IsPositiveRootClosed G.rootBase R₁)
  (hR₂ : ReductiveGroups.IsPositiveRootClosed G.rootBase R₂)

private theorem rootProductDomain :
    IsDomain (G.rootSubsetAlgebra R₁ hR₁ ⊗[K] G.rootSubsetAlgebra R₂ hR₂) :=
  isDomain_tensorProduct

attribute [local instance] rootProductDomain

private theorem rootProductFiniteType :
    Algebra.FiniteType K (G.rootSubsetAlgebra R₁ hR₁ ⊗[K] G.rootSubsetAlgebra R₂ hR₂) :=
  Algebra.FiniteType.trans
    (inferInstance : Algebra.FiniteType K (G.rootSubsetAlgebra R₁ hR₁))
    (inferInstance : Algebra.FiniteType (G.rootSubsetAlgebra R₁ hR₁)
      (G.rootSubsetAlgebra R₁ hR₁ ⊗[K] G.rootSubsetAlgebra R₂ hR₂))

attribute [local instance] rootProductFiniteType

/-- The affine product of two closed root-subgroup varieties. -/
def rootProductVariety : Variety K :=
  affineVariety K (G.rootSubsetAlgebra R₁ hR₁ ⊗[K] G.rootSubsetAlgebra R₂ hR₂)

/-- Points of a root-subgroup product are pairs of subgroup points. -/
def rootProductPointsEquiv :
    (rootProductVariety G R₁ R₂ hR₁ hR₂).points ≃
      (rootSubsetVariety G R₁ hR₁).points × (rootSubsetVariety G R₂ hR₂).points :=
  affineProductPointsEquiv K (G.rootSubsetAlgebra R₁ hR₁) (G.rootSubsetAlgebra R₂ hR₂)

/-- Multiplication identifies disjoint closed root factors with their union subgroup. -/
def rootProductIso (hunion : R = R₁ ∪ R₂) (hdisj : Disjoint R₁ R₂) :
    (rootProductVariety G R₁ R₂ hR₁ hR₂).toOver ≅ (rootSubsetVariety G R hR).toOver :=
  (algSpec (CommRingCat.of K)).mapIso
    (CommAlgCat.isoMk (G.rootSubsetProductEquiv R R₁ R₂ hR hR₁ hR₂ hunion hdisj)).op

/-- The root-product isomorphism is the pullback of ambient group multiplication. -/
theorem rootProductIso_hom_comp (hunion : R = R₁ ∪ R₂) (hdisj : Disjoint R₁ R₂) :
    (rootProductIso G R R₁ R₂ hR hR₁ hR₂ hunion hdisj).hom ≫
        rootSubsetInclusion G R hR =
      (algSpec (CommRingCat.of K)).map (CommAlgCat.ofHom (affineMulMap
        (Ideal.Quotient.mkₐ K (G.rootSubsetIdeal R₁ hR₁).toIdeal)
        (Ideal.Quotient.mkₐ K (G.rootSubsetIdeal R₂ hR₂).toIdeal))).op := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom
      (G.rootSubsetProductEquiv R R₁ R₂ hR hR₁ hR₂ hunion hdisj).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (G.rootSubsetIdeal R hR).toIdeal)) = _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  ext b
  exact G.rootSubsetProductEquiv_mk R R₁ R₂ hR hR₁ hR₂ hunion hdisj b

end
end GroupActions
