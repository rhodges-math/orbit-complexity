import OrbitComplexity.ReductiveGroups.Groups.Hopf.ConjugateQuotient
import OrbitComplexity.GroupActions.Varieties.AffineAutomorphisms
import OrbitComplexity.GroupActions.Varieties.BorelPoints
import OrbitComplexity.GroupActions.Varieties.OppositeBorelPoints
import OrbitComplexity.GroupActions.Varieties.ReductiveConjugation

/-! # Conjugation between the chosen opposite Borel varieties

The defining conjugated Hopf quotient gives the group isomorphism and
its square with the ambient reductive group.
-/

open CategoryTheory AlgebraicGeometry GroupActions ReductiveGroups TauCeti
open CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj

namespace SchubertGeometry
noncomputable section
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

omit [CharZero K] in
private instance borelReduced : IsReduced G.borelAlgebra := by
  have : Algebra.Smooth K G.borelAlgebra := G.borel_smooth
  exact TauCeti.isReduced_of_smooth K G.borelAlgebra

private instance oppositeReduced : IsReduced G.oppositeBorelAlgebra := by
  have : Algebra.Smooth K G.oppositeBorelAlgebra := G.oppositeBorel_smooth
  exact TauCeti.isReduced_of_smooth K G.oppositeBorelAlgebra

/-- Conjugation by the longest representative identifies Borel and opposite Borel. -/
def oppositeBorelConjugationIso :
    (borelVariety G).toOver ≅ (oppositeBorelVariety G).toOver :=
  affineGroupIso (conjugateQuotientEquiv G.borelIdeal G.longestPoint)

/-- The conjugation isomorphism is a morphism of group objects. -/
instance oppositeBorelConjugation_isMonHom :
    IsMonHom (oppositeBorelConjugationIso G).hom := by
  let : IsReduced (G.coordinateAlgebra ⧸ G.borelIdeal.toIdeal) := borelReduced G
  let : IsReduced
      (G.coordinateAlgebra ⧸ (G.borelIdeal.conjugate G.longestPoint).toIdeal) :=
    oppositeReduced G
  exact affineGroupIso_isMonHom (conjugateQuotientEquiv G.borelIdeal G.longestPoint)

/-- The Borel conjugation isomorphism agrees with ambient conjugation. -/
theorem oppositeBorelConjugation_comp :
    (oppositeBorelConjugationIso G).hom ≫ oppositeBorelInclusion G =
      borelInclusion G ≫ (reductiveConjugation G G.longestPoint).hom := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom
      (conjugateQuotientEquiv G.borelIdeal G.longestPoint).toAlgEquiv.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk G.oppositeBorelIdeal.toIdeal)) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk G.borelIdeal.toIdeal)) ≫
        Spec.map (CommRingCat.ofHom
          (HopfAlgebra.pointConjugationBialgEquiv G.longestPoint).toAlgEquiv.toRingHom)
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1

end
end SchubertGeometry
