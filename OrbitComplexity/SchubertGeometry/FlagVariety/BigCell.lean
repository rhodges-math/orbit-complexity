import OrbitComplexity.GroupActions.Varieties.AffineMulComplement
import OrbitComplexity.GroupActions.Varieties.AffineMulEtale
import OrbitComplexity.GroupActions.Varieties.AffineQuotientPoints
import OrbitComplexity.GroupActions.Varieties.ReductiveVariety
import OrbitComplexity.SchubertGeometry.FlagVariety.AffineOpen
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupOppositePoints

/-!
# The big cell in a reductive group

Multiplication embeds the opposite unipotent subgroup times the Borel as an open subvariety
of the reductive group. Complementary tangent images give etaleness, while disjoint subgroup
points give universal injectivity.

## Main definitions

* `SchubertGeometry.bigCellCoordinate`: the restricted multiplication coordinate map.
* `SchubertGeometry.bigCellVariety`: the affine product of the two subgroup varieties.
* `SchubertGeometry.bigCellMorphism`: multiplication over the base field.

## Main results

* `SchubertGeometry.bigCellMorphism_isOpen`: the big-cell open immersion.
-/

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace SchubertGeometry

noncomputable section

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroups.ReductiveGroupData K)

omit [IsAlgClosed K] [CharZero K] in
private theorem bigCellGroupSmooth : Algebra.Smooth K G.coordinateAlgebra := G.reductive.smooth
private theorem bigCellUnipotentSmooth : Algebra.Smooth K G.oppositeUnipotentAlgebra :=
  G.oppositeUnipotent_smooth
omit [CharZero K] in
private theorem bigCellBorelSmooth : Algebra.Smooth K G.borelAlgebra := G.borel_smooth

attribute [local instance] bigCellGroupSmooth bigCellUnipotentSmooth bigCellBorelSmooth

private theorem bigCellProductSmooth :
    Algebra.Smooth K (G.oppositeUnipotentAlgebra ⊗[K] G.borelAlgebra) :=
  Algebra.Smooth.comp K G.oppositeUnipotentAlgebra _

attribute [local instance] bigCellProductSmooth

omit [IsAlgClosed K] [CharZero K] in
private theorem bigCellGroupReduced : IsReduced G.coordinateAlgebra :=
  TauCeti.isReduced_of_smooth K G.coordinateAlgebra
private theorem bigCellUnipotentReduced : IsReduced G.oppositeUnipotentAlgebra :=
  TauCeti.isReduced_of_smooth K G.oppositeUnipotentAlgebra
private theorem bigCellProductReduced :
    IsReduced (G.oppositeUnipotentAlgebra ⊗[K] G.borelAlgebra) :=
  TauCeti.isReduced_of_smooth K (G.oppositeUnipotentAlgebra ⊗[K] G.borelAlgebra)

attribute [local instance] bigCellGroupReduced bigCellUnipotentReduced bigCellProductReduced

/-- The coordinate map of multiplication from the opposite unipotent subgroup and the Borel. -/
def bigCellCoordinate : G.coordinateAlgebra →ₐ[K]
    G.oppositeUnipotentAlgebra ⊗[K] G.borelAlgebra :=
  GroupActions.affineMulMap
    (TauCeti.CommHopfAlgCat.mkQuotient
      (CommHopfAlgCat.of K G.coordinateAlgebra) G.oppositeUnipotentIdeal).hom.toAlgHom
    (TauCeti.CommHopfAlgCat.mkQuotient
      (CommHopfAlgCat.of K G.coordinateAlgebra) G.borelIdeal).hom.toAlgHom

private theorem bigCellCoordinate_etale : (bigCellCoordinate G).toRingHom.Etale := by
  let qI : G.coordinateAlgebra →ₐc[K] G.oppositeUnipotentAlgebra :=
    (TauCeti.CommHopfAlgCat.mkQuotient
      (CommHopfAlgCat.of K G.coordinateAlgebra) G.oppositeUnipotentIdeal).hom
  let qJ : G.coordinateAlgebra →ₐc[K] G.borelAlgebra := (TauCeti.CommHopfAlgCat.mkQuotient
    (CommHopfAlgCat.of K G.coordinateAlgebra) G.borelIdeal).hom
  have hbij : Function.Bijective (GroupActions.affineMulTangent qI qJ) :=
    GroupActions.affineMulTangent_bijective_of_isCompl qI qJ
      (TauCeti.CommHopfAlgCat.mkQuotient_surjective _ _)
      (TauCeti.CommHopfAlgCat.mkQuotient_surjective _ _) G.oppositeUnipotent_isCompl_borel
  exact GroupActions.affineMulMap_etale qI qJ hbij

/-- The affine variety of the opposite unipotent subgroup times the Borel. -/
def bigCellVariety : GroupActions.Variety K :=
  GroupActions.affineVariety K (G.oppositeUnipotentAlgebra ⊗[K] G.borelAlgebra)

/-- Multiplication from the opposite unipotent subgroup times the Borel into the group. -/
def bigCellMorphism : (bigCellVariety G).toOver ⟶ (GroupActions.reductiveVariety G).toOver :=
  (algSpec (CommRingCat.of K)).map (CommAlgCat.ofHom (bigCellCoordinate G)).op

/-- The big-cell morphism is the spectrum map of the multiplication coordinates. -/
theorem bigCellMorphism_left :
    (bigCellMorphism G).left = Spec.map (CommRingCat.ofHom (bigCellCoordinate G).toRingHom) := rfl

/-- Opposite unipotent times Borel multiplication is an open immersion. -/
instance bigCellMorphism_isOpen : IsOpenImmersion (bigCellMorphism G).left :=
  affineOpenImmersion_of_points (bigCellCoordinate G) (bigCellCoordinate_etale G)
    (GroupActions.quotientMulMap_injective G.oppositeUnipotentIdeal G.borelIdeal
      G.oppositeUnipotentPoints_disjoint)

end

end SchubertGeometry
