import OrbitComplexity.GroupActions.Varieties.ReductiveIntegral
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupOpposite
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Opposite unipotent subgroups as affine varieties

The coordinate Hopf algebra of the opposite unipotent subgroup defines an integral group variety.
The quotient map of coordinate algebras gives its closed inclusion into the reductive variety.

## Main definitions

* `GroupActions.oppositeUnipotentVariety`: the variety of the opposite unipotent subgroup.
* `GroupActions.oppositeUnipotentInclusion`: the closed inclusion into the reductive variety.

## Main results

* `GroupActions.oppositeUnipotentVarietyIntegral`: the opposite unipotent variety is integral.
* `GroupActions.oppositeUnipotentInclusion_isClosed`: the inclusion is a closed immersion.
* `GroupActions.oppositeUnipotentInclusion_isMonHom`: the inclusion preserves the group operation.
-/

open CategoryTheory AlgebraicGeometry

namespace GroupActions

noncomputable section

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroups.ReductiveGroupData K)

private theorem oppositeUnipotentSmooth : Algebra.Smooth K G.oppositeUnipotentAlgebra :=
  G.oppositeUnipotent_smooth

attribute [local instance] oppositeUnipotentSmooth

private theorem oppositeUnipotentReduced : IsReduced G.oppositeUnipotentAlgebra :=
  TauCeti.isReduced_of_smooth K G.oppositeUnipotentAlgebra

attribute [local instance] oppositeUnipotentReduced

/-- The affine variety represented by the coordinate algebra of the opposite unipotent subgroup. -/
def oppositeUnipotentVariety : Variety K := affineVariety K G.oppositeUnipotentAlgebra

/-- The variety of the opposite unipotent subgroup is connected. -/
instance oppositeUnipotentVarietyConnected : ConnectedSpace (oppositeUnipotentVariety G).scheme :=
  TauCeti.geometricallyConnectedCommHopfAlgProperty.connectedSpace K
    (CommHopfAlgCat.of K G.oppositeUnipotentAlgebra) G.oppositeUnipotent_geometricallyConnected

/-- The variety of the opposite unipotent subgroup is integral. -/
instance oppositeUnipotentVarietyIntegral : IsIntegral (oppositeUnipotentVariety G).scheme := by
  have : IsRegularRing G.oppositeUnipotentAlgebra := TauCeti.IsRegularRing.of_smooth (R := K)
  have : ∀ x : (oppositeUnipotentVariety G).scheme,
      IsRegularLocalRing ((oppositeUnipotentVariety G).scheme.presheaf.stalk x) := by
    change ∀ x : Spec (CommRingCat.of G.oppositeUnipotentAlgebra),
      IsRegularLocalRing ((Spec (CommRingCat.of G.oppositeUnipotentAlgebra)).presheaf.stalk x)
    intro x
    infer_instance
  exact TauCeti.AlgebraicGeometry.isIntegral_of_connected_of_isRegularLocalRing_stalk _

/-- The coordinate Hopf algebra gives the opposite unipotent variety its group-object structure. -/
instance oppositeUnipotentVarietyGroup : GrpObj (oppositeUnipotentVariety G).toOver := by
  change GrpObj ((Spec (CommRingCat.of G.oppositeUnipotentAlgebra)).asOver
    (Spec (CommRingCat.of K)))
  infer_instance

/-- Restriction of functions includes the opposite unipotent subgroup into the reductive group. -/
def oppositeUnipotentInclusion :
    (oppositeUnipotentVariety G).toOver ⟶ (reductiveVariety G).toOver :=
  ((hopfSpec (CommRingCat.of K)).map
    (TauCeti.CommHopfAlgCat.mkQuotient
      (CommHopfAlgCat.of K G.coordinateAlgebra) G.oppositeUnipotentIdeal).op).hom.hom

/-- The underlying Unipotent inclusion is the spectrum map of the coordinate quotient. -/
theorem oppositeUnipotentInclusion_left :
    (oppositeUnipotentInclusion G).left =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk G.oppositeUnipotentIdeal.toIdeal)) := rfl

/-- The inclusion of the opposite unipotent subgroup is a closed immersion. -/
instance oppositeUnipotentInclusion_isClosed :
    IsClosedImmersion (oppositeUnipotentInclusion G).left := by
  rw [oppositeUnipotentInclusion_left]
  exact IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

set_option backward.isDefEq.respectTransparency.types false in
/-- The opposite unipotent inclusion preserves multiplication. -/
instance oppositeUnipotentInclusion_isMonHom : IsMonHom (oppositeUnipotentInclusion G) := by
  change IsMonHom (((hopfSpec (CommRingCat.of K)).map
    (TauCeti.CommHopfAlgCat.mkQuotient
      (CommHopfAlgCat.of K G.coordinateAlgebra) G.oppositeUnipotentIdeal).op).hom.hom)
  infer_instance

end

end GroupActions
