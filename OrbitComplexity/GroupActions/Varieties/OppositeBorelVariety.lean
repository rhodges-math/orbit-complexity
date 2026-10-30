import OrbitComplexity.GroupActions.Varieties.ReductiveIntegral
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupOpposite
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Opposite Borel subgroups as affine varieties

The coordinate Hopf algebra of the opposite Borel subgroup defines an integral group variety.
The quotient map of coordinate algebras gives its closed inclusion into the reductive variety.

## Main definitions

* `GroupActions.oppositeBorelVariety`: the variety of the opposite Borel subgroup.
* `GroupActions.oppositeBorelInclusion`: its closed inclusion into the reductive variety.

## Main results

* `GroupActions.oppositeBorelVarietyIntegral`: the opposite Borel variety is integral.
* `GroupActions.oppositeBorelInclusion_isClosed`: the inclusion is a closed immersion.
* `GroupActions.oppositeBorelInclusion_isMonHom`: the inclusion preserves the group operation.
-/

open CategoryTheory AlgebraicGeometry

namespace GroupActions

noncomputable section

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroups.ReductiveGroupData K)

private theorem oppositeBorelSmooth : Algebra.Smooth K G.oppositeBorelAlgebra :=
  G.oppositeBorel_smooth

attribute [local instance] oppositeBorelSmooth

private theorem oppositeBorelReduced : IsReduced G.oppositeBorelAlgebra :=
  TauCeti.isReduced_of_smooth K G.oppositeBorelAlgebra

attribute [local instance] oppositeBorelReduced

/-- The affine variety represented by the coordinate algebra of the opposite Borel subgroup. -/
def oppositeBorelVariety : Variety K := affineVariety K G.oppositeBorelAlgebra

/-- The variety of the opposite Borel subgroup is connected. -/
instance oppositeBorelVarietyConnected : ConnectedSpace (oppositeBorelVariety G).scheme :=
  TauCeti.geometricallyConnectedCommHopfAlgProperty.connectedSpace K
    (CommHopfAlgCat.of K G.oppositeBorelAlgebra) G.oppositeBorel_geometricallyConnected

/-- The variety of the opposite Borel subgroup is integral. -/
instance oppositeBorelVarietyIntegral : IsIntegral (oppositeBorelVariety G).scheme := by
  have : IsRegularRing G.oppositeBorelAlgebra := TauCeti.IsRegularRing.of_smooth (R := K)
  have : ∀ x : (oppositeBorelVariety G).scheme,
      IsRegularLocalRing ((oppositeBorelVariety G).scheme.presheaf.stalk x) := by
    change ∀ x : Spec (CommRingCat.of G.oppositeBorelAlgebra),
      IsRegularLocalRing ((Spec (CommRingCat.of G.oppositeBorelAlgebra)).presheaf.stalk x)
    intro x
    infer_instance
  exact TauCeti.AlgebraicGeometry.isIntegral_of_connected_of_isRegularLocalRing_stalk _

/-- The coordinate Hopf algebra gives the opposite Borel variety its group-object structure. -/
instance oppositeBorelVarietyGroup : GrpObj (oppositeBorelVariety G).toOver := by
  change GrpObj ((Spec (CommRingCat.of G.oppositeBorelAlgebra)).asOver (Spec (CommRingCat.of K)))
  infer_instance

/-- The opposite Borel subgroup includes into the reductive group by restriction of functions. -/
def oppositeBorelInclusion : (oppositeBorelVariety G).toOver ⟶ (reductiveVariety G).toOver :=
  ((hopfSpec (CommRingCat.of K)).map
    (TauCeti.CommHopfAlgCat.mkQuotient
      (CommHopfAlgCat.of K G.coordinateAlgebra) G.oppositeBorelIdeal).op).hom.hom

/-- The underlying opposite Borel inclusion is the spectrum map of the coordinate quotient. -/
theorem oppositeBorelInclusion_left :
    (oppositeBorelInclusion G).left =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk G.oppositeBorelIdeal.toIdeal)) := rfl

/-- The inclusion of the opposite Borel subgroup is a closed immersion. -/
instance oppositeBorelInclusion_isClosed : IsClosedImmersion (oppositeBorelInclusion G).left := by
  rw [oppositeBorelInclusion_left]
  exact IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

/-- The opposite Borel inclusion preserves multiplication. -/
instance oppositeBorelInclusion_isMonHom : IsMonHom (oppositeBorelInclusion G) := by
  change IsMonHom (((hopfSpec (CommRingCat.of K)).map
    (TauCeti.CommHopfAlgCat.mkQuotient
      (CommHopfAlgCat.of K G.coordinateAlgebra) G.oppositeBorelIdeal).op).hom.hom)
  infer_instance

end

end GroupActions
