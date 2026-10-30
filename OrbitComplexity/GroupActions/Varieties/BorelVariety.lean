import OrbitComplexity.GroupActions.Varieties.ReductiveIntegral
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupSubgroups
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Borel subgroups as affine varieties

The coordinate Hopf algebra of the chosen Borel subgroup defines an integral group variety.
The quotient map of coordinate algebras gives its closed inclusion into the reductive variety.

## Main definitions

* `GroupActions.borelVariety`: the variety of the chosen Borel subgroup.
* `GroupActions.borelInclusion`: its inclusion as a closed subgroup of the reductive variety.

## Main results

* `GroupActions.borelVarietyIntegral`: the Borel variety is integral.
* `GroupActions.borelInclusion_isClosed`: the inclusion is a closed immersion.
* `GroupActions.borelInclusion_isMonHom`: the inclusion preserves the group operation.
-/

open CategoryTheory AlgebraicGeometry

namespace GroupActions

noncomputable section

universe u

variable {K : Type u} [Field K] [IsAlgClosed K]
  (G : ReductiveGroups.ReductiveGroupData K)

private theorem borelSmooth : Algebra.Smooth K G.borelAlgebra := G.borel_smooth

attribute [local instance] borelSmooth

private theorem borelReduced : IsReduced G.borelAlgebra :=
  TauCeti.isReduced_of_smooth K G.borelAlgebra

attribute [local instance] borelReduced

/-- The affine variety represented by the coordinate algebra of the chosen Borel subgroup. -/
def borelVariety : Variety K := affineVariety K G.borelAlgebra

/-- The variety of the chosen Borel subgroup is connected. -/
instance borelVarietyConnected : ConnectedSpace (borelVariety G).scheme :=
  TauCeti.geometricallyConnectedCommHopfAlgProperty.connectedSpace K
    (CommHopfAlgCat.of K G.borelAlgebra) G.borel_geometricallyConnected

/-- The variety of the chosen Borel subgroup is integral. -/
instance borelVarietyIntegral : IsIntegral (borelVariety G).scheme := by
  have : IsRegularRing G.borelAlgebra := TauCeti.IsRegularRing.of_smooth (R := K)
  have : ∀ x : (borelVariety G).scheme,
      IsRegularLocalRing ((borelVariety G).scheme.presheaf.stalk x) := by
    change ∀ x : Spec (CommRingCat.of G.borelAlgebra),
      IsRegularLocalRing ((Spec (CommRingCat.of G.borelAlgebra)).presheaf.stalk x)
    intro x
    infer_instance
  exact TauCeti.AlgebraicGeometry.isIntegral_of_connected_of_isRegularLocalRing_stalk _

/-- The coordinate Hopf algebra gives the Borel variety its group-object structure. -/
instance borelVarietyGroup : GrpObj (borelVariety G).toOver := by
  change GrpObj ((Spec (CommRingCat.of G.borelAlgebra)).asOver (Spec (CommRingCat.of K)))
  infer_instance

/-- The chosen Borel subgroup includes into the reductive group by restriction of functions. -/
def borelInclusion : (borelVariety G).toOver ⟶ (reductiveVariety G).toOver :=
  ((hopfSpec (CommRingCat.of K)).map
    (TauCeti.CommHopfAlgCat.mkQuotient
      (CommHopfAlgCat.of K G.coordinateAlgebra) G.borelIdeal).op).hom.hom

/-- The underlying Borel inclusion is the spectrum map of the coordinate quotient. -/
theorem borelInclusion_left :
    (borelInclusion G).left =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk G.borelIdeal.toIdeal)) := rfl

/-- The inclusion of the chosen Borel subgroup is a closed immersion. -/
instance borelInclusion_isClosed : IsClosedImmersion (borelInclusion G).left := by
  rw [borelInclusion_left]
  exact IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

set_option backward.isDefEq.respectTransparency.types false in
/-- The chosen Borel inclusion preserves multiplication. -/
instance borelInclusion_isMonHom : IsMonHom (borelInclusion G) := by
  change IsMonHom (((hopfSpec (CommRingCat.of K)).map
    (TauCeti.CommHopfAlgCat.mkQuotient
      (CommHopfAlgCat.of K G.coordinateAlgebra) G.borelIdeal).op).hom.hom)
  infer_instance

end

end GroupActions
