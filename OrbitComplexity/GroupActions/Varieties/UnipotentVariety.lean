import OrbitComplexity.GroupActions.Varieties.ReductiveIntegral
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupUnipotent
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Unipotent subgroups as affine varieties

The coordinate Hopf algebra of the chosen unipotent subgroup defines an integral group variety.
The quotient map of coordinate algebras gives its closed inclusion into the reductive variety.

## Main definitions

* `GroupActions.unipotentVariety`: the variety of the chosen unipotent subgroup.
* `GroupActions.unipotentInclusion`: its inclusion as a closed subgroup of the reductive variety.

## Main results

* `GroupActions.unipotentVarietyIntegral`: the Unipotent variety is integral.
* `GroupActions.unipotentInclusion_isClosed`: the inclusion is a closed immersion.
* `GroupActions.unipotentInclusion_isMonHom`: the inclusion preserves the group operation.
-/

open CategoryTheory AlgebraicGeometry

namespace GroupActions

noncomputable section

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroups.ReductiveGroupData K)

private theorem unipotentSmooth : Algebra.Smooth K G.unipotentAlgebra := G.unipotent_smooth

attribute [local instance] unipotentSmooth

private theorem unipotentReduced : IsReduced G.unipotentAlgebra :=
  TauCeti.isReduced_of_smooth K G.unipotentAlgebra

attribute [local instance] unipotentReduced

/-- The affine variety represented by the coordinate algebra of the chosen unipotent subgroup. -/
def unipotentVariety : Variety K := affineVariety K G.unipotentAlgebra

/-- The variety of the chosen unipotent subgroup is connected. -/
instance unipotentVarietyConnected : ConnectedSpace (unipotentVariety G).scheme :=
  TauCeti.geometricallyConnectedCommHopfAlgProperty.connectedSpace K
    (CommHopfAlgCat.of K G.unipotentAlgebra) G.unipotent_geometricallyConnected

/-- The variety of the chosen unipotent subgroup is integral. -/
instance unipotentVarietyIntegral : IsIntegral (unipotentVariety G).scheme := by
  have : IsRegularRing G.unipotentAlgebra := TauCeti.IsRegularRing.of_smooth (R := K)
  have : ∀ x : (unipotentVariety G).scheme,
      IsRegularLocalRing ((unipotentVariety G).scheme.presheaf.stalk x) := by
    change ∀ x : Spec (CommRingCat.of G.unipotentAlgebra),
      IsRegularLocalRing ((Spec (CommRingCat.of G.unipotentAlgebra)).presheaf.stalk x)
    intro x
    infer_instance
  exact TauCeti.AlgebraicGeometry.isIntegral_of_connected_of_isRegularLocalRing_stalk _

/-- The coordinate Hopf algebra gives the Unipotent variety its group-object structure. -/
instance unipotentVarietyGroup : GrpObj (unipotentVariety G).toOver := by
  change GrpObj ((Spec (CommRingCat.of G.unipotentAlgebra)).asOver (Spec (CommRingCat.of K)))
  infer_instance

/-- The chosen unipotent subgroup includes into the reductive group by restriction of functions. -/
def unipotentInclusion : (unipotentVariety G).toOver ⟶ (reductiveVariety G).toOver :=
  ((hopfSpec (CommRingCat.of K)).map
    (TauCeti.CommHopfAlgCat.mkQuotient
      (CommHopfAlgCat.of K G.coordinateAlgebra) G.unipotentIdeal).op).hom.hom

/-- The underlying Unipotent inclusion is the spectrum map of the coordinate quotient. -/
theorem unipotentInclusion_left :
    (unipotentInclusion G).left =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk G.unipotentIdeal.toIdeal)) := rfl

/-- The inclusion of the chosen unipotent subgroup is a closed immersion. -/
instance unipotentInclusion_isClosed : IsClosedImmersion (unipotentInclusion G).left := by
  rw [unipotentInclusion_left]
  exact IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

set_option backward.isDefEq.respectTransparency.types false in
/-- The chosen unipotent inclusion preserves multiplication. -/
instance unipotentInclusion_isMonHom : IsMonHom (unipotentInclusion G) := by
  change IsMonHom (((hopfSpec (CommRingCat.of K)).map
    (TauCeti.CommHopfAlgCat.mkQuotient
      (CommHopfAlgCat.of K G.coordinateAlgebra) G.unipotentIdeal).op).hom.hom)
  infer_instance

end

end GroupActions
