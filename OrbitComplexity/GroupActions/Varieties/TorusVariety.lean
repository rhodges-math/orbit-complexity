import OrbitComplexity.GroupActions.Varieties.ReductiveIntegral
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupSubgroups
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Maximal tori as affine varieties

The coordinate Hopf algebra of the chosen maximal torus defines an integral group variety.
The quotient map of coordinate algebras gives its closed inclusion into the reductive variety.

## Main definitions

* `GroupActions.torusVariety`: the variety of the chosen maximal torus.
* `GroupActions.torusInclusion`: its inclusion as a closed subgroup of the reductive variety.

## Main results

* `GroupActions.torusVarietyIntegral`: the torus variety is integral.
* `GroupActions.torusInclusion_isClosed`: the inclusion is a closed immersion.
* `GroupActions.torusInclusion_isMonHom`: the inclusion preserves the group operation.
-/

open CategoryTheory AlgebraicGeometry

namespace GroupActions

noncomputable section

universe u

variable {K : Type u} [Field K]
  (G : ReductiveGroups.ReductiveGroupData K)

private theorem torusSmooth : Algebra.Smooth K G.torusAlgebra := G.torus_smooth

attribute [local instance] torusSmooth

private theorem torusReduced : IsReduced G.torusAlgebra :=
  TauCeti.isReduced_of_smooth K G.torusAlgebra

attribute [local instance] torusReduced

/-- The affine variety represented by the coordinate algebra of the chosen maximal torus. -/
def torusVariety : Variety K := affineVariety K G.torusAlgebra

/-- The variety of the chosen maximal torus is connected. -/
instance torusVarietyConnected : ConnectedSpace (torusVariety G).scheme :=
  TauCeti.geometricallyConnectedCommHopfAlgProperty.connectedSpace K
    (CommHopfAlgCat.of K G.torusAlgebra) G.torus_geometricallyConnected

/-- The variety of the chosen maximal torus is integral. -/
instance torusVarietyIntegral : IsIntegral (torusVariety G).scheme := by
  have : IsRegularRing G.torusAlgebra := TauCeti.IsRegularRing.of_smooth (R := K)
  have : ∀ x : (torusVariety G).scheme,
      IsRegularLocalRing ((torusVariety G).scheme.presheaf.stalk x) := by
    change ∀ x : Spec (CommRingCat.of G.torusAlgebra),
      IsRegularLocalRing ((Spec (CommRingCat.of G.torusAlgebra)).presheaf.stalk x)
    intro x
    infer_instance
  exact TauCeti.AlgebraicGeometry.isIntegral_of_connected_of_isRegularLocalRing_stalk _

/-- The coordinate Hopf algebra gives the torus variety its group-object structure. -/
instance torusVarietyGroup : GrpObj (torusVariety G).toOver := by
  change GrpObj ((Spec (CommRingCat.of G.torusAlgebra)).asOver (Spec (CommRingCat.of K)))
  infer_instance

/-- Multiplication on the chosen maximal torus variety is commutative. -/
instance torusVarietyCommGroup : CommGrpObj (torusVariety G).toOver := by
  have : Coalgebra.IsCocomm K G.torusAlgebra :=
    TauCeti.torusCommHopfAlgProperty.isCocomm K G.torusAlgebra G.torus_isTorus
  change CommGrpObj ((Spec (CommRingCat.of G.torusAlgebra)).asOver (Spec (CommRingCat.of K)))
  infer_instance
/-- The chosen maximal torus includes into the reductive group by restriction of functions. -/
def torusInclusion : (torusVariety G).toOver ⟶ (reductiveVariety G).toOver :=
  ((hopfSpec (CommRingCat.of K)).map
    (TauCeti.CommHopfAlgCat.mkQuotient
      (CommHopfAlgCat.of K G.coordinateAlgebra) G.torusIdeal).op).hom.hom

/-- The underlying Torus inclusion is the spectrum map of the coordinate quotient. -/
theorem torusInclusion_left :
    (torusInclusion G).left =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk G.torusIdeal.toIdeal)) := rfl

/-- The inclusion of the chosen maximal torus is a closed immersion. -/
instance torusInclusion_isClosed : IsClosedImmersion (torusInclusion G).left := by
  rw [torusInclusion_left]
  exact IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

set_option backward.isDefEq.respectTransparency.types false in
/-- The chosen torus inclusion preserves multiplication. -/
instance torusInclusion_isMonHom : IsMonHom (torusInclusion G) := by
  change IsMonHom (((hopfSpec (CommRingCat.of K)).map
    (TauCeti.CommHopfAlgCat.mkQuotient
      (CommHopfAlgCat.of K G.coordinateAlgebra) G.torusIdeal).op).hom.hom)
  infer_instance

end

end GroupActions
