import OrbitComplexity.GroupActions.Varieties.AffineMorphisms
import OrbitComplexity.GroupActions.Varieties.AffineGroup

/-! # Isomorphisms of affine group varieties

An isomorphism of coordinate Hopf algebras induces an isomorphism of group varieties. Its
rational-point map is composition with the coordinate isomorphism.

## Main definitions

* `GroupActions.affineGroupIso`: the group-variety isomorphism induced by a Hopf isomorphism.

## Main results

* `GroupActions.affineGroupIso_isMonHom`: the induced map preserves multiplication.
* `GroupActions.affineGroupIso_points`: the coordinate formula on rational points.
-/

open CategoryTheory AlgebraicGeometry

namespace GroupActions

noncomputable section

universe u

variable {K A B : Type u} [Field K] [CommRing A] [CommRing B]
  [HopfAlgebra K A] [HopfAlgebra K B] [IsReduced A] [IsReduced B]
  [Algebra.FiniteType K A] [Algebra.FiniteType K B]

/-- A Hopf-algebra isomorphism induces a group-variety isomorphism in the reverse direction. -/
def affineGroupIso (e : A ≃ₐc[K] B) :
    (affineVariety K B).toOver ≅ (affineVariety K A).toOver :=
  (Grp.forget _).mapIso ((hopfSpec (CommRingCat.of K)).mapIso (CommHopfAlgCat.isoMk e).op)

/-- The variety isomorphism induced by a Hopf isomorphism preserves multiplication. -/
instance affineGroupIso_isMonHom (e : A ≃ₐc[K] B) : IsMonHom (affineGroupIso e).hom := by
  change IsMonHom (((hopfSpec (CommRingCat.of K)).map
    (CommHopfAlgCat.ofHom e.toBialgHom).op).hom.hom)
  infer_instance

/-- On rational points, the induced group-variety isomorphism composes coordinate maps. -/
theorem affineGroupIso_points (e : A ≃ₐc[K] B) (p : B →ₐ[K] K) :
    Variety.mapPoints (affineGroupIso e).hom ((affineVarietyPointsEquiv K B).symm p) =
      (affineVarietyPointsEquiv K A).symm (p.comp e.toAlgEquiv.toAlgHom) :=
  affineMorphism_points e.toAlgEquiv.toAlgHom p

end

end GroupActions
