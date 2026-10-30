import OrbitComplexity.GroupActions.Varieties.AffinePointTopology
import OrbitComplexity.GroupActions.Actions.Points
import OrbitComplexity.ReductiveGroups.Groups.Cells.PointFlagSpace
import Mathlib.AlgebraicGeometry.Group.Affine

/-! # Rational points of affine group varieties

The spectrum of a reduced finite-type commutative Hopf algebra is a group variety. The
group law on its rational points is the convolution law on coordinate algebra maps.

## Main definitions

* `GroupActions.affineVarietyGroup`: the canonical group object of an affine Hopf algebra.
* `GroupActions.affineGroupPointsMulEquiv`: coordinate points with convolution multiplication.
-/

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace GroupActions

noncomputable section

attribute [local instance] ReductiveGroups.pointZariskiTopology

universe u

variable (K : Type u) [Field K]

private def affineBaseIso : Over.mk (𝟙 (Spec (CommRingCat.of K))) ≅
    (Spec (CommRingCat.of K)).asOver (Spec (CommRingCat.of K)) :=
  Over.isoMk (Iso.refl (Spec (CommRingCat.of K))) (by
    change 𝟙 _ ≫ Spec.map (CommRingCat.ofHom (algebraMap K K)) = 𝟙 _
    simp only [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp])

variable (A : Type u) [CommRing A] [HopfAlgebra K A] [IsReduced A] [Algebra.FiniteType K A]

/-- The Hopf algebra gives its affine variety the canonical group-object structure. -/
instance affineVarietyGroup : GrpObj (affineVariety K A).toOver := by
  change GrpObj ((Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of K)))
  infer_instance

private theorem affinePointsOverHom (g : WithConv (A →ₐ[K] K)) :
    (affineVariety K A).pointsEquivOverHom (affinePointsEquiv g.ofConv) =
      (affineBaseIso K).hom ≫ Spec.mapMulEquiv g := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom g.ofConv.toRingHom) =
    𝟙 _ ≫ Spec.map (CommRingCat.ofHom g.ofConv.toRingHom)
  exact (Category.id_comp _).symm

set_option backward.isDefEq.respectTransparency.types false in
/-- Convolution points are the group of rational points of the affine group variety. -/
def affineGroupPointsMulEquiv : WithConv (A →ₐ[K] K) ≃* (affineVariety K A).points where
  toEquiv := (WithConv.equiv _).trans affinePointsEquiv
  map_mul' g h := by
    apply (affineVariety K A).pointsEquivOverHom.injective
    rw [Variety.pointsEquivOverHom_mul]
    calc
      _ = (affineBaseIso K).hom ≫ Spec.mapMulEquiv (g * h) := affinePointsOverHom K A _
      _ = (affineBaseIso K).hom ≫ (Spec.mapMulEquiv g * Spec.mapMulEquiv h) :=
        congrArg (fun f => (affineBaseIso K).hom ≫ f) (map_mul Spec.mapMulEquiv g h)
      _ = ((affineBaseIso K).hom ≫ Spec.mapMulEquiv g) *
          ((affineBaseIso K).hom ≫ Spec.mapMulEquiv h) := MonObj.comp_mul _ _ _
      _ = _ := congrArg₂ (fun a b => a * b)
        (affinePointsOverHom K A g).symm (affinePointsOverHom K A h).symm

/-- The coordinate-point comparison sends a convolution point to its spectrum map. -/
theorem affineGroupPointsMulEquiv_apply (g : WithConv (A →ₐ[K] K)) :
    (affineGroupPointsMulEquiv K A g).val =
      Spec.map (CommRingCat.ofHom g.ofConv.toRingHom) := rfl

end

end GroupActions
