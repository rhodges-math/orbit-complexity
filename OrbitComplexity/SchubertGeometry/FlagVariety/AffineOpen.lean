import OrbitComplexity.GroupActions.Varieties.AffineVariety
import OrbitComplexity.GroupActions.Varieties.Morphisms
import OrbitComplexity.GroupActions.Varieties.DifferentialMaps
import OrbitComplexity.FrobeniusSplitting.Normality.UniversallyInjective
import Mathlib.AlgebraicGeometry.Group.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# Affine open immersions from rational points

Injectivity on rational points gives universal injectivity for separated morphisms of
finite-type affine varieties over an algebraically closed field. Etaleness then gives an
open immersion.

## Main results

* `SchubertGeometry.affineOpenImmersion_of_points`: the rational-point criterion.
-/

open CategoryTheory AlgebraicGeometry

namespace SchubertGeometry

noncomputable section

universe u

variable {K A B : Type u} [Field K]
  [CommRing A] [Algebra K A] [IsReduced A] [Algebra.FiniteType K A]
  [CommRing B] [Algebra K B] [IsReduced B] [Algebra.FiniteType K B]

private def affineOverMap (f : A →ₐ[K] B) :
    (GroupActions.affineVariety K B).toOver ⟶ (GroupActions.affineVariety K A).toOver :=
  (algSpec (CommRingCat.of K)).map (CommAlgCat.ofHom f).op

private theorem affineOverMap_points (f : A →ₐ[K] B) (p : B →ₐ[K] K) :
    GroupActions.Variety.mapPoints (affineOverMap f) (GroupActions.affinePointsEquiv p) =
      GroupActions.affinePointsEquiv (p.comp f) := by
  apply Subtype.ext
  change Spec.map (CommRingCat.ofHom p.toRingHom) ≫
    Spec.map (CommRingCat.ofHom f.toRingHom) = _
  rw [← Spec.map_comp]
  rfl

variable [IsAlgClosed K]

/-- An etale affine morphism injective on rational points is an open immersion. -/
theorem affineOpenImmersion_of_points (f : A →ₐ[K] B) (hf : f.toRingHom.Etale)
    (hp : Function.Injective (fun p : B →ₐ[K] K => p.comp f)) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom f.toRingHom)) := by
  let X := GroupActions.affineVariety K B
  let Y := GroupActions.affineVariety K A
  let φ := affineOverMap f
  have hφ : Function.Injective (GroupActions.Variety.mapPoints φ) := by
    intro x y hxy
    obtain ⟨p, rfl⟩ := GroupActions.affinePointsEquiv.surjective x
    obtain ⟨q, rfl⟩ := GroupActions.affinePointsEquiv.surjective y
    rw [affineOverMap_points, affineOverMap_points] at hxy
    exact congrArg GroupActions.affinePointsEquiv
      (hp (GroupActions.affinePointsEquiv.injective hxy))
  have hclosed : Set.InjOn φ.left (closedPoints X.scheme) := by
    intro x hx y hy hxy
    obtain ⟨p, hp⟩ := X.pointsEquivClosedPoints.surjective ⟨x, hx⟩
    obtain ⟨q, hq⟩ := X.pointsEquivClosedPoints.surjective ⟨y, hy⟩
    have hp' : X.pointMap p = x := congrArg Subtype.val hp
    have hq' : X.pointMap q = y := congrArg Subtype.val hq
    have hpoints : GroupActions.Variety.mapPoints φ p =
        GroupActions.Variety.mapPoints φ q := by
      apply Y.pointMap_injective
      rw [GroupActions.Variety.pointMap_mapPoints, GroupActions.Variety.pointMap_mapPoints,
        hp', hq']
      exact hxy
    exact hp'.symm.trans ((congrArg X.pointMap (hφ hpoints)).trans hq')
  have : LocallyOfFiniteType (φ.left ≫ Y.toSpec) := φ.w.symm ▸ X.locallyOfFiniteType
  have : IsSeparated φ.left := by
    change IsSeparated (Spec.map (CommRingCat.ofHom f.toRingHom))
    infer_instance
  have : UniversallyInjective φ.left :=
    FrobeniusSplitting.universallyInjective_of_closedPoints φ.left Y.toSpec hclosed
  have : Etale φ.left := HasRingHomProperty.Spec_iff.mpr hf
  exact GroupActions.openImmersion_of_etale φ.left

end

end SchubertGeometry
