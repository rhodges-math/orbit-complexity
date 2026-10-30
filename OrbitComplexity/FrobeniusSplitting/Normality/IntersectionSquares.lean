import Batteries.Tactic.Lint
import OrbitComplexity.FrobeniusSplitting.Normality.CoordinateComparisons
import OrbitComplexity.FrobeniusSplitting.Normality.AffinePushouts

/-!
# Pushout squares of affine intersection coordinates
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace FrobeniusSplitting

universe u

private theorem isPullback_eq_inf {X : Scheme.{u}} {U V W Z : X.Opens}
    (hUV : U ≤ V) (hUW : U ≤ W) (hVZ : V ≤ Z) (hWZ : W ≤ Z)
    (h : U = V ⊓ W) :
    CategoryTheory.IsPullback (X.homOfLE hUV) (X.homOfLE hUW)
      (X.homOfLE hVZ) (X.homOfLE hWZ) := by
  subst U
  exact isPullback_opens_inf_le hVZ hWZ

/-- Union of index sets gives pushout refinements of affine-intersection coordinate cospans. -/
theorem intersectionCoordinates_refine {X : Scheme.{u}} {I K : Type u} [CommRing K]
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    (base : X ⟶ Spec (.of K)) (U : I → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (s t r : {a : Finset I // a.Nonempty}ᵒᵖ) (fi : s ⟶ r) (fj : t ⟶ r) :
    ∃ (v : {a : Finset I // a.Nonempty}ᵒᵖ) (gi : v ⟶ s) (gj : v ⟶ t),
      CategoryTheory.IsPushout
        (CommRingCat.ofHom ((intersectionCoordinates base (intersectionOpens U)).map
          fi.unop).hom.toRingHom)
        (CommRingCat.ofHom ((intersectionCoordinates base (intersectionOpens U)).map
          fj.unop).hom.toRingHom)
        (CommRingCat.ofHom ((intersectionCoordinates base (intersectionOpens U)).map
          gi.unop).hom.toRingHom)
        (CommRingCat.ofHom ((intersectionCoordinates base (intersectionOpens U)).map
          gj.unop).hom.toRingHom) := by
  classical
  let D := intersectionOpens U ⋙ X.restrictFunctor ⋙ Over.map base
  have (z : {a : Finset I // a.Nonempty}ᵒᵖ) : IsAffine (D.obj z).left :=
    intersectionOpens_affine U hU z
  let v : {a : Finset I // a.Nonempty}ᵒᵖ :=
    .op ⟨s.unop.val ∪ t.unop.val, s.unop.property.mono Finset.subset_union_left⟩
  let gi : v ⟶ s := (homOfLE (show s.unop ≤ v.unop from Finset.subset_union_left)).op
  let gj : v ⟶ t := (homOfLE (show t.unop ≤ v.unop from Finset.subset_union_right)).op
  refine ⟨v, gi, gj, ?_⟩
  have hraw : CategoryTheory.IsPullback (D.map gi).left (D.map gj).left
      (D.map fi).left (D.map fj).left := by
    change CategoryTheory.IsPullback
      (X.homOfLE (leOfHom ((intersectionOpens U).map gi)))
      (X.homOfLE (leOfHom ((intersectionOpens U).map gj)))
      (X.homOfLE (leOfHom ((intersectionOpens U).map fi)))
      (X.homOfLE (leOfHom ((intersectionOpens U).map fj)))
    exact isPullback_eq_inf _ _ _ _ Finset.iInf_union
  have hcoords := coordinateSquare_pullback (.of K) D gi gj fi fj hraw
  exact (isPushout_iff_spec_pullback _ _ _ _).mpr hcoords

end FrobeniusSplitting
