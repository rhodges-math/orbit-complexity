import Batteries.Tactic.Lint
import OrbitComplexity.FrobeniusSplitting.Normality.IntersectionMorphisms
import OrbitComplexity.FrobeniusSplitting.Normality.CoordinateDiagrams

/-!
# Scheme maps and intersection coordinates
-/

open CategoryTheory AlgebraicGeometry Opposite

namespace FrobeniusSplitting

universe u

/-- Restrictions of a morphism to labeled affine intersections form a natural transformation. -/
noncomputable def intersectionSchemeMap {X Y : Scheme.{u}} {I J K : Type u} [CommRing K]
    (f : X ⟶ Y) (g : Y ⟶ Spec (.of K)) (U : J → X.Opens) (V : I → Y.Opens)
    (label : J → I) (hle : ∀ j, U j ≤ f ⁻¹ᵁ V (label j)) :
    (intersectionOpens U ⋙ X.restrictFunctor ⋙ Over.map (f ≫ g)) ⟶
      (intersectionIndexMap label).op ⋙
        (intersectionOpens V ⋙ Y.restrictFunctor ⋙ Over.map g) where
  app s := Over.homMk
    (f.resLE ((intersectionOpens V).obj ((intersectionIndexMap label).op.obj s))
      ((intersectionOpens U).obj s) (intersection_preimage_le f U V label hle s)) (by
        change f.resLE _ _ _ ≫
          (((intersectionOpens V).obj ((intersectionIndexMap label).op.obj s)).ι ≫ g) =
            ((intersectionOpens U).obj s).ι ≫ (f ≫ g)
        rw [← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc])
  naturality s t a := by
    ext1
    change X.homOfLE (leOfHom ((intersectionOpens U).map a)) ≫ f.resLE _ _ _ =
      f.resLE _ _ _ ≫ Y.homOfLE (leOfHom ((intersectionOpens V).map
        ((intersectionIndexMap label).op.map a)))
    rw [← cancel_mono (((intersectionOpens V).obj
      ((intersectionIndexMap label).op.obj t)).ι)]
    simp only [Category.assoc, Scheme.homOfLE_ι, Scheme.Hom.resLE_comp_ι]
    rw [← Category.assoc, Scheme.homOfLE_ι]

/-- Pullbacks on intersection coordinate rings are natural with respect to restriction. -/
noncomputable def intersectionCoordinateMap {X Y : Scheme.{u}} {I J K : Type u}
    [CommRing K] (f : X ⟶ Y) (g : Y ⟶ Spec (.of K))
    (U : J → X.Opens) (V : I → Y.Opens) (label : J → I)
    (hle : ∀ j, U j ≤ f ⁻¹ᵁ V (label j)) :
    intersectionIndexMap label ⋙ intersectionCoordinates g (intersectionOpens V) ⟶
      intersectionCoordinates (f ≫ g) (intersectionOpens U) :=
  NatTrans.unop
    (Functor.whiskerRight (intersectionSchemeMap f g U V label hle) (algΓ (.of K)))

end FrobeniusSplitting
