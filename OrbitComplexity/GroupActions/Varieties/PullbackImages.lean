import OrbitComplexity.GroupActions.Varieties.Morphisms
import Mathlib.AlgebraicGeometry.Morphisms.Preimmersion
import Mathlib.AlgebraicGeometry.LimitsOver

/-! # Rational images of pullback projections

The universal property of a pullback lifts matching rational points. An isomorphic variety
model has the same projection image and inherits preimmersion properties by base change.
-/

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace GroupActions.Variety
universe u
variable {K : Type u} [Field K] {X Y Z P : GroupActions.Variety K}

private theorem points_comp (f : X.toOver ⟶ Y.toOver) (x : X.points) :
    Y.pointsEquivOverHom (mapPoints f x) = X.pointsEquivOverHom x ≫ f := rfl

/-- A pullback projection has rational image equal to the inverse image of the other image. -/
theorem pullback_points_range (f : X.toOver ⟶ Z.toOver) (g : Y.toOver ⟶ Z.toOver)
    (e : P.toOver ≅ pullback f g) :
    Set.range (mapPoints (e.hom ≫ pullback.snd f g)) =
      (mapPoints g) ⁻¹' Set.range (mapPoints f) := by
  ext y
  constructor
  · rintro ⟨p, rfl⟩
    refine ⟨mapPoints (e.hom ≫ pullback.fst f g) p, ?_⟩
    have he : (e.hom ≫ pullback.fst f g) ≫ f =
        (e.hom ≫ pullback.snd f g) ≫ g := by
      simp only [Category.assoc, pullback.condition]
    simpa only [mapPoints_comp] using congrArg (fun h => mapPoints h p) he
  · rintro ⟨x, hxy⟩
    have h : X.pointsEquivOverHom x ≫ f = Y.pointsEquivOverHom y ≫ g := by
      apply Over.OverMorphism.ext
      exact congrArg Subtype.val hxy
    let l := pullback.lift (X.pointsEquivOverHom x) (Y.pointsEquivOverHom y) h
    refine ⟨P.pointsEquivOverHom.symm (l ≫ e.inv), ?_⟩
    apply Y.pointsEquivOverHom.injective
    rw [points_comp, Equiv.apply_symm_apply]
    dsimp only [l]
    simp only [Category.assoc, e.inv_hom_id_assoc, pullback.lift_snd]

end GroupActions.Variety
