import Batteries.Tactic.Lint
import OrbitComplexity.FrobeniusSplitting.Normality.ColimitCovers
import Mathlib.AlgebraicGeometry.RelativeGluing

/-!
# EquifiberedColimits

Mixed affine diagrams and geometric properties of their colimit morphisms.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FrobeniusSplitting

universe u v w

/-- Every component of an equifibered open diagram is the pullback of its component
on any specified compatible colimits. -/
theorem isPullback_colimit_component {J : Type v} [Category.{w} J] [Quiver.IsThin J]
    [Small.{u} J] (F G : J ⥤ Scheme.{u})
    [∀ {i j} (f : i ⟶ j), IsOpenImmersion (G.map f)]
    [(G ⋙ Scheme.forget).IsLocallyDirected]
    (α : F ⟶ G) (hα : α.Equifibered)
    (cF : Cocone F) (cG : Cocone G) (hcF : IsColimit cF) (hcG : IsColimit cG)
    (q : cF.pt ⟶ cG.pt) (hcomp : ∀ i, cF.ι.app i ≫ q = α.app i ≫ cG.ι.app i)
    (i : J) : IsPullback (α.app i) (cF.ι.app i) (cG.ι.app i) q := by
  let := colimitCoverCategory G
  let := colimitCoverDirected G
  let 𝒰 := Scheme.IsLocallyDirected.openCover G
  let : Small.{u} 𝒰.I₀ := inferInstanceAs (Small.{u} J)
  let : Quiver.IsThin 𝒰.I₀ := inferInstanceAs (Quiver.IsThin J)
  let d : Scheme.Cover.RelativeGluingData 𝒰 :=
    { functor := F
      natTrans := α
      equifibered := hα }
  have {i j} (f : i ⟶ j) : IsOpenImmersion (F.map f) := by
    apply MorphismProperty.of_isPullback (hα f).flip
    infer_instance
  have : (F ⋙ Scheme.forget).IsLocallyDirected :=
    Scheme.isLocallyDirected_of_equifibered_of_injective α hα
      (fun f ↦ (F.map f).injective)
  let b : colimit F ⟶ colimit G := d.toBase
  let eF := hcF.coconePointUniqueUpToIso (colimit.isColimit F)
  let eG := hcG.coconePointUniqueUpToIso (colimit.isColimit G)
  have hF (j : J) : cF.ι.app j ≫ eF.hom = colimit.ι F j :=
    hcF.comp_coconePointUniqueUpToIso_hom (colimit.isColimit F) j
  have hG (j : J) : cG.ι.app j ≫ eG.hom = colimit.ι G j :=
    hcG.comp_coconePointUniqueUpToIso_hom (colimit.isColimit G) j
  have heq : eF.hom ≫ b = q ≫ eG.hom := by
    apply hcF.hom_ext
    intro j
    calc
      _ = colimit.ι F j ≫ b := by rw [← Category.assoc, hF]
      _ = α.app j ≫ colimit.ι G j := d.ι_toBase j
      _ = α.app j ≫ (cG.ι.app j ≫ eG.hom) := by rw [hG]
      _ = _ := by rw [← Category.assoc, ← hcomp, Category.assoc]
  have hcart : IsPullback (α.app i) (colimit.ι F i) (colimit.ι G i) b :=
    d.isPullback_natTrans_ι_toBase i
  apply hcart.of_iso'
    (Iso.refl _) (Iso.refl _) eF eG
  · simp
  · simpa using (hF i).symm
  · simpa using (hG i).symm
  · exact heq

end FrobeniusSplitting
