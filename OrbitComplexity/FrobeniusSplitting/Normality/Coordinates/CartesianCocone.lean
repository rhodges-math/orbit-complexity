import OrbitComplexity.FrobeniusSplitting.Normality.ColimitCovers
import OrbitComplexity.FrobeniusSplitting.Normality.RelativeBaseChange

/-! # Specified cocones with cartesian component squares -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
noncomputable section
universe u v w
namespace FrobeniusSplitting

/-- A specified scheme cocone is colimiting when its component squares are the pullbacks. -/
def cartesianCoconeIsColimit {J : Type v} [Category.{w} J] [Quiver.IsThin J]
    [Small.{u} J] (F G : J ⥤ Scheme.{u})
    [∀ {i j} (f : i ⟶ j), IsOpenImmersion (G.map f)]
    [(G ⋙ Scheme.forget).IsLocallyDirected]
    (α : F ⟶ G) (hα : α.Equifibered)
    (cF : Cocone F) (cG : Cocone G) (hcG : IsColimit cG)
    (f : cF.pt ⟶ cG.pt)
    (hcart : ∀ j, IsPullback (α.app j) (cF.ι.app j) (cG.ι.app j) f) :
    IsColimit cF := by
  let := colimitCoverCategory G
  let := colimitCoverDirected G
  let U := Scheme.IsLocallyDirected.openCover G
  let : Small.{u} U.I₀ := inferInstanceAs (Small.{u} J)
  let : Quiver.IsThin U.I₀ := inferInstanceAs (Quiver.IsThin J)
  let d : Scheme.Cover.RelativeGluingData U :=
    { functor := F, natTrans := α, equifibered := hα }
  let {i j} (g : i ⟶ j) : IsOpenImmersion (F.map g) :=
    MorphismProperty.of_isPullback (hα g).flip inferInstance
  let : (F ⋙ Scheme.forget).IsLocallyDirected :=
    Scheme.isLocallyDirected_of_equifibered_of_injective α hα
      (fun g ↦ (F.map g).injective)
  let eG := (colimit.isColimit G).coconePointUniqueUpToIso hcG
  let b := colimit.desc F cF
  have hG (j : J) : colimit.ι G j ≫ eG.hom = cG.ι.app j :=
    (colimit.isColimit G).comp_coconePointUniqueUpToIso_hom hcG j
  have hb : IsPullback d.toBase b eG.hom f := by
    apply isPullback_relativeGluing U d eG.hom b f
    intro j
    change J at j
    change IsPullback (α.app j) (colimit.ι F j ≫ b) (colimit.ι G j ≫ eG.hom) f
    rw [colimit.ι_desc, hG]
    exact hcart j
  have hdesc : (colimit.isColimit F).desc cF = b := by
    apply (colimit.isColimit F).hom_ext
    intro j
    exact ((colimit.isColimit F).fac cF j).trans (colimit.ι_desc cF j).symm
  let : IsIso ((colimit.isColimit F).desc cF) := by
    rw [hdesc]
    exact hb.isIso_snd_of_isIso
  exact (colimit.isColimit F).ofPointIso

end FrobeniusSplitting
