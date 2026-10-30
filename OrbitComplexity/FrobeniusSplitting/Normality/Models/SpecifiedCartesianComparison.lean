import OrbitComplexity.FrobeniusSplitting.Normality.ColimitCovers
import OrbitComplexity.FrobeniusSplitting.Normality.RelativeBaseChange

/-! # Cartesian comparisons of specified colimits -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
noncomputable section
universe u v w
namespace FrobeniusSplitting

/-- Component base squares give a Cartesian comparison of the specified scheme colimits. -/
theorem exists_specified_comparison {J : Type v} [Category.{w} J] [Quiver.IsThin J]
    [Small.{u} J] (F G : J ⥤ Scheme.{u})
    [∀ {i j} (f : i ⟶ j), IsOpenImmersion (G.map f)]
    [(G ⋙ Scheme.forget).IsLocallyDirected]
    (α : F ⟶ G) (cF : Cocone F) (cG : Cocone G)
    (hF : IsColimit cF) (hG : IsColimit cG)
    {Y Z : Scheme.{u}} (a : cF.pt ⟶ Y) (b : cG.pt ⟶ Z) (c : Y ⟶ Z)
    (hcart : ∀ j, IsPullback (α.app j) (cF.ι.app j ≫ a) (cG.ι.app j ≫ b) c) :
    ∃ f : cF.pt ⟶ cG.pt, IsPullback f a b c ∧
      ∀ j, cF.ι.app j ≫ f = α.app j ≫ cG.ι.app j := by
  have hα : α.Equifibered := by
    intro i j f
    have hs : IsPullback (α.app i) (F.map f ≫ (cF.ι.app j ≫ a))
        (G.map f ≫ (cG.ι.app j ≫ b)) c := by
      simpa only [← Category.assoc, cF.w f, cG.w f] using hcart i
    exact (hs.of_bot (α.naturality f).symm (hcart j)).flip
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
  let eF := (colimit.isColimit F).coconePointUniqueUpToIso hF
  let eG := (colimit.isColimit G).coconePointUniqueUpToIso hG
  have heF (j : J) : colimit.ι F j ≫ eF.hom = cF.ι.app j :=
    (colimit.isColimit F).comp_coconePointUniqueUpToIso_hom hF j
  have heG (j : J) : colimit.ι G j ≫ eG.hom = cG.ι.app j :=
    (colimit.isColimit G).comp_coconePointUniqueUpToIso_hom hG j
  let k : Cocone F := { pt := cG.pt, ι := α ≫ cG.ι }
  let f := hF.desc k
  have hf (j : J) : cF.ι.app j ≫ f = α.app j ≫ cG.ι.app j := hF.fac k j
  have hb : IsPullback d.toBase (eF.hom ≫ a) (eG.hom ≫ b) c := by
    apply isPullback_relativeGluing U d (eG.hom ≫ b) (eF.hom ≫ a) c
    intro j
    change J at j
    change IsPullback (α.app j) (colimit.ι F j ≫ (eF.hom ≫ a))
      (colimit.ι G j ≫ (eG.hom ≫ b)) c
    simpa only [← Category.assoc, heF, heG] using hcart j
  have hd : d.toBase ≫ eG.hom = eF.hom ≫ f := by
    apply (colimit.isColimit F).hom_ext
    intro j
    calc
      _ = (colimit.ι F j ≫ d.toBase) ≫ eG.hom := (Category.assoc _ _ _).symm
      _ = (α.app j ≫ colimit.ι G j) ≫ eG.hom :=
        congrArg (fun z ↦ z ≫ eG.hom) (d.ι_toBase j)
      _ = α.app j ≫ cG.ι.app j := by rw [Category.assoc, heG]
      _ = cF.ι.app j ≫ f := (hf j).symm
      _ = _ := (congrArg (fun z ↦ z ≫ f) (heF j)).symm.trans (Category.assoc _ _ _)
  refine ⟨f, ?_, hf⟩
  exact hb.of_iso eF eG (Iso.refl _) (Iso.refl _) hd
    (Category.comp_id _)
    (Category.comp_id _)
    ((Category.comp_id c).trans (Category.id_comp c).symm)

end FrobeniusSplitting
