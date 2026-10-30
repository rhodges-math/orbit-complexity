import Batteries.Tactic.Lint
import OrbitComplexity.FrobeniusSplitting.Normality.ColimitCovers
import OrbitComplexity.FrobeniusSplitting.Normality.RelativeBaseChange
import Mathlib.CategoryTheory.Limits.Over

/-!
# Cartesian comparisons of glued scheme diagrams
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FrobeniusSplitting

universe u v w

/-- Compatible cartesian comparisons of open diagrams give a cartesian square of glued schemes. -/
theorem exists_glued_comparisons {J : Type v} [Category.{w} J] [Quiver.IsThin J]
    [Small.{u} J] {Y Z : Scheme.{u}}
    (F : J ⥤ Over Y) (G : J ⥤ Over Z) (c : Y ⟶ Z)
    [∀ {i j} (f : i ⟶ j), IsOpenImmersion ((G.map f).left)]
    [((G ⋙ Over.forget Z) ⋙ Scheme.forget).IsLocallyDirected]
    (α : F ⋙ Over.forget Y ⟶ G ⋙ Over.forget Z) (hα : α.Equifibered)
    (hcart : ∀ i, IsPullback (α.app i) (F.obj i).hom (G.obj i).hom c) :
    ∃ (cF : Cocone F) (cG : Cocone G) (q : cF.pt.left ⟶ cG.pt.left),
      Nonempty (IsColimit cF) ∧ Nonempty (IsColimit cG) ∧
      IsPullback q cF.pt.hom cG.pt.hom c ∧
      ∀ i, (cF.ι.app i).left ≫ q = α.app i ≫ (cG.ι.app i).left := by
  let F₀ := F ⋙ Over.forget Y
  let G₀ := G ⋙ Over.forget Z
  have {i j} (f : i ⟶ j) : IsOpenImmersion (G₀.map f) := by
    change IsOpenImmersion (G.map f).left
    infer_instance
  let := colimitCoverCategory G₀
  let := colimitCoverDirected G₀
  let 𝒰 := Scheme.IsLocallyDirected.openCover G₀
  let : Small.{u} 𝒰.I₀ := inferInstanceAs (Small.{u} J)
  let : Quiver.IsThin 𝒰.I₀ := inferInstanceAs (Quiver.IsThin J)
  let d : Scheme.Cover.RelativeGluingData 𝒰 :=
    { functor := F₀
      natTrans := α
      equifibered := hα }
  have {i j} (f : i ⟶ j) : IsOpenImmersion (F₀.map f) := by
    apply MorphismProperty.of_isPullback (hα f).flip
    infer_instance
  have : (F₀ ⋙ Scheme.forget).IsLocallyDirected :=
    Scheme.isLocallyDirected_of_equifibered_of_injective α hα
      (fun f ↦ (F₀.map f).injective)
  let bF : Cocone F₀ :=
    { pt := Y
      ι :=
        { app := fun i ↦ (F.obj i).hom
          naturality := by
            intro i j f
            change (F.map f).left ≫ (F.obj j).hom = (F.obj i).hom ≫ 𝟙 Y
            rw [Category.comp_id]
            exact Over.w (F.map f) } }
  let bG : Cocone G₀ :=
    { pt := Z
      ι :=
        { app := fun i ↦ (G.obj i).hom
          naturality := by
            intro i j f
            change (G.map f).left ≫ (G.obj j).hom = (G.obj i).hom ≫ 𝟙 Z
            rw [Category.comp_id]
            exact Over.w (G.map f) } }
  let cF : Cocone F :=
    { pt := Over.mk (colimit.desc F₀ bF)
      ι :=
        { app := fun i ↦ Over.homMk (colimit.ι F₀ i) (colimit.ι_desc bF i)
          naturality := by
            intro i j f
            ext1
            exact colimit.w F₀ f } }
  let cG : Cocone G :=
    { pt := Over.mk (colimit.desc G₀ bG)
      ι :=
        { app := fun i ↦ Over.homMk (colimit.ι G₀ i) (colimit.ι_desc bG i)
          naturality := by
            intro i j f
            ext1
            exact colimit.w G₀ f } }
  refine ⟨cF, cG, d.toBase, ⟨?_⟩, ⟨?_⟩, ?_, ?_⟩
  · exact isColimitOfReflects (Over.forget Y) (colimit.isColimit F₀)
  · exact isColimitOfReflects (Over.forget Z) (colimit.isColimit G₀)
  · apply isPullback_relativeGluing 𝒰 d (colimit.desc G₀ bG)
      (colimit.desc F₀ bF) c
    intro i
    change J at i
    change IsPullback (α.app i) (colimit.ι F₀ i ≫ colimit.desc F₀ bF)
      (colimit.ι G₀ i ≫ colimit.desc G₀ bG) c
    rw [colimit.ι_desc, colimit.ι_desc]
    exact hcart i
  · intro i
    change J at i
    change colimit.ι F₀ i ≫ d.toBase = α.app i ≫ colimit.ι G₀ i
    exact d.ι_toBase i

end FrobeniusSplitting
