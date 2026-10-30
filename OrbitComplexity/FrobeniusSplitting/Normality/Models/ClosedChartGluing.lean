import OrbitComplexity.FrobeniusSplitting.Normality.ColimitCovers
import Mathlib.AlgebraicGeometry.RelativeGluing
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! Closed targets glued from cartesian quotient charts. -/

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FrobeniusSplitting

universe u v w

/-- Cartesian closed chart maps over a locally directed open atlas glue to a
closed immersion between the two scheme colimits. -/
theorem exists_closed_atlas_gluing
    {J : Type v} [Category.{w} J] [Quiver.IsThin J] [Small.{u} J]
    (F G : J ⥤ Scheme.{u}) (a : F ⟶ G) (ha : a.Equifibered)
    [∀ {i j} (f : i ⟶ j), IsOpenImmersion (G.map f)]
    [(G ⋙ Scheme.forget).IsLocallyDirected]
    (cG : Cocone G) (hcG : IsColimit cG)
    (hclosed : ∀ i, IsClosedImmersion (a.app i)) :
    ∃ (c : Cocone F) (f : c.pt ⟶ cG.pt),
      Nonempty (IsColimit c) ∧ IsClosedImmersion f ∧
      ∀ i, c.ι.app i ≫ f = a.app i ≫ cG.ι.app i := by
  have : ∀ {i j} (h : i ⟶ j), IsOpenImmersion (F.map h) := fun h ↦
    MorphismProperty.of_isPullback (ha h).flip inferInstance
  have : (F ⋙ Scheme.forget).IsLocallyDirected :=
    Scheme.isLocallyDirected_of_equifibered_of_injective a ha
      (fun {_ _} h ↦ (F.map h).injective)
  let U := Scheme.IsLocallyDirected.openCover G
  have : Small.{u} U.I₀ := by
    change Small.{u} J
    infer_instance
  let := colimitCoverCategory G
  have : Quiver.IsThin U.I₀ := by
    change Quiver.IsThin J
    infer_instance
  let := colimitCoverDirected G
  let d : U.RelativeGluingData :=
    { functor := F
      natTrans := a
      equifibered := ha }
  have : HasColimit d.functor := by
    change HasColimit F
    infer_instance
  have hd : IsClosedImmersion d.toBase := by
    apply IsZariskiLocalAtTarget.of_openCover (P := @IsClosedImmersion) U
    intro i
    have hcart := (d.isPullback_natTrans_ι_toBase i).flip
    change IsClosedImmersion (pullback.snd d.toBase (U.f i))
    have : IsClosedImmersion (d.natTrans.app i) := by
      change IsClosedImmersion (a.app i)
      exact hclosed i
    exact hcart.isoPullback_inv_snd ▸
      (inferInstance : IsClosedImmersion (hcart.isoPullback.inv ≫ d.natTrans.app i))
  let e := (colimit.isColimit G).coconePointUniqueUpToIso hcG
  let f := d.toBase ≫ e.hom
  let : IsClosedImmersion d.toBase := hd
  have hf : IsClosedImmersion f := by
    change IsClosedImmersion (d.toBase ≫ e.hom)
    infer_instance
  refine ⟨colimit.cocone d.functor, f, ⟨colimit.isColimit d.functor⟩,
    hf, ?_⟩
  intro i
  change colimit.ι d.functor i ≫ (d.toBase ≫ e.hom) =
    d.natTrans.app i ≫ cG.ι.app i
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ e.hom) (d.ι_toBase i)).trans
      ((Category.assoc _ _ _).trans
        (congrArg (d.natTrans.app i ≫ ·)
          ((colimit.isColimit G).comp_coconePointUniqueUpToIso_hom hcG i))))


end FrobeniusSplitting
