import Mathlib.AlgebraicGeometry.Group.Affine
import Mathlib.AlgebraicGeometry.Gluing

/-! # The affine legs of a retained prior cocone -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
noncomputable section
universe u v w
namespace SchubertGeometry

/-- The same retained cocone supplies open affine charts, its restriction
arrows, and their structural maps to the coefficient scheme. -/
theorem retained_prior_charts {R : Type u} [CommRing R]
    {J : Type v} [Category.{w} J] [Quiver.IsThin J] [Small.{u} J]
    (N : J ⥤ CommAlgCat.{u} R)
    [hmapOpen : ∀ {s t} (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (N.map f).hom.toRingHom))]
    [hdirected : ((N.op ⋙ algSpec (.of R) ⋙ Over.forget (Spec (.of R))) ⋙
      Scheme.forget).IsLocallyDirected]
    (cG : Cocone (N.op ⋙ algSpec (.of R))) (hcG : IsColimit cG) :
    (∀ s, IsOpenImmersion (cG.ι.app (.op s)).left) ∧
    (∀ s t (f : s ⟶ t),
      Spec.map (CommRingCat.ofHom (N.map f).hom.toRingHom) ≫
        (cG.ι.app (.op s)).left = (cG.ι.app (.op t)).left) ∧
    ∀ s, (cG.ι.app (.op s)).left ≫ cG.pt.hom =
      Spec.map (CommRingCat.ofHom (algebraMap R (N.obj s))) := by
  let E := N.op ⋙ algSpec (.of R) ⋙ Over.forget (Spec (.of R))
  let eOpen : ∀ {s t : Jᵒᵖ} (f : s ⟶ t), IsOpenImmersion (E.map f) := by
    intro s t f
    change IsOpenImmersion (Spec.map (CommRingCat.ofHom (N.map f.unop).hom.toRingHom))
    exact hmapOpen f.unop
  let eDirected : (E ⋙ Scheme.forget).IsLocallyDirected := hdirected
  let C := (Over.forget (Spec (.of R))).mapCocone cG
  have hC : IsColimit C := isColimitOfPreserves (Over.forget (Spec (.of R))) hcG
  let : HasColimit E := HasColimit.mk ⟨C, hC⟩
  let cover : (colimit E).OpenCover :=
    @Scheme.IsLocallyDirected.openCover Jᵒᵖ inferInstance E eOpen eDirected
      (inferInstance : Quiver.IsThin Jᵒᵖ) (inferInstance : Small.{u} Jᵒᵖ)
  let e : colimit E ≅ cG.pt.left :=
    (colimit.isColimit E).coconePointUniqueUpToIso hC
  refine ⟨?_, ?_, ?_⟩
  · intro s
    have hleg := (colimit.isColimit E).comp_coconePointUniqueUpToIso_hom hC (.op s)
    change colimit.ι E (.op s) ≫ e.hom = (cG.ι.app (.op s)).left at hleg
    have hι : IsOpenImmersion (colimit.ι E (.op s)) := by
      change IsOpenImmersion (cover.f (Opposite.op s : Jᵒᵖ))
      exact cover.map_prop (Opposite.op s : Jᵒᵖ)
    rw [← hleg]
    exact @IsOpenImmersion.comp _ _ _ (colimit.ι E (.op s)) e.hom hι inferInstance
  · intro s t f
    exact congrArg Over.Hom.left (cG.w f.op)
  · intro s
    exact (cG.ι.app (.op s)).w

end SchubertGeometry
