import Batteries.Tactic.Lint
import Mathlib.AlgebraicGeometry.Cover.Directed
import Mathlib.AlgebraicGeometry.Cover.Open
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.CategoryTheory.Limits.Over

/-!
# Finiteness properties of glued affine schemes
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FrobeniusSplitting

universe u w

/-- A finite affine open diagram glues to a quasi-compact scheme locally of finite presentation. -/
theorem finite_affine_colimit_properties {J : Type u} [Category.{w} J]
    [Finite J] [Small.{u} J] [Quiver.IsThin J] {S : Scheme.{u}}
    (F : J ⥤ Over S)
    [∀ {i j} (f : i ⟶ j), IsOpenImmersion (F.map f).left]
    [((F ⋙ Over.forget S) ⋙ Scheme.forget).IsLocallyDirected]
    [hAffine : ∀ i, IsAffine (F.obj i).left]
    [hfp : ∀ i, LocallyOfFinitePresentation (F.obj i).hom]
    (c : Cocone F) (hc : IsColimit c) :
    CompactSpace c.pt.left ∧ LocallyOfFinitePresentation c.pt.hom := by
  let F₀ := F ⋙ Over.forget S
  have {i j} (f : i ⟶ j) : IsOpenImmersion (F₀.map f) := by
    change IsOpenImmersion (F.map f).left
    infer_instance
  let c₀ := (Over.forget S).mapCocone c
  let hc₀ : IsColimit c₀ := isColimitOfPreserves (Over.forget S) hc
  let e := (colimit.isColimit F₀).coconePointUniqueUpToIso hc₀
  let 𝒰 := (Scheme.IsLocallyDirected.openCover F₀).pushforwardIso e.hom
  have : Finite 𝒰.I₀ := inferInstanceAs (Finite J)
  have hcompact : ∀ i : 𝒰.I₀, CompactSpace (𝒰.X i) := by
    intro i
    change CompactSpace (F.obj i).left
    exact @Scheme.compactSpace_of_isAffine (F.obj i).left (hAffine i)
  refine ⟨Scheme.OpenCover.compactSpace (H := hcompact) 𝒰, ?_⟩
  let : IsZariskiLocalAtSource (@LocallyOfFinitePresentation.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := @RingHom.FinitePresentation)
  apply IsZariskiLocalAtSource.of_openCover
    (P := @LocallyOfFinitePresentation.{u}) (f := c.pt.hom) 𝒰
  intro i
  change J at i
  change LocallyOfFinitePresentation ((colimit.ι F₀ i ≫ e.hom) ≫ c.pt.hom)
  erw [colimit.comp_coconePointUniqueUpToIso_hom]
  change LocallyOfFinitePresentation ((c.ι.app i).left ≫ c.pt.hom)
  exact (Over.w (c.ι.app i)).symm ▸ hfp i

end FrobeniusSplitting
