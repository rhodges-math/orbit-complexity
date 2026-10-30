import Batteries.Tactic.Lint
import OrbitComplexity.FrobeniusSplitting.Normality.EquifiberedColimits
import Mathlib.AlgebraicGeometry.Morphisms.Basic

/-!
# ColimitProperties

Mixed affine diagrams and geometric properties of their colimit morphisms.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FrobeniusSplitting

universe u v w

/-- A property local on the target descends from the components of an equifibered
diagram to any compatible morphism of specified colimits. -/
theorem property_of_colimit_components {J : Type v} [Category.{w} J] [Quiver.IsThin J]
    [Small.{u} J] (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtTarget P]
    (F G : J ⥤ Scheme.{u})
    [∀ {i j} (f : i ⟶ j), IsOpenImmersion (G.map f)]
    [(G ⋙ Scheme.forget).IsLocallyDirected]
    (α : F ⟶ G) (hα : α.Equifibered)
    (cF : Cocone F) (cG : Cocone G) (hcF : IsColimit cF) (hcG : IsColimit cG)
    (q : cF.pt ⟶ cG.pt) (hcomp : ∀ i, cF.ι.app i ≫ q = α.app i ≫ cG.ι.app i)
    (hP : ∀ i, P (α.app i)) : P q := by
  let eG := (colimit.isColimit G).coconePointUniqueUpToIso hcG
  let 𝒰 := (Scheme.IsLocallyDirected.openCover G).pushforwardIso eG.hom
  have hG (i : J) : colimit.ι G i ≫ eG.hom = cG.ι.app i :=
    (colimit.isColimit G).comp_coconePointUniqueUpToIso_hom hcG i
  have hcart (i : 𝒰.I₀) :
      IsPullback (α.app i) (cF.ι.app i) (𝒰.f i) q := by
    change J at i
    change IsPullback (α.app i) (cF.ι.app i) (colimit.ι G i ≫ eG.hom) q
    rw [hG]
    exact isPullback_colimit_component F G α hα cF cG hcF hcG q hcomp i
  apply IsZariskiLocalAtTarget.of_openCover (P := P) 𝒰
  intro i
  let e := (hcart i).flip.isoPullback
  have heq : e.hom ≫ 𝒰.pullbackHom q i = α.app i :=
    (hcart i).flip.isoPullback_hom_snd
  apply (P.cancel_left_of_respectsIso e.hom _).mp
  rw [heq]
  exact hP i

end FrobeniusSplitting
