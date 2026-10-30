import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.OpenFrameRestriction
import Batteries.Tactic.Lint

/-!
# Generator agreement on chart intersections

Agreement of pulled coframes on a fibre product implies agreement of
their generator sections on the intersection of the two open images.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Opposite
open AlgebraicGeometry.Scheme.Modules
open CategoryTheory.Limits

namespace SchubertGeometry.ProjectiveCartier

open private compositeFrame from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.OpenFrameRestriction

private abbrev unitModule (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

private theorem section_eq_at_inf {X : TopCat.{u}} (M : X.Presheaf Ab)
    {U V W : TopologicalSpace.Opens X} (hW : W = U ⊓ V)
    (hWU : W ≤ U) (hWV : W ≤ V) (s : M.obj (op U)) (t : M.obj (op V))
    (h : M.map (homOfLE hWU).op s = M.map (homOfLE hWV).op t) :
    M.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op s =
      M.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op t := by
  subst W
  exact h

/-- Coframe agreement on a fibre product gives generator agreement on the
intersection of the two open chart images. -/
theorem openFrameSection_overlap {A B X : Scheme.{u}}
    (f : A ⟶ X) (g : B ⟶ X) [IsOpenImmersion f] [IsOpenImmersion g]
    (L : X.Modules)
    (E : (Scheme.Modules.pullback f).obj L ≅ unitModule A)
    (F : (Scheme.Modules.pullback g).obj L ≅ unitModule B)
    (heq : compositeFrame (pullback.fst f g) f L E =
      (pullbackCongr (pullback.condition (f := f) (g := g))).app L ≪≫
        compositeFrame (pullback.snd f g) g L F) :
    L.presheaf.map (homOfLE
        (inf_le_left : f.opensRange ⊓ g.opensRange ≤ f.opensRange)).op
        (openFrameSection f L E) =
      L.presheaf.map (homOfLE
        (inf_le_right : f.opensRange ⊓ g.opensRange ≤ g.opensRange)).op
        (openFrameSection g L F) := by
  have hW : (pullback.fst f g ≫ f).opensRange = f.opensRange ⊓ g.opensRange := by
    rw [Scheme.Hom.opensRange_comp, Scheme.Hom.opensRange_pullbackFst,
      Scheme.Hom.image_preimage_eq_opensRange_inf]
  have hleft := openFrameSection_comp (pullback.fst f g) f L E
  have hright := openFrameSection_triangle (pullback.snd f g) g
    (pullback.fst f g ≫ f) (pullback.condition (f := f) (g := g)).symm L F
  have he := congrArg (openFrameSection (pullback.fst f g ≫ f) L) heq
  exact section_eq_at_inf L.presheaf hW _ _ (openFrameSection f L E)
    (openFrameSection g L F) (hleft.symm.trans (he.trans hright))

end SchubertGeometry.ProjectiveCartier
