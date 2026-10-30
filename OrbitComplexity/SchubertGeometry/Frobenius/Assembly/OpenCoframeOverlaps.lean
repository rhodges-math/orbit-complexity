import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.OpenCoframeSections
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.OpenFrameOverlaps
import Batteries.Tactic.Lint

/-!
# Coframe agreement on intersections of open images

The coframes on chart images agree on their intersection whenever the
pulled chart coframes agree on the fibre product.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Opposite
open AlgebraicGeometry.Scheme.Modules
open CategoryTheory.Limits
open FrobeniusSplitting.OperatorSheaf

namespace SchubertGeometry.ProjectiveCartier

open private compositeFrame from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.OpenFrameRestriction

private abbrev unitModule (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

private theorem generator_range {A X : Scheme.{u}} (j : A ⟶ X)
    [IsOpenImmersion j] (L : X.Modules)
    (E : (Scheme.Modules.pullback j).obj L ≅ unitModule A) :
    coframeGenerator L j.opensRange (coframeOverRange j L E) =
      openFrameSection j L E := by
  let U := j.opensRange
  have hOn := openFrameSection_onOpen L U (coframeOverRange j L E)
  have hframe := coframeOnOpen_range j L E
  have htri := openFrameSection_triangle j.isoOpensRange.inv j U.ι
    (Scheme.Hom.isoOpensRange_inv_comp j) L E
  have htri' :
      openFrameSection U.ι L
        ((pullbackCongr (Scheme.Hom.isoOpensRange_inv_comp j).symm).app L ≪≫
          ((pullbackComp j.isoOpensRange.inv j).app L).symm ≪≫
            (Scheme.Modules.pullback j.isoOpensRange.inv).mapIso E ≪≫
              pullbackObjUnitIso j.isoOpensRange.inv) =
      L.presheaf.map (homOfLE U.opensRange_ι.le).op (openFrameSection j L E) := by
    simpa only [compositeFrame] using htri
  have harrow : homOfLE U.opensRange_ι.le = eqToHom U.opensRange_ι :=
    Subsingleton.elim _ _
  rw [harrow] at htri'
  have hs := hOn.symm.trans
    ((congrArg (openFrameSection U.ι L) hframe).trans htri')
  have hinj : Function.Injective (L.presheaf.map (eqToHom U.opensRange_ι).op) :=
    (ConcreteCategory.bijective_of_isIso _).injective
  exact hinj hs

/-- Agreement of pulled chart coframes gives agreement on the intersection
of their open images. -/
theorem openCoframe_overlap_eq {A B X : Scheme.{u}}
    (f : A ⟶ X) (g : B ⟶ X) [IsOpenImmersion f] [IsOpenImmersion g]
    (L : X.Modules)
    (E : (Scheme.Modules.pullback f).obj L ≅ unitModule A)
    (F : (Scheme.Modules.pullback g).obj L ≅ unitModule B)
    (heq : compositeFrame (pullback.fst f g) f L E =
      (pullbackCongr (pullback.condition (f := f) (g := g))).app L ≪≫
        compositeFrame (pullback.snd f g) g L F) :
    restrictModuleIso L (unitModule X)
        (inf_le_left : f.opensRange ⊓ g.opensRange ≤ f.opensRange)
        (coframeOverRange f L E) =
      restrictModuleIso L (unitModule X)
        (inf_le_right : f.opensRange ⊓ g.opensRange ≤ g.opensRange)
        (coframeOverRange g L F) := by
  apply coframe_eq_of_generator L (f.opensRange ⊓ g.opensRange)
  have hleft := coframeGenerator_restrict L
    (inf_le_left : f.opensRange ⊓ g.opensRange ≤ f.opensRange)
    (coframeOverRange f L E)
  have hright := coframeGenerator_restrict L
    (inf_le_right : f.opensRange ⊓ g.opensRange ≤ g.opensRange)
    (coframeOverRange g L F)
  have hgenleft := congrArg
    (fun s => (L.val.map (homOfLE
      (inf_le_left : f.opensRange ⊓ g.opensRange ≤ f.opensRange)).op).hom s)
    (generator_range f L E)
  have hgenright := congrArg
    (fun s => (L.val.map (homOfLE
      (inf_le_right : f.opensRange ⊓ g.opensRange ≤ g.opensRange)).op).hom s)
    (generator_range g L F)
  exact hleft.trans (hgenleft.trans
    ((openFrameSection_overlap f g L E F heq).trans (hgenright.symm.trans hright.symm)))

end SchubertGeometry.ProjectiveCartier
