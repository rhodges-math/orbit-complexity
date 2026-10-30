import OrbitComplexity.FrobeniusSplitting.Normality.Assembly.AdjustedCoframes
import OrbitComplexity.FrobeniusSplitting.Normality.Assembly.FrameScalarTransport
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Adjustment through a commuting chart square

The coframe ratio is measured after the specified comparison of pullback
modules. Scaling the original coframe by the retained unit therefore gives
the prescribed coframe through that same comparison.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.Modules
open FrobeniusSplitting.CharacterLine

open private pullback_scale spec_scalar_image from
  OrbitComplexity.FrobeniusSplitting.Normality.Assembly.AdjustedCoframes

namespace FrobeniusSplitting.RetainedCharacter

private abbrev unitModule (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

private theorem prefixed_adjustment {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) {L : (Spec (.of A)).Modules}
    (E : L ≅ unitModule (Spec (.of A))) {M : (Spec (.of B)).Modules}
    (H : M ≅ (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom φ))).obj L)
    (F : M ≅ unitModule (Spec (.of B))) (d : Aˣ)
    (hd : φ (d : A) = (affineCoframeUnit B
      (H ≪≫ (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom φ))).mapIso E ≪≫
        pullbackObjUnitIso (Spec.map (CommRingCat.ofHom φ))) F : B)) :
    H ≪≫ (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom φ))).mapIso
        (adjustedCoframe E d) ≪≫
          pullbackObjUnitIso (Spec.map (CommRingCat.ofHom φ)) = F := by
  apply Iso.ext
  have hp := pullback_scale (Spec.map (CommRingCat.ofHom φ)) E
    (Units.map (Scheme.ΓSpecIso (.of A)).inv.hom.toMonoidHom d)
  have hscalar : (Spec.map (CommRingCat.ofHom φ)).appTop
      ((Units.map (Scheme.ΓSpecIso (.of A)).inv.hom.toMonoidHom d :
        Γ(Spec (.of A), ⊤)ˣ) : Γ(Spec (.of A), ⊤)) =
      (Scheme.ΓSpecIso (.of B)).inv (φ (d : A)) := spec_scalar_image φ (d : A)
  rw [hscalar] at hp
  have h := congrArg (fun k => H.hom ≫ k) hp
  change (H ≪≫ (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom φ))).mapIso
      (adjustedCoframe E d) ≪≫
        pullbackObjUnitIso (Spec.map (CommRingCat.ofHom φ))).hom = _ at h
  rw [← Category.assoc, hd] at h
  exact h.trans (affineCoframeUnit_hom B
    (H ≪≫ (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom φ))).mapIso E ≪≫
      pullbackObjUnitIso (Spec.map (CommRingCat.ofHom φ))) F).symm

/-- A retained coframe ratio identifies the adjusted frame through its chart square. -/
theorem adjustedCoframe_square {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) {S T : Scheme.{u}} (q : T ⟶ S)
    (a : Spec (.of B) ⟶ T) (b : Spec (.of A) ⟶ S)
    (h : Spec.map (CommRingCat.ofHom φ) ≫ b = a ≫ q) (L : S.Modules)
    (E : (Scheme.Modules.pullback b).obj L ≅ unitModule (Spec (.of A)))
    (F : (Scheme.Modules.pullback a).obj ((Scheme.Modules.pullback q).obj L) ≅
      unitModule (Spec (.of B))) (d : Aˣ)
    (hd : φ (d : A) = (affineCoframeUnit B
      (squareFrameIso q a b (Spec.map (CommRingCat.ofHom φ)) h L E) F : B)) :
    squareFrameIso q a b (Spec.map (CommRingCat.ofHom φ)) h L
      (adjustedCoframe E d) = F := by
  exact prefixed_adjustment φ E
    ((pullbackComp a q).app L ≪≫ (pullbackCongr h.symm).app L ≪≫
      ((pullbackComp (Spec.map (CommRingCat.ofHom φ)) b).app L).symm)
    F d hd

end FrobeniusSplitting.RetainedCharacter
