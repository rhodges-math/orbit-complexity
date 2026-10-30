import OrbitComplexity.FrobeniusSplitting.Normality.Assembly.FrameReflection
import Batteries.Tactic.Lint

/-!
# Adjustment of affine line coframes

A unit scales a coframe of a line module. A scalar comparison of the unit
with the ratio of two coframes identifies the pulled-back adjusted coframe.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.Modules

namespace FrobeniusSplitting.RetainedCharacter

private abbrev unitModule (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

private def scaleCoframe {X : Scheme.{u}} {L : X.Modules}
    (E : L ≅ unitModule X) (d : Γ(X, ⊤)ˣ) : L ≅ unitModule X :=
  E ≪≫ asIso (globalSectionsSmul (unitModule X) d)

private theorem pullback_scale {X Y : Scheme.{u}} (f : X ⟶ Y)
    {L : Y.Modules} (E : L ≅ unitModule Y) (d : Γ(Y, ⊤)ˣ) :
    ((Scheme.Modules.pullback f).mapIso (scaleCoframe E d) ≪≫
      pullbackObjUnitIso f).hom =
      ((Scheme.Modules.pullback f).mapIso E ≪≫ pullbackObjUnitIso f).hom ≫
        globalSectionsSmul (unitModule X) (f.appTop (d : Γ(Y, ⊤))) := by
  change (Scheme.Modules.pullback f).map
      (E.hom ≫ globalSectionsSmul (unitModule Y) d) ≫
        (pullbackObjUnitIso f).hom =
    ((Scheme.Modules.pullback f).map E.hom ≫ (pullbackObjUnitIso f).hom) ≫
      globalSectionsSmul (unitModule X) (f.appTop (d : Γ(Y, ⊤)))
  rw [Functor.map_comp, pullback_map_globalSectionsSmul, Category.assoc,
    globalSectionsSmul_naturality, ← Category.assoc]
  rfl

private theorem spec_scalar_image {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (a : A) :
    (Spec.map (CommRingCat.ofHom φ)).appTop ((Scheme.ΓSpecIso (.of A)).inv a) =
      (Scheme.ΓSpecIso (.of B)).inv (φ a) := by
  exact (ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ)) a).symm

/-- Scale an affine line coframe by a unit in its coordinate ring. -/
def adjustedCoframe {A : Type u} [CommRing A]
    {L : (Spec (.of A)).Modules} (E : L ≅ unitModule (Spec (.of A)))
    (d : Aˣ) : L ≅ unitModule (Spec (.of A)) :=
  scaleCoframe E (Units.map (Scheme.ΓSpecIso (.of A)).inv.hom.toMonoidHom d)

/-- A scalar comparison with the coframe ratio identifies the adjusted coframe. -/
theorem adjustedCoframe_pullback {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) {L : (Spec (.of A)).Modules}
    (E : L ≅ unitModule (Spec (.of A)))
    (F : (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom φ))).obj L ≅
      unitModule (Spec (.of B))) (d : Aˣ)
    (hd : φ (d : A) = (affineCoframeUnit B
      ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom φ))).mapIso E ≪≫
        pullbackObjUnitIso (Spec.map (CommRingCat.ofHom φ))) F : B)) :
    (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom φ))).mapIso
        (adjustedCoframe E d) ≪≫ pullbackObjUnitIso (Spec.map (CommRingCat.ofHom φ)) =
      F := by
  apply Iso.ext
  have h := pullback_scale (Spec.map (CommRingCat.ofHom φ)) E
    (Units.map (Scheme.ΓSpecIso (.of A)).inv.hom.toMonoidHom d)
  change ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom φ))).mapIso
      (adjustedCoframe E d) ≪≫
        pullbackObjUnitIso (Spec.map (CommRingCat.ofHom φ))).hom = _ at h
  have hscalar : (Spec.map (CommRingCat.ofHom φ)).appTop
      ((Units.map (Scheme.ΓSpecIso (.of A)).inv.hom.toMonoidHom d :
        Γ(Spec (.of A), ⊤)ˣ) : Γ(Spec (.of A), ⊤)) =
      (Scheme.ΓSpecIso (.of B)).inv (φ (d : A)) := spec_scalar_image φ (d : A)
  rw [hscalar, hd] at h
  exact h.trans (affineCoframeUnit_hom B
    ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom φ))).mapIso E ≪≫
      pullbackObjUnitIso (Spec.map (CommRingCat.ofHom φ))) F).symm

end FrobeniusSplitting.RetainedCharacter
