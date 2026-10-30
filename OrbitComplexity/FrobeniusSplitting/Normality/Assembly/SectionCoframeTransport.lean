import OrbitComplexity.FrobeniusSplitting.Normality.Assembly.AdjustedCoframes
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Section coordinates under a coframe comparison

A comparison of the same section through a scheme map gives its entire
coordinate transformation. The multiplier is the ratio of the two specified
coframes of the same pulled-back line.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.Modules

open private unitValue unitValue_smul from
  OrbitComplexity.FrobeniusSplitting.Normality.Assembly.FrameReflection
open private spec_scalar_image from
  OrbitComplexity.FrobeniusSplitting.Normality.Assembly.AdjustedCoframes

namespace FrobeniusSplitting.RetainedCharacter

private abbrev unitModule (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

private theorem pulled_section_coordinate {X Y : Scheme.{u}} (f : X ⟶ Y)
    {L : Y.Modules} (s : unitModule Y ⟶ L) (E : L ≅ unitModule Y)
    (a : Γ(Y, ⊤)) (hs : s ≫ E.hom = globalSectionsSmul (unitModule Y) a) :
    ((pullbackObjUnitIso f).inv ≫ (Scheme.Modules.pullback f).map s) ≫
      ((Scheme.Modules.pullback f).mapIso E ≪≫ pullbackObjUnitIso f).hom =
        globalSectionsSmul (unitModule X) (f.appTop a) := by
  change ((pullbackObjUnitIso f).inv ≫ (Scheme.Modules.pullback f).map s) ≫
    ((Scheme.Modules.pullback f).map E.hom ≫ (pullbackObjUnitIso f).hom) = _
  calc
    _ = (pullbackObjUnitIso f).inv ≫
        ((Scheme.Modules.pullback f).map (s ≫ E.hom) ≫
          (pullbackObjUnitIso f).hom) := by
      rw [Functor.map_comp]
      simp only [Category.assoc]
    _ = (pullbackObjUnitIso f).inv ≫
        (globalSectionsSmul ((Scheme.Modules.pullback f).obj (unitModule Y))
          (f.appTop a) ≫ (pullbackObjUnitIso f).hom) := by
      rw [hs]
      exact congrArg
        (fun k => (pullbackObjUnitIso f).inv ≫ k ≫ (pullbackObjUnitIso f).hom)
        (pullback_map_globalSectionsSmul f (unitModule Y) a)
    _ = (pullbackObjUnitIso f).inv ≫
        ((pullbackObjUnitIso f).hom ≫
          globalSectionsSmul (unitModule X) (f.appTop a)) := by
      exact congrArg (fun k => (pullbackObjUnitIso f).inv ≫ k)
        (globalSectionsSmul_naturality (pullbackObjUnitIso f).hom (f.appTop a))
    _ = _ := by rw [Iso.inv_hom_id_assoc]

private theorem scalar_hom_injective {X : Scheme.{u}} {a b : Γ(X, ⊤)}
    (h : globalSectionsSmul (unitModule X) a = globalSectionsSmul (unitModule X) b) :
    a = b := by
  have hv := congrArg (fun k : unitModule X ⟶ unitModule X => unitValue k) h
  simpa only [unitValue_smul] using hv

/-- Whole section and coframe comparisons determine the entire coordinate change. -/
theorem coframe_section_transport {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) {L : (Spec (.of A)).Modules} {M : (Spec (.of B)).Modules}
    (s : unitModule (Spec (.of A)) ⟶ L) (t : unitModule (Spec (.of B)) ⟶ M)
    (H : M ≅ (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom φ))).obj L)
    (E : L ≅ unitModule (Spec (.of A))) (F : M ≅ unitModule (Spec (.of B)))
    (a : A) (b : B)
    (hs : s ≫ E.hom = globalSectionsSmul (unitModule (Spec (.of A)))
      ((Scheme.ΓSpecIso (.of A)).inv a))
    (ht : t ≫ F.hom = globalSectionsSmul (unitModule (Spec (.of B)))
      ((Scheme.ΓSpecIso (.of B)).inv b))
    (hsection : t ≫ H.hom = (pullbackObjUnitIso (Spec.map (CommRingCat.ofHom φ))).inv ≫
      (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom φ))).map s) :
    b = (affineCoframeUnit B
      (H ≪≫ (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom φ))).mapIso E ≪≫
        pullbackObjUnitIso (Spec.map (CommRingCat.ofHom φ))) F : B) * φ a := by
  let E₀ : M ≅ unitModule (Spec (.of B)) :=
    H ≪≫ (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom φ))).mapIso E ≪≫
      pullbackObjUnitIso (Spec.map (CommRingCat.ofHom φ))
  have hsource : t ≫ E₀.hom = globalSectionsSmul (unitModule (Spec (.of B)))
      ((Scheme.ΓSpecIso (.of B)).inv (φ a)) := by
    calc
      t ≫ E₀.hom = (t ≫ H.hom) ≫
          ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom φ))).mapIso E ≪≫
            pullbackObjUnitIso (Spec.map (CommRingCat.ofHom φ))).hom :=
        (Category.assoc _ _ _).symm
      _ = _ := by
        rw [hsection]
        have h := pulled_section_coordinate (Spec.map (CommRingCat.ofHom φ)) s E
          ((Scheme.ΓSpecIso (.of A)).inv a) hs
        rw [spec_scalar_image] at h
        exact h
  have heq : globalSectionsSmul (unitModule (Spec (.of B)))
      ((Scheme.ΓSpecIso (.of B)).inv b) =
      globalSectionsSmul (unitModule (Spec (.of B)))
        ((Scheme.ΓSpecIso (.of B)).inv ((affineCoframeUnit B E₀ F : B) * φ a)) := by
    calc
      _ = t ≫ F.hom := ht.symm
      _ = t ≫ (E₀.hom ≫ globalSectionsSmul (unitModule (Spec (.of B)))
          ((Scheme.ΓSpecIso (.of B)).inv (affineCoframeUnit B E₀ F : B))) :=
        congrArg (fun k => t ≫ k) (affineCoframeUnit_hom B E₀ F)
      _ = globalSectionsSmul (unitModule (Spec (.of B)))
          ((Scheme.ΓSpecIso (.of B)).inv (φ a)) ≫
          globalSectionsSmul (unitModule (Spec (.of B)))
            ((Scheme.ΓSpecIso (.of B)).inv (affineCoframeUnit B E₀ F : B)) := by
        rw [← Category.assoc, hsource]
      _ = _ := by
        rw [← globalSectionsSmul_mul]
        congr 1
        exact (Scheme.ΓSpecIso (.of B)).inv.hom.map_mul _ _ |>.symm
  exact (Scheme.ΓSpecIso (.of B)).symm.commRingCatIsoToRingEquiv.injective
    (scalar_hom_injective heq)

end FrobeniusSplitting.RetainedCharacter
