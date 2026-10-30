import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.CharacterFrameRatios
import OrbitComplexity.FrobeniusSplitting.Normality.Assembly.FrameReflection
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Powers of coframe units from character evaluation

Two coframe families identified with the canonical character evaluations
have the powers of their degree-one ratio. The identifications are whole
module maps; no coordinate presentation of their source modules is used.
-/

set_option autoImplicit false

noncomputable section
universe u v w

open AlgebraicGeometry CategoryTheory
open ReductiveGroups GroupActions FrobeniusSplitting

namespace SchubertGeometry.CharacterLine

open private scaledFrame unit_ratio_from_scalar from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendPowerFrames

private theorem coframe_scalar_transfer {C : Type v} [Category.{w} C]
    {L M T : C} (D : L ≅ M) (E F : M ⟶ T) (e f : L ⟶ T) (s : T ⟶ T)
    (hE : D.hom ≫ E = e) (hF : D.hom ≫ F = f) (h : f = e ≫ s) :
    F = E ≫ s := by
  apply (cancel_epi D.hom).mp
  calc
    _ = f := hF
    _ = e ≫ s := h
    _ = (D.hom ≫ E) ≫ s := congrArg (fun t => t ≫ s) hE.symm
    _ = _ := Category.assoc _ _ _

private theorem evaluation_scalar_transfer {C : Type v} [Category.{w} C]
    {L M T : C} (D : L ≅ M) (E F : M ⟶ T) (e f : L ⟶ T) (s : T ⟶ T)
    (hE : D.hom ≫ E = e) (hF : D.hom ≫ F = f) (h : F = E ≫ s) :
    f = e ≫ s := by
  calc
    _ = D.hom ≫ F := hF.symm
    _ = D.hom ≫ (E ≫ s) := congrArg (fun t => D.hom ≫ t) h
    _ = (D.hom ≫ E) ≫ s := (Category.assoc _ _ _).symm
    _ = _ := congrArg (fun t => t ≫ s) hE

/-- Coframe families with canonical character evaluations have the powers
of their single degree-one comparison unit. -/
theorem characterCoframe_unit_power
    {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K) (A : CommAlgCat.{u} K) (g : G.points)
    (a : (algSpec (.of K)).obj (.op A) ⟶ (oppositeUnipotentVariety G).toOver)
    (k : (algSpec (.of K)).obj (.op A) ⟶ (reductiveVariety G).toOver)
    (h : a ≫ flagChartMorphism G g = k ≫ flagQuotientMorphism G)
    (m : Spec (.of A) ⟶ (flagVariety G).scheme)
    (hk : k.left ≫ flagQuotient G = m)
    (l : (algSpec (.of K)).obj (.op A) ⟶ (reductiveVariety G).toOver)
    (hl : l = a ≫ flagChartMap G g)
    (ha : l.left ≫ flagQuotient G = m)
    (M : ℕ → (Spec (.of A)).Modules)
    (D : ∀ n, (Scheme.Modules.pullback m).obj
      (flagCharacterModule G (G.positiveRootCharacter ^ n)) ≅ M n)
    (E F : ∀ n, M n ≅ SheafOfModules.unit (Spec (.of A)).ringCatSheaf)
    (hE : ∀ n, (D n).hom ≫ (E n).hom =
      characterFrameEvaluation G (G.positiveRootCharacter ^ n)
        ((algSpec (.of K)).obj (.op A)) m l ha)
    (hF : ∀ n, (D n).hom ≫ (F n).hom =
      characterFrameEvaluation G (G.positiveRootCharacter ^ n)
        ((algSpec (.of K)).obj (.op A)) m k hk)
    (n : ℕ) :
    affineCoframeUnit A (E n) (F n) = (affineCoframeUnit A (E 1) (F 1)) ^ n := by
  let c : Aˣ := affineCoframeUnit A (E 1) (F 1)
  have h₁ := evaluation_scalar_transfer (D 1) (E 1).hom (F 1).hom
    (characterFrameEvaluation G (G.positiveRootCharacter ^ 1)
      ((algSpec (.of K)).obj (.op A)) m l ha)
    (characterFrameEvaluation G (G.positiveRootCharacter ^ 1)
      ((algSpec (.of K)).obj (.op A)) m k hk)
    (Scheme.Modules.globalSectionsSmul
      (SheafOfModules.unit (Spec (.of A)).ringCatSheaf)
      ((Scheme.ΓSpecIso (.of A)).inv (c : A)))
    (hE 1) (hF 1)
    (FrobeniusSplitting.RetainedCharacter.affineCoframeUnit_hom A (E 1) (F 1))
  have hp := characterFrame_power_of_one G A g a k h m hk l hl ha c h₁ n
  have hp' : characterFrameEvaluation G (G.positiveRootCharacter ^ n)
      ((algSpec (.of K)).obj (.op A)) m k hk =
    characterFrameEvaluation G (G.positiveRootCharacter ^ n)
      ((algSpec (.of K)).obj (.op A)) m l ha ≫
        Scheme.Modules.globalSectionsSmul
          (SheafOfModules.unit (Spec (.of A)).ringCatSheaf)
          ((Scheme.ΓSpecIso (.of A)).inv ((c : A) ^ n)) := hp
  have hc := coframe_scalar_transfer (D n) (E n).hom (F n).hom
    (characterFrameEvaluation G (G.positiveRootCharacter ^ n)
      ((algSpec (.of K)).obj (.op A)) m l ha)
    (characterFrameEvaluation G (G.positiveRootCharacter ^ n)
      ((algSpec (.of K)).obj (.op A)) m k hk)
    (Scheme.Modules.globalSectionsSmul
      (SheafOfModules.unit (Spec (.of A)).ringCatSheaf)
      ((Scheme.ΓSpecIso (.of A)).inv ((c : A) ^ n)))
    (hE n) (hF n) hp'
  exact unit_ratio_from_scalar A (E n) (F n) (c ^ n) hc

end SchubertGeometry.CharacterLine
