import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendPowerFrames
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Character frame ratios from their first power

The ratio for the positive-root character determines the ratios for all its
powers. The comparison uses the same two group lifts and the same scalar unit.
-/

set_option autoImplicit false

noncomputable section
universe u

open AlgebraicGeometry CategoryTheory Opposite
open ReductiveGroups GroupActions FrobeniusSplitting

namespace SchubertGeometry.CharacterLine

open private scaledFrame factor_power_at unit_ratio_from_power_one from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendPowerFrames

private theorem frame_unit_of_ratio {A : Type u} [CommRing A]
    {L : (Spec (.of A)).Modules}
    (E F : L ≅ SheafOfModules.unit (Spec (.of A)).ringCatSheaf) (c : Aˣ)
    (h : F.hom = scaledFrame E.hom
      (Scheme.Modules.globalSectionsSmul
        (SheafOfModules.unit (Spec (.of A)).ringCatSheaf)
        ((Scheme.ΓSpecIso (.of A)).inv (c : A)))) :
    affineCoframeUnit A E F = c := by
  apply unit_ratio_from_power_one A E F c
  simpa only [scaledFrame, pow_one] using h

private theorem frame_units_unique {A : Type u} [CommRing A]
    {L : (Spec (.of A)).Modules}
    (e f : L ⟶ SheafOfModules.unit (Spec (.of A)).ringCatSheaf)
    (he : IsIso e) (hf : IsIso f) (c v : Aˣ)
    (hc : f = scaledFrame e (Scheme.Modules.globalSectionsSmul
      (SheafOfModules.unit (Spec (.of A)).ringCatSheaf)
      ((Scheme.ΓSpecIso (.of A)).inv (c : A))))
    (hv : f = scaledFrame e (Scheme.Modules.globalSectionsSmul
      (SheafOfModules.unit (Spec (.of A)).ringCatSheaf)
      ((Scheme.ΓSpecIso (.of A)).inv ((v : A) ^ 1)))) : c = v := by
  let E : L ≅ SheafOfModules.unit (Spec (.of A)).ringCatSheaf :=
    @asIso _ _ _ _ e he
  let F : L ≅ SheafOfModules.unit (Spec (.of A)).ringCatSheaf :=
    @asIso _ _ _ _ f hf
  have hc' : affineCoframeUnit A E F = c := frame_unit_of_ratio E F c hc
  have hv' : affineCoframeUnit A E F = v := by
    apply frame_unit_of_ratio E F v
    change f = scaledFrame e (Scheme.Modules.globalSectionsSmul
      (SheafOfModules.unit (Spec (.of A)).ringCatSheaf)
      ((Scheme.ΓSpecIso (.of A)).inv (v : A)))
    simpa only [pow_one] using hv
  exact hc'.symm.trans hv'

/-- The ratio of two lifts at character power one determines their ratio at
every power of the positive-root character, using the same scalar unit. -/
theorem characterFrame_power_of_one
    {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K) (A : CommAlgCat.{u} K) (g : G.points)
    (a : (algSpec (.of K)).obj (op A) ⟶ (oppositeUnipotentVariety G).toOver)
    (k : (algSpec (.of K)).obj (op A) ⟶ (reductiveVariety G).toOver)
    (h : a ≫ flagChartMorphism G g = k ≫ flagQuotientMorphism G)
    (m : Spec (.of A) ⟶ (flagVariety G).scheme)
    (hk : k.left ≫ SchubertGeometry.flagQuotient G = m)
    (l : (algSpec (.of K)).obj (op A) ⟶ (reductiveVariety G).toOver)
    (hl : l = a ≫ flagChartMap G g)
    (ha : l.left ≫ SchubertGeometry.flagQuotient G = m) (c : Aˣ)
    (h1 : characterFrameEvaluation G (G.positiveRootCharacter ^ 1)
        ((algSpec (.of K)).obj (op A)) m k hk =
      scaledFrame (characterFrameEvaluation G (G.positiveRootCharacter ^ 1)
        ((algSpec (.of K)).obj (op A)) m l ha)
      (Scheme.Modules.globalSectionsSmul
        (SheafOfModules.unit (Spec (.of A)).ringCatSheaf)
        ((Scheme.ΓSpecIso (.of A)).inv (c : A)))) (n : ℕ) :
    characterFrameEvaluation G (G.positiveRootCharacter ^ n)
        ((algSpec (.of K)).obj (op A)) m k hk =
      scaledFrame (characterFrameEvaluation G (G.positiveRootCharacter ^ n)
        ((algSpec (.of K)).obj (op A)) m l ha)
      (Scheme.Modules.globalSectionsSmul
        (SheafOfModules.unit (Spec (.of A)).ringCatSheaf)
        ((Scheme.ΓSpecIso (.of A)).inv ((c : A) ^ n))) := by
  let v : Aˣ := ProjectiveLine.positiveBorelSection G A (frameBorelFactor G A g a k h)
  have hcv : c = v := frame_units_unique
    (characterFrameEvaluation G (G.positiveRootCharacter ^ 1)
      ((algSpec (.of K)).obj (op A)) m l ha)
    (characterFrameEvaluation G (G.positiveRootCharacter ^ 1)
      ((algSpec (.of K)).obj (op A)) m k hk)
    (characterFrameEvaluation_isIso G (G.positiveRootCharacter ^ 1)
      ((algSpec (.of K)).obj (op A)) m l ha)
    (characterFrameEvaluation_isIso G (G.positiveRootCharacter ^ 1)
      ((algSpec (.of K)).obj (op A)) m k hk)
    c v h1 (factor_power_at (G := G) A g a k h m hk l hl ha v rfl 1)
  exact factor_power_at (G := G) A g a k h m hk l hl ha c hcv n

end SchubertGeometry.CharacterLine
