import OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.Invertible
import OrbitComplexity.FrobeniusSplitting.Modules.RelativeCoefficients
import OrbitComplexity.FrobeniusSplitting.Modules.RelativeMaps
import OrbitComplexity.SchubertGeometry.Frobenius.Determinant.Function
import Batteries.Tactic.Lint
import Batteries.Tactic.OpenPrivate

set_option autoImplicit false

/-! # The original determinant-power section of the character module -/

open AlgebraicGeometry CategoryTheory ReductiveGroups GroupActions
open CartesianMonoidalCategory MonoidalCategory
open FrobeniusSplitting.CharacterLine
open scoped CategoryTheory.MonObj

noncomputable section
universe u

namespace SchubertGeometry.CharacterLine

open private rightMul rightMul_quotient pairFst characterPullback weightedPullback
  functionsPullback from OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.Module

private theorem map_comp_precompose {D E : Type*} [Category D] [Category E]
    (F : D ⥤ E) {U V W : D} {P : E} (s : U ⟶ V) (i : V ⟶ W) (t : U ⟶ W)
    (h : s ≫ i = t) (a : P ⟶ F.obj U) :
    (a ≫ F.map s) ≫ F.map i = a ≫ F.map t :=
  (Category.assoc _ _ _).trans
    ((congrArg (fun f => a ≫ f) (F.map_comp s i).symm).trans
      (congrArg (fun f => a ≫ F.map f) h))

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

private abbrev H := (reductiveVariety G).toOver
private abbrev B := (borelVariety G).toOver
private abbrev F := (flagVariety G).scheme
private abbrev pair := H G ⊗ B G
private abbrev productObj := Over.mk (flagQuotient G)
private abbrev pairObj := Over.mk ((fst (H G) (B G)).left ≫ flagQuotient G)

private def rightMap : pairObj G ⟶ productObj G :=
  Over.homMk (rightMul G).left (rightMul_quotient G)

private def firstMap : pairObj G ⟶ productObj G :=
  Over.homMk (fst (H G) (B G)).left rfl

private def weight (N : ℕ) : Γ((pair G).left, ⊤) :=
  (snd (H G) (B G)).left.appTop
    (borelCharacterSection G (G.positiveRootCharacter ^ N))

/-- The regular coefficient power gives its module section on the flag quotient. -/
def determinantCoefficientSection (N : ℕ) :
    SheafOfModules.unit (F G).ringCatSheaf ⟶ relativeFunctionsObj (F G) (productObj G) :=
  relativeCoefficient (F G) (productObj G) (DeterminantSection.positiveDetPowerFunction G N)

private theorem coefficient_condition (N : ℕ) :
    flagCharacterCondition G (G.positiveRootCharacter ^ N)
      (determinantCoefficientSection G N) := by
  have h := relativeCoefficient_character (F G) (rightMap G) (firstMap G)
    (DeterminantSection.positiveDetPowerFunction G N) (weight G N)
    (DeterminantSection.positiveDetPowerFunction_right G N)
  have ha : relativeFunctionsMap (F G) (rightMap G) = characterPullback G := rfl
  have hb : relativeFunctionsMap (F G) (firstMap G) ≫
      relativeFunctionsSmul (F G) (pairObj G) (weight G N) =
        weightedPullback G (G.positiveRootCharacter ^ N) := by
    have hfirst : relativeFunctionsMap (F G) (firstMap G) =
        functionsPullback (pairFst G).left (flagQuotient G) :=
      relativeFunctionsMap_unit (pairFst G).left (flagQuotient G)
    exact congrArg
      (fun f : relativeFunctionsObj (F G) (productObj G) ⟶
          relativeFunctionsObj (F G) (pairObj G) =>
        f ≫ relativeFunctionsSmul (F G) (pairObj G) (weight G N)) hfirst
  change determinantCoefficientSection G N ≫ characterPullback G =
    determinantCoefficientSection G N ≫ weightedPullback G (G.positiveRootCharacter ^ N)
  exact (congrArg (fun f => determinantCoefficientSection G N ≫ f) ha.symm).trans
    (h.trans (congrArg (fun f => determinantCoefficientSection G N ≫ f) hb))

/-- The same determinant power is a section of the original full-character invertible module. -/
def flagDeterminantModuleSection (N : ℕ) :
    SheafOfModules.unit (F G).ringCatSheaf ⟶
      flagCharacterModule G (G.positiveRootCharacter ^ N) :=
  flagCharacterLift G (G.positiveRootCharacter ^ N)
    (determinantCoefficientSection G N) (coefficient_condition G N)

/-- The image of the section is the determinant coefficient section. -/
theorem flagDeterminantModuleSection_inclusion (N : ℕ) :
    flagDeterminantModuleSection G N ≫ flagCharacterInclusion G (G.positiveRootCharacter ^ N) =
      determinantCoefficientSection G N :=
  flagCharacterLift_inclusion G (G.positiveRootCharacter ^ N)
    (determinantCoefficientSection G N) (coefficient_condition G N)

/-- The original BSDH endpoint pulls this same full-character section back to its word line. -/
def wordDeterminantModuleSection (N : ℕ) (word : List G.rootBase.support) :
    SheafOfModules.unit (bsdhScheme G word).ringCatSheaf ⟶
      wordCharacterModule G (G.positiveRootCharacter ^ N) word :=
  (Scheme.Modules.pullbackObjUnitIso (bsdhMap G word)).inv ≫
    (Scheme.Modules.pullback (bsdhMap G word)).map (flagDeterminantModuleSection G N)

/-- The word module section still pulls back the same original regular coefficient map. -/
theorem wordDeterminantModuleSection_inclusion (N : ℕ) (word : List G.rootBase.support) :
    wordDeterminantModuleSection G N word ≫
        (Scheme.Modules.pullback (bsdhMap G word)).map
          (flagCharacterInclusion G (G.positiveRootCharacter ^ N)) =
      (Scheme.Modules.pullbackObjUnitIso (bsdhMap G word)).inv ≫
        (Scheme.Modules.pullback (bsdhMap G word)).map (determinantCoefficientSection G N) := by
  exact map_comp_precompose (Scheme.Modules.pullback (bsdhMap G word))
    (flagDeterminantModuleSection G N)
    (flagCharacterInclusion G (G.positiveRootCharacter ^ N))
    (determinantCoefficientSection G N) (flagDeterminantModuleSection_inclusion G N)
    (Scheme.Modules.pullbackObjUnitIso (bsdhMap G word)).inv

end SchubertGeometry.CharacterLine
