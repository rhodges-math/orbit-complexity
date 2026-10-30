import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendCoframePowers
import TauCeti.AlgebraicGeometry.Modules.Pullback
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Append coframe pullback associativity

The word and flag comparisons combine by pullback associativity. The formula
holds for every character power and both polynomial charts.
-/

set_option autoImplicit false
set_option maxHeartbeats 10000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ReductiveGroups GroupActions
open CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj

noncomputable section
universe u v w

namespace SchubertGeometry.RetainedCharacter

open private polynomialBase
  from OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.AppendCoordinates
open private appendEndpoint appendPolynomialLift appendPolynomialLift_endpoint appendRawCoframe
    appendEvaluation
  from OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.AppendCoframes
open CharacterLine.CoframeTransport

variable {K : Type u} [fieldInst : Field K] [algInst : IsAlgClosed K]
    [charInst : CharZero K]
    (G : ReductiveGroupData K) (word : List G.rootBase.support) (i : G.rootBase.support)
    (V : Over (Spec (.of K))) (g : G.points)
    (a : V ⟶ (oppositeUnipotentVariety G).toOver)
    (c : V ⊗ (schubertVariety G
      (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver ⟶
        Over.mk (bsdhToSpec G (word ++ [i])))
    (hend : c.left ≫ (bsdhAppendIso G word i).hom.left ≫
      pullback.snd (bsdhMap G word) (flagBundleProjection G
        (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val))) =
      (a ⊗ₘ 𝟙 (schubertVariety G
        (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver).left ≫
          flagBundleChart G _ g)
    (B : CommAlgCat.{u} K) (p : (algSpec (.of K)).obj (.op B) ⟶ V)


/-- The append polynomial coframe on the pulled-back flag character line. -/
def appendFlagCoframe (n : ℕ) (j : Fin 2) :
    (Scheme.Modules.pullback (X := Spec (.of (Polynomial B))) (Y := bsdhScheme G (word ++
            [i])) (@CategoryStruct.comp Scheme.{u} Scheme.instCategory.toCategoryStruct
          (Spec (.of (Polynomial B))) (projectiveScheme B (ULift.{u} (Fin 2))) (bsdhScheme G
            (word ++ [i]))
          (projectiveLinePolynomialChart B ⟨j⟩) (projectiveAppendChart G i B p c))).obj
      ((Scheme.Modules.pullback (X := bsdhScheme G (word ++ [i])) (Y := (flagVariety
            G).scheme) (bsdhMap G (word ++ [i]))).obj
        (CharacterLine.flagCharacterModule G (G.positiveRootCharacter ^ n))) ⟶
    SheafOfModules.unit (Spec (.of (Polynomial B))).ringCatSheaf :=
  (@appendPolynomialFrame.{u} K fieldInst algInst charInst G word i V g a c hend B p n ⟨j⟩).hom

/-- The flag coframe agrees with the specified append polynomial frame. -/
theorem appendFlagCoframe_eq (n : ℕ) (j : Fin 2) :
    @appendFlagCoframe.{u} K fieldInst algInst charInst G word i V g a c hend B p n j =
      (@appendPolynomialFrame.{u} K fieldInst algInst charInst G word i V g a c hend B p n
            ⟨j⟩).hom := rfl

private theorem raw_map_eq (chi : G.characters) (j : Fin 2) :
    @appendRawCoframe.{u} K fieldInst algInst charInst G word i V g a c hend B p chi j =
      (Scheme.Modules.pullbackComp (projectiveLinePolynomialChart B ⟨j⟩)
        (appendEndpoint G word i V c B p)).hom.app
          (CharacterLine.flagCharacterModule G chi) ≫
        @appendEvaluation.{u} K fieldInst algInst charInst G word i V g a c hend B p chi j := rfl

private theorem evaluation_map_eq (chi : G.characters) (j : Fin 2)
    (hk : (appendPolynomialLift G i V g a B p j).left ≫ flagQuotient G =
      projectiveLinePolynomialChart B ⟨j⟩ ≫
        (@CategoryStruct.comp Scheme.{u} Scheme.instCategory.toCategoryStruct
          (projectiveScheme B (ULift.{u} (Fin 2))) (bsdhScheme G (word ++ [i])) (flagVariety
            G).scheme
          (projectiveAppendChart G i B p c) (bsdhMap G (word ++ [i])))) :

    @Eq ((Scheme.Modules.pullback (projectiveLinePolynomialChart B ⟨j⟩ ≫
        (@CategoryStruct.comp Scheme.{u} Scheme.instCategory.toCategoryStruct
          (projectiveScheme B (ULift.{u} (Fin 2))) (bsdhScheme G (word ++ [i])) (flagVariety
            G).scheme
          (projectiveAppendChart G i B p c) (bsdhMap G (word ++ [i]))))).obj
          (CharacterLine.flagCharacterModule G chi) ⟶
        SheafOfModules.unit (polynomialBase B).left.ringCatSheaf)
      (@appendEvaluation.{u} K fieldInst algInst charInst G word i V g a c hend B p chi j)
      (CharacterLine.characterFrameEvaluation G chi (polynomialBase B)
        (projectiveLinePolynomialChart B ⟨j⟩ ≫
          (@CategoryStruct.comp Scheme.{u} Scheme.instCategory.toCategoryStruct
          (projectiveScheme B (ULift.{u} (Fin 2))) (bsdhScheme G (word ++ [i])) (flagVariety
            G).scheme
          (projectiveAppendChart G i B p c) (bsdhMap G (word ++ [i]))))
        (appendPolynomialLift G i V g a B p j) hk) := rfl

private theorem word_cast_id {D : Type v} [Category.{w} D]
    (chi : G.characters) (F : (bsdhScheme G word).Modules → D) :
    eqToHom (congrArg F
      (show CharacterLine.wordCharacterModule G chi word =
        (Scheme.Modules.pullback (X := bsdhScheme G word)
          (Y := (flagVariety G).scheme) (bsdhMap G word)).obj
            (CharacterLine.flagCharacterModule G chi) from rfl).symm) =
      𝟙 (F ((Scheme.Modules.pullback (X := bsdhScheme G word)
        (Y := (flagVariety G).scheme) (bsdhMap G word)).obj
          (CharacterLine.flagCharacterModule G chi))) := rfl

set_option maxHeartbeats 40000 in
private theorem canonical_raw (n : ℕ) (j : Fin 2) :

    @Eq ((Scheme.Modules.pullback (X := Spec (.of (Polynomial B))) (Y := bsdhScheme G (word ++
            [i])) (@CategoryStruct.comp Scheme.{u} Scheme.instCategory.toCategoryStruct
          (Spec (.of (Polynomial B))) (projectiveScheme B (ULift.{u} (Fin 2))) (bsdhScheme G
            (word ++ [i]))
          (projectiveLinePolynomialChart B ⟨j⟩) (projectiveAppendChart G i B p c))).obj
          ((Scheme.Modules.pullback (X := bsdhScheme G (word ++ [i])) (Y := (flagVariety
            G).scheme) (bsdhMap G (word ++ [i]))).obj
            (CharacterLine.flagCharacterModule G (G.positiveRootCharacter ^ n))) ⟶
      SheafOfModules.unit (Spec (.of (Polynomial B))).ringCatSheaf)
      (@appendFlagCoframe.{u} K fieldInst algInst charInst G word i V g a c hend B p n j)
      ((Scheme.Modules.pullbackComp (X := Spec (.of (Polynomial B))) (Y := projectiveScheme B
            (ULift.{u} (Fin 2))) (Z := bsdhScheme G (word ++ [i]))
            (projectiveLinePolynomialChart B ⟨j⟩) (projectiveAppendChart G i B p c)).inv.app
          ((Scheme.Modules.pullback (X := bsdhScheme G (word ++ [i])) (Y := (flagVariety
            G).scheme) (bsdhMap G (word ++ [i]))).obj
            (CharacterLine.flagCharacterModule G (G.positiveRootCharacter ^ n))) ≫
        (Scheme.Modules.pullback (X := Spec (.of (Polynomial B))) (Y := projectiveScheme B
            (ULift.{u} (Fin 2))) (projectiveLinePolynomialChart B ⟨j⟩)).map
          ((Scheme.Modules.pullbackComp (X := projectiveScheme B (ULift.{u} (Fin 2))) (Y :=
            bsdhScheme G (word ++ [i])) (Z := (flagVariety G).scheme) (projectiveAppendChart G
            i B p c) (bsdhMap G (word ++ [i]))).hom.app
              (CharacterLine.flagCharacterModule G (G.positiveRootCharacter ^ n))) ≫
        @appendRawCoframe.{u} K fieldInst algInst charInst G word i V g a c hend B p
            (G.positiveRootCharacter ^ n) j) := by
  have hN : CharacterLine.wordCharacterModule G (G.positiveRootCharacter ^ n) (word ++ [i]) =
      (Scheme.Modules.pullback (X := bsdhScheme G (word ++ [i])) (Y := (flagVariety G).scheme)
            (bsdhMap G (word ++ [i]))).obj
        (CharacterLine.flagCharacterModule G (G.positiveRootCharacter ^ n)) := rfl
  have hc := component_reindex
    (Scheme.Modules.pullbackComp (X := Spec (.of (Polynomial B))) (Y := projectiveScheme B
            (ULift.{u} (Fin 2))) (Z := bsdhScheme G (word ++ [i]))
            (projectiveLinePolynomialChart B ⟨j⟩) (projectiveAppendChart G i B p c)) hN
    (@appendPolynomialFrame.{u} K fieldInst algInst charInst G word i V g a c hend B p n ⟨j⟩).hom _
    (@appendPolynomialFrame_raw.{u} K fieldInst algInst charInst G word i V g a c hend B p n j)
  have hleft := word_cast_id (D := (Spec (.of (Polynomial B))).Modules)
    G (word ++ [i]) (G.positiveRootCharacter ^ n)
    (Scheme.Modules.pullback (X := Spec (.of (Polynomial B)))
      (Y := bsdhScheme G (word ++ [i]))
      (@CategoryStruct.comp Scheme.{u} Scheme.instCategory.toCategoryStruct
        (Spec (.of (Polynomial B))) (projectiveScheme B (ULift.{u} (Fin 2)))
        (bsdhScheme G (word ++ [i]))
        (projectiveLinePolynomialChart B ⟨j⟩) (projectiveAppendChart G i B p c))).obj
  have hright := @word_cast_id K fieldInst algInst charInst G (word ++ [i])
    (Spec (.of (Polynomial B))).Modules inferInstance (G.positiveRootCharacter ^ n)
    ((Scheme.Modules.pullback (X := projectiveScheme B (ULift.{u} (Fin 2)))
      (Y := bsdhScheme G (word ++ [i])) (projectiveAppendChart G i B p c)) ⋙
      Scheme.Modules.pullback (X := Spec (.of (Polynomial B)))
        (Y := projectiveScheme B (ULift.{u} (Fin 2)))
        (projectiveLinePolynomialChart B ⟨j⟩)).obj
  exact strip_component_casts hleft hright hc


private theorem canonical_raw_map (chi : G.characters) (j : Fin 2) :

    @Eq ((Scheme.Modules.pullback (X := Spec (.of (Polynomial B))) (Y := projectiveScheme B
            (ULift.{u} (Fin 2))) (projectiveLinePolynomialChart B ⟨j⟩)).obj
        ((Scheme.Modules.pullback (@CategoryStruct.comp Scheme.{u} (inferInstanceAs
            (CategoryStruct Scheme.{u}))
          (projectiveScheme B (ULift.{u} (Fin 2))) (bsdhScheme G (word ++ [i])) (flagVariety
            G).scheme
          (projectiveAppendChart G i B p c) (bsdhMap G (word ++ [i])))).obj
            (CharacterLine.flagCharacterModule G chi)) ⟶
      SheafOfModules.unit (Spec (.of (Polynomial B))).ringCatSheaf)
      (@appendRawCoframe.{u} K fieldInst algInst charInst G word i V g a c hend B p chi j)
      ((Scheme.Modules.pullbackComp (projectiveLinePolynomialChart B ⟨j⟩)
        (@CategoryStruct.comp Scheme.{u} Scheme.instCategory.toCategoryStruct
          (projectiveScheme B (ULift.{u} (Fin 2))) (bsdhScheme G (word ++ [i])) (flagVariety
            G).scheme
          (projectiveAppendChart G i B p c) (bsdhMap G (word ++ [i])))).hom.app
          (CharacterLine.flagCharacterModule G chi) ≫
      @appendEvaluation.{u} K fieldInst algInst charInst G word i V g a c hend B p chi j) := by
  have hF : Scheme.Modules.pullback (appendEndpoint G word i V c B p) ⋙
      Scheme.Modules.pullback (projectiveLinePolynomialChart B ⟨j⟩) =
      Scheme.Modules.pullback (@CategoryStruct.comp Scheme.{u} (inferInstanceAs
            (CategoryStruct Scheme.{u}))
          (projectiveScheme B (ULift.{u} (Fin 2))) (bsdhScheme G (word ++ [i])) (flagVariety
            G).scheme
          (projectiveAppendChart G i B p c) (bsdhMap G (word ++ [i]))) ⋙
      Scheme.Modules.pullback (projectiveLinePolynomialChart B ⟨j⟩) := rfl
  have hH : Scheme.Modules.pullback (projectiveLinePolynomialChart B ⟨j⟩ ≫
      appendEndpoint G word i V c B p) =
      Scheme.Modules.pullback (projectiveLinePolynomialChart B ⟨j⟩ ≫
        (@CategoryStruct.comp Scheme.{u} Scheme.instCategory.toCategoryStruct
          (projectiveScheme B (ULift.{u} (Fin 2))) (bsdhScheme G (word ++ [i])) (flagVariety
            G).scheme
          (projectiveAppendChart G i B p c) (bsdhMap G (word ++ [i])))) := rfl
  have hE : HEq
      (Scheme.Modules.pullbackComp (projectiveLinePolynomialChart B ⟨j⟩)
        (appendEndpoint G word i V c B p))
      (Scheme.Modules.pullbackComp (projectiveLinePolynomialChart B ⟨j⟩)
        (@CategoryStruct.comp Scheme.{u} Scheme.instCategory.toCategoryStruct
          (projectiveScheme B (ULift.{u} (Fin 2))) (bsdhScheme G (word ++ [i])) (flagVariety
            G).scheme
          (projectiveAppendChart G i B p c) (bsdhMap G (word ++ [i])))) := HEq.rfl
  have hc := iso_app_reindex hF hH _ _ hE (CharacterLine.flagCharacterModule G chi)
    (@appendRawCoframe.{u} K fieldInst algInst charInst G word i V g a c hend B p chi j)
    (@appendEvaluation.{u} K fieldInst algInst charInst G word i V g a c hend B p chi j)
    (raw_map_eq G word i V g a c hend B p chi j)
  have hrho : eqToHom (congrArg (fun L => L.obj (CharacterLine.flagCharacterModule G chi))
      hF.symm) = 𝟙 _ := rfl
  have hsigma : eqToHom (congrArg (fun L => L.obj (CharacterLine.flagCharacterModule G chi))
      hH.symm) = 𝟙 _ := rfl
  exact strip_component_casts hrho hsigma hc

/-- Pullback associativity expresses the append coframe as endpoint evaluation. -/
theorem appendFlagCoframe_assoc (n : ℕ) (j : Fin 2) :
    @appendFlagCoframe.{u} K fieldInst algInst charInst G word i V g a c hend B p n j =
      CategoryStruct.comp
        (Z := SheafOfModules.unit (Spec (.of (Polynomial B))).ringCatSheaf)
        ((Scheme.Modules.pullbackComp
        (X := Spec (.of (Polynomial B))) (Y := bsdhScheme G (word ++ [i]))
        (Z := (flagVariety G).scheme)
        (@CategoryStruct.comp Scheme.{u} Scheme.instCategory.toCategoryStruct
          (Spec (.of (Polynomial B))) (projectiveScheme B (ULift.{u} (Fin 2))) (bsdhScheme G
            (word ++ [i]))
          (projectiveLinePolynomialChart B ⟨j⟩) (projectiveAppendChart G i B p c))
        (bsdhMap G (word ++ [i]))).hom.app
          (CharacterLine.flagCharacterModule G (G.positiveRootCharacter ^ n)))
        (CategoryStruct.comp
          (Z := SheafOfModules.unit (Spec (.of (Polynomial B))).ringCatSheaf)
          ((Scheme.Modules.pullbackCongr
        (X := Spec (.of (Polynomial B))) (Y := (flagVariety G).scheme)
        (Category.assoc (W := Spec (.of (Polynomial B)))
          (X := projectiveScheme B (ULift.{u} (Fin 2)))
          (Y := bsdhScheme G (word ++ [i])) (Z := (flagVariety G).scheme)
        (projectiveLinePolynomialChart B ⟨j⟩) (projectiveAppendChart G i B p c)
        (bsdhMap G (word ++ [i])))).hom.app
          (CharacterLine.flagCharacterModule G (G.positiveRootCharacter ^ n)))
          (@appendEvaluation.{u} K fieldInst algInst charInst G word i V g a c hend B p
            (G.positiveRootCharacter ^ n) j)) := by
  have hFrameFact := @canonical_raw.{u} K fieldInst algInst charInst G word i V g a c hend B p n j
  have hRawFact := @canonical_raw_map.{u} K fieldInst algInst charInst G word i V g a c hend B p
    (G.positiveRootCharacter ^ n) j
  have hStep0 := @SchubertGeometry.CharacterLine.CoframeTransport.coframe_to_assoc.{u}
    (Spec (.of (Polynomial B))) (projectiveScheme B (ULift.{u} (Fin 2)))
    (bsdhScheme G (word ++ [i])) (flagVariety G).scheme
    (projectiveLinePolynomialChart B ⟨j⟩) (projectiveAppendChart G i B p c)
    (bsdhMap G (word ++ [i]))
    (CharacterLine.flagCharacterModule G (G.positiveRootCharacter ^ n))
    (SheafOfModules.unit (Spec (.of (Polynomial B))).ringCatSheaf)
  have hStep1 := hStep0
    (@appendFlagCoframe.{u} K fieldInst algInst charInst G word i V g a c hend B p n j)
    (@appendRawCoframe.{u} K fieldInst algInst charInst G word i V g a c hend B p
            (G.positiveRootCharacter ^ n) j)
    (@appendEvaluation.{u} K fieldInst algInst charInst G word i V g a c hend B p
            (G.positiveRootCharacter ^ n) j)
  have hStep2 := hStep1 hFrameFact
  have hAssoc := hStep2 hRawFact
  exact hAssoc



end SchubertGeometry.RetainedCharacter
