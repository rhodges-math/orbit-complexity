import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendCoframeAssociativity
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # The polynomial append coframe as lift evaluation

The append coframe evaluates the prescribed lift on both polynomial charts and
for every character power.
-/

set_option autoImplicit false
set_option maxHeartbeats 100000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ReductiveGroups GroupActions
open CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj

noncomputable section
universe u

namespace SchubertGeometry.RetainedCharacter

open private polynomialBase
  from OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.AppendCoordinates
open private appendPolynomialLift appendPolynomialLift_endpoint
  from OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.AppendCoframes
open private evaluation_map_eq
  from OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendCoframeAssociativity

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
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



private theorem coframe_evaluation (chi : G.characters)
    {X : Scheme.{u}} (base : X ⟶ Spec (.of K))
    {m n : X ⟶ (flagVariety G).scheme} (hmn : m = n)
    (k : Over.mk base ⟶ (reductiveVariety G).toOver)
    (hk : k.left ≫ flagQuotient G = m)
    {P T : X.Modules}
    {d : P ⟶ (Scheme.Modules.pullback m).obj (CharacterLine.flagCharacterModule G chi)}
    {ev : (Scheme.Modules.pullback n).obj (CharacterLine.flagCharacterModule G chi) ⟶ T}
    {frame : P ⟶ T}
    (final : (Scheme.Modules.pullback m).obj (CharacterLine.flagCharacterModule G chi) ⟶ T)
    (hf : frame = d ≫ (Scheme.Modules.pullbackCongr hmn).hom.app
      (CharacterLine.flagCharacterModule G chi) ≫ ev)
    (hT : T = SheafOfModules.unit X.ringCatSheaf)
    (he : HEq ev (CharacterLine.characterFrameEvaluation G chi (Over.mk base) n k
      (hk.trans hmn)))
    (hfinal : HEq final (CharacterLine.characterFrameEvaluation G chi (Over.mk base) m k hk)) :
    frame = d ≫ final := by
  cases hT
  have hev := eq_of_heq he
  have hfin := eq_of_heq hfinal
  rw [hf, hev, CharacterLine.characterFrameEvaluation_congr G chi (Over.mk base) hmn k hk,
    ← hfin]

/-- Pullback composition at a module is unchanged when the middle scheme is
replaced by an equal one. -/
private theorem pullbackComp_app_heq {X Y Y' Z : Scheme.{u}} (hY : Y = Y')
    (f : X ⟶ Y) (f' : X ⟶ Y') (g : Y ⟶ Z) (g' : Y' ⟶ Z) (hf : HEq f f') (hg : HEq g g')
    (M : Z.Modules) :
    HEq ((Scheme.Modules.pullbackComp f g).hom.app M)
      ((Scheme.Modules.pullbackComp f' g').hom.app M) := by
  subst hY
  cases hf
  cases hg
  rfl

/-- The append polynomial coframe evaluates the prescribed regular lift,
with the original word-to-flag comparison on either polynomial chart. -/
theorem appendPolynomialFrame_evaluation (n : ℕ) (j : Fin 2) :
    @Eq ((Scheme.Modules.pullback (projectiveLinePolynomialChart B ⟨j⟩ ≫
        projectiveAppendChart G i B p c)).obj
      ((Scheme.Modules.pullback (bsdhMap G (word ++ [i]))).obj
        (CharacterLine.flagCharacterModule G (G.positiveRootCharacter ^ n))) ⟶
      SheafOfModules.unit (Spec (.of (Polynomial B))).ringCatSheaf)
      (appendPolynomialFrame G word i V g a c hend B p n ⟨j⟩).hom
      ((Scheme.Modules.pullbackComp
        (projectiveLinePolynomialChart B ⟨j⟩ ≫ projectiveAppendChart G i B p c)
        (bsdhMap G (word ++ [i]))).hom.app
          (CharacterLine.flagCharacterModule G (G.positiveRootCharacter ^ n)) ≫
      CharacterLine.characterFrameEvaluation G (G.positiveRootCharacter ^ n)
        (polynomialBase B)
        ((projectiveLinePolynomialChart B ⟨j⟩ ≫ projectiveAppendChart G i B p c) ≫
          bsdhMap G (word ++ [i]))
        (appendPolynomialLift G i V g a B p j)
        ((appendPolynomialLift_endpoint G word i V g a c hend B p j).trans
          (Category.assoc (projectiveLinePolynomialChart B ⟨j⟩)
            (projectiveAppendChart G i B p c) (bsdhMap G (word ++ [i]))).symm)) := by
  have hk := (appendPolynomialLift_endpoint G word i V g a c hend B p j).trans
    (Category.assoc (projectiveLinePolynomialChart B ⟨j⟩)
      (projectiveAppendChart G i B p c) (bsdhMap G (word ++ [i]))).symm
  have h := coframe_evaluation G (G.positiveRootCharacter ^ n)
    (X := Spec (.of (Polynomial B))) (polynomialBase B).hom
    (Category.assoc (projectiveLinePolynomialChart B ⟨j⟩)
      (projectiveAppendChart G i B p c) (bsdhMap G (word ++ [i])))
    (appendPolynomialLift G i V g a B p j) hk
    (CharacterLine.characterFrameEvaluation G (G.positiveRootCharacter ^ n)
      (polynomialBase B)
      ((projectiveLinePolynomialChart B ⟨j⟩ ≫ projectiveAppendChart G i B p c) ≫
        bsdhMap G (word ++ [i])) (appendPolynomialLift G i V g a B p j) hk)
    (appendFlagCoframe_assoc G word i V g a c hend B p n j)
    rfl
    (heq_of_eq (evaluation_map_eq G word i V g a c hend B p (G.positiveRootCharacter ^ n) j
      (hk.trans (Category.assoc (projectiveLinePolynomialChart B ⟨j⟩)
        (projectiveAppendChart G i B p c) (bsdhMap G (word ++ [i]))))))
    HEq.rfl
  -- `h` names the middle scheme `bsdhScheme`, the statement the chart's codomain; the explicit
  -- bridge spares the kernel an unfolding of `bsdhScheme`.
  have hd := pullbackComp_app_heq
    (Y := (Over.mk (bsdhToSpec G (word ++ [i]))).left) (Y' := bsdhScheme G (word ++ [i])) rfl
    (projectiveLinePolynomialChart B ⟨j⟩ ≫ projectiveAppendChart G i B p c)
    (@CategoryStruct.comp Scheme.{u} Scheme.instCategory.toCategoryStruct
      (Spec (.of (Polynomial B))) (projectiveScheme B (ULift.{u} (Fin 2)))
      (bsdhScheme G (word ++ [i]))
      (projectiveLinePolynomialChart B ⟨j⟩) (projectiveAppendChart G i B p c))
    (bsdhMap G (word ++ [i])) (bsdhMap G (word ++ [i])) HEq.rfl HEq.rfl
    (CharacterLine.flagCharacterModule G (G.positiveRootCharacter ^ n))
  have hd' := by with_reducible exact eq_of_heq hd
  have h3 := (appendFlagCoframe_eq G word i V g a c hend B p n j).symm.trans h
  with_reducible exact h3.trans (congrArg (· ≫ _) hd'.symm)

end SchubertGeometry.RetainedCharacter
