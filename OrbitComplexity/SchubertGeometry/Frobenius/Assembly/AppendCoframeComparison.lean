import OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.WordMatching
import OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.UnitTrivialization
import OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.AppendSections
import OrbitComplexity.FrobeniusSplitting.Normality.Assembly.FrameUnitRetention
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # The coframe units on a specified append refinement

The matching-line coframe and the projective append coframe are constructed
from their respective chart isomorphisms. Their ratio is retained in the fixed
coefficient models, together with every power of the same unit.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open ReductiveGroups GroupActions FrobeniusSplitting
open FrobeniusSplitting.RetainedCharacter
open CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct

noncomputable section
universe u v

namespace SchubertGeometry.RetainedCharacter

open private singletonIndex from OrbitComplexity.FrobeniusSplitting.Modules.MatchingModule
open private chartLift
  from OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.WordMatchingBase

private abbrev O (X : Scheme.{u}) : X.Modules := SheafOfModules.unit X.ringCatSheaf

private def comparisonCoframe {P X Y Q : Scheme.{u}}
    (j : P ⟶ X) (q : X ⟶ Y) (k : P ⟶ Q) (r : Q ⟶ Y)
    (h : j ≫ q = k ≫ r) (M : X.Modules) (N : Y.Modules)
    (E : M ≅ (Scheme.Modules.pullback q).obj N)
    (e : (Scheme.Modules.pullback r).obj N ≅ O Q) :
    (Scheme.Modules.pullback j).obj M ≅ O P :=
  (Scheme.Modules.pullback j).mapIso E ≪≫
    (Scheme.Modules.pullbackComp j q).app N ≪≫
    (Scheme.Modules.pullbackCongr h).app N ≪≫
    ((Scheme.Modules.pullbackComp k r).app N).symm ≪≫
    (Scheme.Modules.pullback k).mapIso e ≪≫ Scheme.Modules.pullbackObjUnitIso k

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K) (word : List G.rootBase.support) (i : G.rootBase.support)

/-- The word character line has a specified coframe on either polynomial chart
of the given append product chart. -/
def appendPolynomialFrame
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
    (B : CommAlgCat.{u} K) (p : (algSpec (.of K)).obj (op B) ⟶ V)
    (n : ℕ) (ε : ULift.{u} (Fin 2)) :
    (Scheme.Modules.pullback
      (X := Spec (.of (Polynomial B))) (Y := bsdhScheme G (word ++ [i]))
      (@CategoryStruct.comp Scheme.{u} Scheme.instCategory.toCategoryStruct
        (Spec (.of (Polynomial B))) (projectiveScheme B (ULift.{u} (Fin 2)))
        (bsdhScheme G (word ++ [i]))
        (projectiveLinePolynomialChart B ε) (projectiveAppendChart G i B p c))).obj
        (CharacterLine.wordCharacterModule G (G.positiveRootCharacter ^ n)
          (word ++ [i])) ≅
      SheafOfModules.unit (Spec (.of (Polynomial B))).ringCatSheaf :=
  ((Scheme.Modules.pullbackComp
    (X := Spec (.of (Polynomial B))) (Y := projectiveScheme B (ULift.{u} (Fin 2)))
    (Z := bsdhScheme G (word ++ [i])) (projectiveLinePolynomialChart B ε)
    (projectiveAppendChart G i B p c)).app
      (CharacterLine.wordCharacterModule G (G.positiveRootCharacter ^ n) (word ++ [i]))).symm ≪≫
    (Scheme.Modules.pullback
      (X := Spec (.of (Polynomial B))) (Y := projectiveScheme B (ULift.{u} (Fin 2)))
      (projectiveLinePolynomialChart B ε)).mapIso
      (CharacterLine.appendCharacterDegreeIso G word i V g a c hend B p n) ≪≫
    (Scheme.Modules.restrictFunctorIsoPullback
      (projectiveLinePolynomialChart B ε)).symm.app
        (ProjectiveLine.projectiveTransitionModule B (2 * n)) ≪≫
    ProjectiveLine.projectiveTransitionChart B (2 * n) ε

variable {J : Type u}
    (F : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} K)
    [hFopen : ∀ {s t} (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (F.map f).hom.toRingHom))]
    [hFdir : ((F.op ⋙ algSpec (.of K) ⋙ Over.forget (Spec (.of K))) ⋙
      Scheme.forget).IsLocallyDirected]
    (cF : Cocone (F.op ⋙ algSpec (.of K))) (hcF : IsColimit cF)
    (q : cF.pt.left ⟶ bsdhScheme G (word ++ [i]))
    (point : J → G.points)
    (a : ∀ j, (algSpec (.of K)).obj (op (F.obj (singletonIndex j))) ⟶
      (oppositeUnipotentVariety G).toOver)
    (ha : ∀ j, (a j).left ≫ (flagChartMorphism G (point j)).left =
      (cF.ι.app (op (singletonIndex j))).left ≫ (q ≫ bsdhMap G (word ++ [i])))
    (beta : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val)
      (k : J) (_ : k ∈ s.val),
      (algSpec (.of K)).obj (op (F.obj s)) ⟶ (borelVariety G).toOver)
    (hgroup : ∀ s j hj k hk, chartLift G F point a s j hj =
      chartLift G F point a s k hk * (beta s j hj k hk ≫ borelInclusion G))
    (hco : ∀ s j hj k hk l hl, wordTransitionUnit G F beta s j hj l hl =
      wordTransitionUnit G F beta s k hk l hl * wordTransitionUnit G F beta s j hj k hk)
    (hn : ∀ s t (f : s ⟶ t) j hj k hk,
      Units.map (F.map f).hom.toMonoidHom (wordTransitionUnit G F beta s j hj k hk) =
        wordTransitionUnit G F beta t j ((leOfHom f) hj) k ((leOfHom f) hk))

private def fieldAppendCoframe
    (s : {s : Finset J // s.Nonempty})
    (V : Over (Spec (.of K))) (g : G.points)
    (b : V ⟶ (oppositeUnipotentVariety G).toOver)
    (c : V ⊗ (schubertVariety G
      (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver ⟶
        Over.mk (bsdhToSpec G (word ++ [i])))
    (hend : c.left ≫ (bsdhAppendIso G word i).hom.left ≫
      pullback.snd (bsdhMap G word) (flagBundleProjection G
        (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val))) =
      (b ⊗ₘ 𝟙 (schubertVariety G
        (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver).left ≫
          flagBundleChart G _ g)
    (B : CommAlgCat.{u} K) (p : (algSpec (.of K)).obj (op B) ⟶ V)
    (ε : ULift.{u} (Fin 2))
    (k : Spec (.of (F.obj s)) ⟶ Spec (.of (Polynomial B)))
    (hk : (cF.ι.app (op s)).left ≫ q =
      k ≫ projectiveLinePolynomialChart B ε ≫ projectiveAppendChart G i B p c) :
    (Scheme.Modules.pullback (cF.ι.app (op s)).left).obj
      (matchingModule F cF (wordTransitionUnit G F beta) 1) ≅ O (Spec (.of (F.obj s))) :=
  comparisonCoframe (cF.ι.app (op s)).left q k
    (projectiveLinePolynomialChart B ε ≫ projectiveAppendChart G i B p c) hk
    (matchingModule F cF (wordTransitionUnit G F beta) 1)
    (CharacterLine.wordCharacterModule G (G.positiveRootCharacter ^ 1) (word ++ [i]))
    (wordCharacterMatchingIso G F cF hcF (word ++ [i]) q 1 point a ha beta hgroup hco hn).symm
    (appendPolynomialFrame G word i V g b c hend B p 1 ε)

/-- The specified append factorization determines a coordinate unit comparing
the matching coframe with the degree-one projective append coframe. -/
def appendFrameUnit
    (s : {s : Finset J // s.Nonempty})
    (V : Over (Spec (.of K))) (g : G.points)
    (b : V ⟶ (oppositeUnipotentVariety G).toOver)
    (c : V ⊗ (schubertVariety G
      (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver ⟶
        Over.mk (bsdhToSpec G (word ++ [i])))
    (hend : c.left ≫ (bsdhAppendIso G word i).hom.left ≫
      pullback.snd (bsdhMap G word) (flagBundleProjection G
        (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val))) =
      (b ⊗ₘ 𝟙 (schubertVariety G
        (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver).left ≫
          flagBundleChart G _ g)
    (B : CommAlgCat.{u} K) (p : (algSpec (.of K)).obj (op B) ⟶ V)
    (ε : ULift.{u} (Fin 2))
    (k : Spec (.of (F.obj s)) ⟶ Spec (.of (Polynomial B)))
    (hk : (cF.ι.app (op s)).left ≫ q =
      k ≫ projectiveLinePolynomialChart B ε ≫ projectiveAppendChart G i B p c) :
    (F.obj s)ˣ :=
  affineCoframeUnit (F.obj s)
    (localCharacterTrivialization F cF hcF (wordTransitionUnit G F beta) 1 hco hn
      s s.property.choose s.property.choose_spec)
    (fieldAppendCoframe G word i F cF hcF q point a ha beta hgroup hco hn
      s V g b c hend B p ε k hk)

variable
    (V : {s : Finset J // s.Nonempty} → Over (Spec (.of K)))
    (g : {s : Finset J // s.Nonempty} → G.points)
    (b : ∀ s, V s ⟶ (oppositeUnipotentVariety G).toOver)
    (c : ∀ s, V s ⊗ (schubertVariety G
      (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver ⟶
        Over.mk (bsdhToSpec G (word ++ [i])))
    (hend : ∀ s, (c s).left ≫ (bsdhAppendIso G word i).hom.left ≫
      pullback.snd (bsdhMap G word) (flagBundleProjection G
        (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val))) =
      (b s ⊗ₘ 𝟙 (schubertVariety G
        (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver).left ≫
          flagBundleChart G _ (g s))
    (B : {s : Finset J // s.Nonempty} → CommAlgCat.{u} K)
    (p : ∀ s, (algSpec (.of K)).obj (op (B s)) ⟶ V s)
    (ε : {s : Finset J // s.Nonempty} → ULift.{u} (Fin 2))
    (k : ∀ s, Spec (.of (F.obj s)) ⟶ Spec (.of (Polynomial (B s))))
    (hk : ∀ s, (cF.ι.app (op s)).left ≫ q =
      k s ≫ projectiveLinePolynomialChart (B s) (ε s) ≫
        projectiveAppendChart G i (B s) (p s) (c s))

end SchubertGeometry.RetainedCharacter
