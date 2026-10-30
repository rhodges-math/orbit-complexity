import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.MatchingCoframeEvaluation
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.RefinedAppendUnits
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Matching coframe evaluation on an affine refinement

The original matching coframe is pulled along a specified map to its chart.
Its evaluation is the character evaluation of the composite group lift.
All comparison and pullback identities are proved over arbitrary objects.
-/

set_option autoImplicit false

noncomputable section
universe u v w

open AlgebraicGeometry CategoryTheory Opposite
open CategoryTheory.Limits (Cocone IsColimit)
open AlgebraicGeometry.Scheme.Modules
open ReductiveGroups GroupActions
open FrobeniusSplitting.CharacterLine FrobeniusSplitting.RetainedCharacter
open scoped CategoryTheory.MonObj

namespace SchubertGeometry.RetainedCharacter

open private singletonIndex from OrbitComplexity.FrobeniusSplitting.Modules.MatchingModule
open private chartLift lift_quotient from
  OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.WordMatchingBase
open private frame_on_composite from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.RefinedAppendUnits
open private CoframeTransport.pullCoframe CoframeTransport.evaluation_base_change from
  OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.CoframeTransport

private theorem flatten_evaluation {C D : Type v} [Category.{w} C] [Category.{w} D]
    (F : C ⥤ D) {L M N : C} {T : D} (A : L ≅ N) (W : L ≅ M)
    (e : F.obj M ⟶ T) (b : F.obj N ⟶ T)
    (h : F.map W.hom ≫ e = F.map A.hom ≫ b) :
    F.map (A.symm ≪≫ W).hom ≫ e = b := by
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.map_comp, Category.assoc]
  rw [h, ← Category.assoc, ← F.map_comp, A.inv_hom_id, F.map_id, Category.id_comp]

private theorem composite_evaluation {X Y Z : Scheme.{u}} (u : X ⟶ Y) (j : Y ⟶ Z)
    {L M : Z.Modules} (d : L ⟶ M)
    (E : (pullback j).obj M ≅ SheafOfModules.unit Y.ringCatSheaf)
    (b : (pullback j).obj L ⟶ SheafOfModules.unit Y.ringCatSheaf)
    (h : (pullback j).map d ≫ E.hom = b) :
    (pullback (u ≫ j)).map d ≫
        (frame_on_composite u j (u ≫ j) rfl M E).hom =
      CoframeTransport.pullCoframe u j L b := by
  have hn := (pullbackComp u j).inv.naturality d
  change (pullback (u ≫ j)).map d ≫
      ((pullbackComp u j).inv.app M ≫ (pullback u).map E.hom ≫
        (pullbackObjUnitIso u).hom) =
    (pullbackComp u j).inv.app L ≫ (pullback u).map b ≫
      (pullbackObjUnitIso u).hom
  calc
    _ = (pullbackComp u j).inv.app L ≫
        (pullback u).map ((pullback j).map d) ≫
          (pullback u).map E.hom ≫ (pullbackObjUnitIso u).hom := by
      simpa only [Functor.comp_map, Category.assoc] using
        congrArg (fun t => t ≫ (pullback u).map E.hom ≫ (pullbackObjUnitIso u).hom) hn
    _ = _ := by
      simpa only [Functor.map_comp, Category.assoc] using
        congrArg (fun t => (pullbackComp u j).inv.app L ≫
          (pullback u).map t ≫ (pullbackObjUnitIso u).hom) h

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K) {J : Type u}
    (F : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} K)
    [∀ {s t} (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (F.map f).hom.toRingHom))]
    [((F.op ⋙ algSpec (.of K) ⋙ Over.forget (Spec (.of K))) ⋙
      Scheme.forget).IsLocallyDirected]
    (cF : Cocone (F.op ⋙ algSpec (.of K))) (hcF : IsColimit cF)
    (word : List G.rootBase.support) (q : cF.pt.left ⟶ bsdhScheme G word) (n : ℕ)
    (point : J → G.points)
    (a : ∀ j, (algSpec (.of K)).obj (op (F.obj (singletonIndex j))) ⟶
      (oppositeUnipotentVariety G).toOver)
    (ha : ∀ j, (a j).left ≫ (flagChartMorphism G (point j)).left =
      (cF.ι.app (op (singletonIndex j))).left ≫ (q ≫ bsdhMap G word))
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

/-- The canonical word comparison after combining its two flag pullbacks. -/
def wordFlagMatchingIso :
    (pullback (q ≫ bsdhMap G word)).obj
        (CharacterLine.flagCharacterModule G (G.positiveRootCharacter ^ n)) ≅
      matchingModule F cF (wordTransitionUnit G F beta) n :=
  ((pullbackComp q (bsdhMap G word)).app
      (CharacterLine.flagCharacterModule G (G.positiveRootCharacter ^ n))).symm ≪≫
    wordCharacterMatchingIso G F cF hcF word q n point a ha beta hgroup hco hn

/-- On any refinement of an original matching chart, the canonical coframe
evaluates at the composite group lift, for every full character power. -/
theorem wordMatchingFrame_composite
    (s : {s : Finset J // s.Nonempty}) (j : J) (hj : j ∈ s.val)
    (P : Over (Spec (.of K)))
    (f : P ⟶ (algSpec (.of K)).obj (op (F.obj s))) :
    (pullback (f.left ≫ (cF.ι.app (op s)).left)).map
        (wordFlagMatchingIso G F cF hcF word q n point a ha beta hgroup hco hn).hom ≫
      (frame_on_composite f.left (cF.ι.app (op s)).left
        (f.left ≫ (cF.ι.app (op s)).left) rfl
        (matchingModule F cF (wordTransitionUnit G F beta) n)
        (localCharacterTrivialization F cF hcF (wordTransitionUnit G F beta)
          n hco hn s j hj)).hom =
    (pullbackComp (f.left ≫ (cF.ι.app (op s)).left) (q ≫ bsdhMap G word)).hom.app
        (CharacterLine.flagCharacterModule G (G.positiveRootCharacter ^ n)) ≫
      CharacterLine.characterFrameEvaluation G (G.positiveRootCharacter ^ n) P
        ((f.left ≫ (cF.ι.app (op s)).left) ≫ (q ≫ bsdhMap G word))
        (f ≫ chartLift G F point a s j hj)
        (((Category.assoc f.left (chartLift G F point a s j hj).left (flagQuotient G)).trans
          (congrArg (fun t => f.left ≫ t) (lift_quotient G F cF word q point a ha s j hj))).trans
            (Category.assoc f.left (cF.ι.app (op s)).left (q ≫ bsdhMap G word)).symm) := by
  have h₀ := wordMatchingFrame_evaluation G F cF hcF word q n
    point a ha beta hgroup hco hn s j hj
  have h₁ := flatten_evaluation (pullback (cF.ι.app (op s)).left)
    ((pullbackComp q (bsdhMap G word)).app
      (CharacterLine.flagCharacterModule G (G.positiveRootCharacter ^ n)))
    (wordCharacterMatchingIso G F cF hcF word q n point a ha beta hgroup hco hn)
    (localCharacterTrivialization F cF hcF (wordTransitionUnit G F beta) n hco hn s j hj).hom
    _ h₀
  have h₂ := composite_evaluation f.left (cF.ι.app (op s)).left
    (wordFlagMatchingIso G F cF hcF word q n point a ha beta hgroup hco hn).hom
    (localCharacterTrivialization F cF hcF (wordTransitionUnit G F beta) n hco hn s j hj)
    _ h₁
  have h₃ := CoframeTransport.evaluation_base_change G (G.positiveRootCharacter ^ n)
    ((algSpec (.of K)).obj (op (F.obj s))) P f (cF.ι.app (op s)).left
    (q ≫ bsdhMap G word) (f.left ≫ (cF.ι.app (op s)).left) rfl
    (chartLift G F point a s j hj) (lift_quotient G F cF word q point a ha s j hj)
  exact h₂.trans h₃

end SchubertGeometry.RetainedCharacter
