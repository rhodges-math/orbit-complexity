import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.RefinedCharacterCoframes
import OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.FrameComposition
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Flag evaluation of the original refined matching coframe

The canonical comparison combines the word and flag pullbacks before
coordinates are taken. Its coframe is still pulled from the original
matching chart, on the same matching line in every degree.
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
open private associate_coframe from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendPowerFrames
open private flagComparison comparison_prefix_cancel from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.CoframeEvaluations

private theorem unflatten_evaluation {C D : Type v} [Category.{w} C] [Category.{w} D]
    (F : C ⥤ D) {L M N : C} {T : D} (A : L ≅ N) (W : L ≅ M)
    (e : F.obj M ⟶ T) (b : F.obj N ⟶ T)
    (h : F.map (A.symm ≪≫ W).hom ≫ e = b) :
    F.map W.hom ≫ e = F.map A.hom ≫ b := by
  have hh : F.map A.hom ≫ F.map A.inv = 𝟙 _ := by
    rw [← F.map_comp, A.hom_inv_id, F.map_id]
  have h₀ := congrArg (fun t => F.map A.hom ≫ t) h
  simpa only [Iso.trans_hom, Iso.symm_hom, Functor.map_comp,
    ← Category.assoc, hh, Category.id_comp] using h₀

private theorem refined_quotient {C : Type v} [Category.{w} C]
    {P Q X Y Z H : C} (u : P ⟶ Q) (k : Q ⟶ H) (π : H ⟶ Z)
    (j : Q ⟶ X) (q : X ⟶ Y) (z : Y ⟶ Z) (h : k ≫ π = j ≫ (q ≫ z)) :
    (u ≫ k) ≫ π = ((u ≫ j) ≫ q) ≫ z := by
  simpa only [Category.assoc] using congrArg (fun t => u ≫ t) h

private theorem flag_evaluation {P X Y Z : Scheme.{u}}
    (j : P ⟶ X) (q : X ⟶ Y) (z : Y ⟶ Z) (L : Z.Modules) (M : X.Modules)
    (W : (pullback q).obj ((pullback z).obj L) ≅ M)
    (D : (pullback (q ≫ z)).obj L ≅ M)
    (hD : D = ((pullbackComp q z).app L).symm ≪≫ W)
    (E : (pullback j).obj M ≅ SheafOfModules.unit P.ringCatSheaf)
    (J : (pullback ((j ≫ q) ≫ z)).obj L ≅ (pullback j).obj M)
    (hJ : J = flagComparison j q z L M W)
    (e₀ : (pullback (j ≫ (q ≫ z))).obj L ⟶ SheafOfModules.unit P.ringCatSheaf)
    (e₁ : (pullback ((j ≫ q) ≫ z)).obj L ⟶ SheafOfModules.unit P.ringCatSheaf)
    (h : (pullback j).map D.hom ≫ E.hom =
      (pullbackComp j (q ≫ z)).hom.app L ≫ e₀)
    (hc : (pullbackCongr (Category.assoc j q z)).hom.app L ≫ e₀ = e₁) :
    J.hom ≫ E.hom = e₁ := by
  subst D
  subst J
  have h₀ := unflatten_evaluation (pullback j)
    ((pullbackComp q z).app L) W E.hom _ h
  have h₁ := associate_coframe j q z L e₀ e₁ hc
  exact comparison_prefix_cancel
    ((pullbackComp (j ≫ q) z).app L)
    ((pullbackComp j q).app ((pullback z).obj L))
    ((pullback j).mapIso W) E.hom _ (h₀.trans h₁)

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


/-- The original matching coframe on an arbitrary chart refinement has the
canonical flag evaluation, with the word comparison and its maps retained. -/
theorem matchingRefinedCoframe_eval
    (s : {s : Finset J // s.Nonempty}) (j : J) (hj : j ∈ s.val)
    (P : Over (Spec (.of K)))
    (f : P ⟶ (algSpec (.of K)).obj (op (F.obj s))) :
    (flagChartComparison G word n (f.left ≫ (cF.ι.app (op s)).left) q
      (matchingModule F cF (wordTransitionUnit G F beta) n)
      (wordCharacterMatchingIso G F cF hcF word q n point a ha beta hgroup hco hn)).hom ≫
      (frame_on_composite f.left (cF.ι.app (op s)).left
        (f.left ≫ (cF.ι.app (op s)).left) rfl
        (matchingModule F cF (wordTransitionUnit G F beta) n)
        (localCharacterTrivialization F cF hcF (wordTransitionUnit G F beta)
          n hco hn s j hj)).hom =
    CharacterLine.characterFrameEvaluation G (G.positiveRootCharacter ^ n) P
      (((f.left ≫ (cF.ι.app (op s)).left) ≫ q) ≫ bsdhMap G word)
      (f ≫ chartLift G F point a s j hj)
      (refined_quotient f.left (chartLift G F point a s j hj).left (flagQuotient G)
        (cF.ι.app (op s)).left q (bsdhMap G word)
        (lift_quotient G F cF word q point a ha s j hj)) := by
  refine flag_evaluation (f.left ≫ (cF.ι.app (op s)).left) q (bsdhMap G word)
    (CharacterLine.flagCharacterModule G (G.positiveRootCharacter ^ n))
    (matchingModule F cF (wordTransitionUnit G F beta) n)
    (wordCharacterMatchingIso G F cF hcF word q n point a ha beta hgroup hco hn)
    (wordFlagMatchingIso G F cF hcF word q n point a ha beta hgroup hco hn) rfl
    (frame_on_composite f.left (cF.ι.app (op s)).left
      (f.left ≫ (cF.ι.app (op s)).left) rfl
      (matchingModule F cF (wordTransitionUnit G F beta) n)
      (localCharacterTrivialization F cF hcF (wordTransitionUnit G F beta)
        n hco hn s j hj))
    (flagChartComparison G word n (f.left ≫ (cF.ι.app (op s)).left) q
      (matchingModule F cF (wordTransitionUnit G F beta) n)
      (wordCharacterMatchingIso G F cF hcF word q n point a ha beta hgroup hco hn)) rfl
    (CharacterLine.characterFrameEvaluation G (G.positiveRootCharacter ^ n) P
      ((f.left ≫ (cF.ι.app (op s)).left) ≫ (q ≫ bsdhMap G word))
      (f ≫ chartLift G F point a s j hj)
      ((refined_quotient f.left (chartLift G F point a s j hj).left (flagQuotient G)
        (cF.ι.app (op s)).left q (bsdhMap G word)
        (lift_quotient G F cF word q point a ha s j hj)).trans
          (Category.assoc (f.left ≫ (cF.ι.app (op s)).left) q (bsdhMap G word))))
    _ ?_ ?_
  · exact wordMatchingFrame_composite G F cF hcF word q n
      point a ha beta hgroup hco hn s j hj P f
  · exact CharacterLine.characterFrameEvaluation_congr G (G.positiveRootCharacter ^ n)
      P (Category.assoc (f.left ≫ (cF.ι.app (op s)).left) q (bsdhMap G word))
      (f ≫ chartLift G F point a s j hj)
      (refined_quotient f.left (chartLift G F point a s j hj).left (flagQuotient G)
        (cF.ι.app (op s)).left q (bsdhMap G word)
        (lift_quotient G F cF word q point a ha s j hj))

end SchubertGeometry.RetainedCharacter
