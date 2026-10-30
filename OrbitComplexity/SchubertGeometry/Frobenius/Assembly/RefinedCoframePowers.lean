import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.RefinedMatchingEvaluation
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-!+# Character coframes on common chart refinements

The polynomial append coframe and the matching coframe are compared on the
same pullback of the original character module. Their quotient in degree
`n` is the `n`th power of their quotient in degree one.
-/

noncomputable section
universe u v w

open AlgebraicGeometry CategoryTheory Opposite
open CategoryTheory.Limits (Cocone IsColimit)
open AlgebraicGeometry.Scheme.Modules
open ReductiveGroups GroupActions FrobeniusSplitting
open FrobeniusSplitting.CharacterLine FrobeniusSplitting.RetainedCharacter
open CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj

namespace SchubertGeometry.RetainedCharacter

open private comparisonCoframe from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendCoframeComparison
open private comparisonResult comparison_export endpoint_pullback from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendPowerFrames
open private flagComparison comparisonTail_cancel from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.CoframeEvaluations
open private polynomialBase from
  OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.AppendCoordinates
open private appendPolynomialLift appendPolynomialLift_endpoint from
  OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.AppendCoframes
open private singletonIndex singletonArrow from
  OrbitComplexity.FrobeniusSplitting.Modules.MatchingModule
open private chartLift lift_quotient from
  OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.WordMatchingBase
open private frame_on_composite from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.RefinedAppendUnits
open private refined_quotient from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.RefinedMatchingEvaluation

private theorem comparison_flat
    {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K) (χ : G.characters) {X Y : Scheme.{u}}
    {P Q : Over (Spec (.of K))} (f : P ⟶ Q)
    {j : P.left ⟶ X} {q : X ⟶ Y} {r : Q.left ⟶ Y}
    (h : j ≫ q = f.left ≫ r) (M : X.Modules)
    (z : Y ⟶ (flagVariety G).scheme)
    (W : (pullback q).obj ((pullback z).obj (CharacterLine.flagCharacterModule G χ)) ≅ M)
    (E : (pullback r).obj ((pullback z).obj (CharacterLine.flagCharacterModule G χ)) ≅
      SheafOfModules.unit Q.left.ringCatSheaf)
    (a : Q ⟶ (reductiveVariety G).toOver)
    (ha : a.left ≫ flagQuotient G = r ≫ z)
    (hc : comparisonResult G χ f h h W.symm E z rfl a ha)
    (D : (pullback ((j ≫ q) ≫ z)).obj (CharacterLine.flagCharacterModule G χ) ≅
      (pullback j).obj M)
    (hD : D = flagComparison j q z (CharacterLine.flagCharacterModule G χ) M W)
    (A : (pullback j).obj M ≅ SheafOfModules.unit P.left.ringCatSheaf)
    (hA : A = comparisonCoframe j q f.left r h M
      ((pullback z).obj (CharacterLine.flagCharacterModule G χ)) W.symm E)
    (b : P ⟶ (reductiveVariety G).toOver) (hb : b = f ≫ a)
    (hquot : b.left ≫ flagQuotient G = (j ≫ q) ≫ z) :
    D.hom ≫ A.hom = CharacterLine.characterFrameEvaluation G χ P ((j ≫ q) ≫ z) b hquot := by
  subst D
  apply comparisonTail_cancel j q z (CharacterLine.flagCharacterModule G χ) M W A
  exact comparison_export hc W.symm rfl A hA b hb hquot

private theorem refine_lift {C : Type v} [Category.{w} C] {P Q A B H : C}
    (f : P ⟶ Q) (t : Q ⟶ A) (a : A ⟶ B) (z : B ⟶ H)
    (l : Q ⟶ H) (hl : l = t ≫ a ≫ z) :
    f ≫ l = (f ≫ t ≫ a) ≫ z := by
  rw [hl, Category.assoc, Category.assoc]

private theorem coframe_evaluation_transfer {C : Type v} [Category.{w} C]
    {L M U : C} (D₀ D : L ≅ M) (E₀ E : M ≅ U) (e₀ e : L ⟶ U)
    (h₀ : D₀.hom ≫ E₀.hom = e₀)
    (hD : D₀ = D) (hE : E₀ = E) (he : e₀ = e) : D.hom ≫ E.hom = e := by
  subst D
  subst E
  subst e
  exact h₀

private theorem over_quotient_eq {B : Scheme.{u}} {P Q H Z : Over B}
    (a : P ⟶ Q) (c : Q ⟶ H) (π : H ⟶ Z) (d : Q ⟶ Z)
    (hd : c ≫ π = d) (l k : P ⟶ H) (hl : l = a ≫ c)
    (m : P.left ⟶ Z.left)
    (hlq : l.left ≫ π.left = m) (hkq : k.left ≫ π.left = m) :
    a ≫ d = k ≫ π := by
  rw [← hd, ← Category.assoc, ← hl]
  exact (Over.forget B).map_injective (hlq.trans hkq.symm)

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K)

section Append

variable (word : List G.rootBase.support) (i : G.rootBase.support)
    (V : Over (Spec (.of K))) (g : G.points)
    (a : V ⟶ (oppositeUnipotentVariety G).toOver)
    (c : V ⊗ (schubertVariety G
      (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver ⟶
        Over.mk (bsdhToSpec G (word ++ [i])))
    (hend : c.left ≫ (bsdhAppendIso G word i).hom.left ≫
      CategoryTheory.Limits.pullback.snd (bsdhMap G word) (flagBundleProjection G
        (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val))) =
      (a ⊗ₘ 𝟙 (schubertVariety G
        (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver).left ≫
          flagBundleChart G _ g)
    (B : CommAlgCat.{u} K) (p : (algSpec (.of K)).obj (op B) ⟶ V)

/-- The refined append coframe has the polynomial group-lift evaluation
after the canonical comparison with the flag character module. -/
theorem appendRefinedFlag_eval (n : ℕ) (ε : Fin 2)
    {X : Scheme.{u}} (P : Over (Spec (.of K)))
    (j : P.left ⟶ X) (q : X ⟶ bsdhScheme G (word ++ [i]))
    (f : P ⟶ polynomialBase B)
    (h : j ≫ q = f.left ≫
      (projectiveLinePolynomialChart B ⟨ε⟩ ≫ projectiveAppendChart G i B p c))
    (M : X.Modules)
    (W : (pullback q).obj
      (CharacterLine.wordCharacterModule G (G.positiveRootCharacter ^ n) (word ++ [i])) ≅ M) :
    (flagChartComparison G (word ++ [i]) n j q M W).hom ≫
      (comparisonCoframe j q f.left
        (projectiveLinePolynomialChart B ⟨ε⟩ ≫ projectiveAppendChart G i B p c) h M
        (CharacterLine.wordCharacterModule G (G.positiveRootCharacter ^ n) (word ++ [i]))
        W.symm (appendPolynomialFrame G word i V g a c hend B p n ⟨ε⟩)).hom =
    CharacterLine.characterFrameEvaluation G (G.positiveRootCharacter ^ n) P
      ((j ≫ q) ≫ bsdhMap G (word ++ [i]))
      (f ≫ appendPolynomialLift G i V g a B p ε)
      (endpoint_pullback G P (polynomialBase B) f
        (projectiveLinePolynomialChart B ⟨ε⟩ ≫ projectiveAppendChart G i B p c)
        (bsdhMap G (word ++ [i])) (j ≫ q) h.symm
        (appendPolynomialLift G i V g a B p ε)
        ((appendPolynomialLift_endpoint G word i V g a c hend B p ε).trans
          (Category.assoc (projectiveLinePolynomialChart B ⟨ε⟩)
            (projectiveAppendChart G i B p c) (bsdhMap G (word ++ [i]))).symm)) := by
  have hc := appendRefinedCoframe_eval G word i V g a c hend B p n ε P j q f h M W
  exact comparison_flat G (G.positiveRootCharacter ^ n)
    (Y := bsdhScheme G (word ++ [i])) (P := P) f h M
    (bsdhMap G (word ++ [i])) W
    (appendPolynomialFrame G word i V g a c hend B p n ⟨ε⟩)
    (appendPolynomialLift G i V g a B p ε)
    ((appendPolynomialLift_endpoint G word i V g a c hend B p ε).trans
      (Category.assoc (projectiveLinePolynomialChart B ⟨ε⟩)
        (projectiveAppendChart G i B p c) (bsdhMap G (word ++ [i]))).symm)
    hc (flagChartComparison G (word ++ [i]) n j q M W) rfl
    (comparisonCoframe j q f.left
      (projectiveLinePolynomialChart B ⟨ε⟩ ≫ projectiveAppendChart G i B p c) h M
      (CharacterLine.wordCharacterModule G (G.positiveRootCharacter ^ n) (word ++ [i]))
      W.symm (appendPolynomialFrame G word i V g a c hend B p n ⟨ε⟩)) rfl
    (f ≫ appendPolynomialLift G i V g a B p ε) rfl _

end Append

section Matching

variable {J : Type u}
    (F : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} K)
    [∀ {s t} (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (F.map f).hom.toRingHom))]
    [((F.op ⋙ algSpec (.of K) ⋙ Over.forget (Spec (.of K))) ⋙
      Scheme.forget).IsLocallyDirected]
    (cF : Cocone (F.op ⋙ algSpec (.of K))) (hcF : IsColimit cF)
    (word : List G.rootBase.support) (i : G.rootBase.support)
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

/-- On a common refinement, the polynomial append coframe and the original
matching coframe have transition unit equal to the power of its degree-one unit. -/
theorem refinedCoframe_unit_power
    (A : CommAlgCat.{u} K) (s : {s : Finset J // s.Nonempty}) (j : J) (hj : j ∈ s.val)
    (f : (algSpec (.of K)).obj (op A) ⟶ (algSpec (.of K)).obj (op (F.obj s)))
    (V : Over (Spec (.of K))) (g : G.points)
    (b : V ⟶ (oppositeUnipotentVariety G).toOver)
    (c : V ⊗ (schubertVariety G
      (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver ⟶
        Over.mk (bsdhToSpec G (word ++ [i])))
    (hend : c.left ≫ (bsdhAppendIso G word i).hom.left ≫
      CategoryTheory.Limits.pullback.snd (bsdhMap G word) (flagBundleProjection G
        (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val))) =
      (b ⊗ₘ 𝟙 (schubertVariety G
        (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver).left ≫
          flagBundleChart G _ g)
    (B : CommAlgCat.{u} K) (p : (algSpec (.of K)).obj (op B) ⟶ V) (ε : Fin 2)
    (k : (algSpec (.of K)).obj (op A) ⟶ polynomialBase B)
    (h : (f.left ≫ (cF.ι.app (op s)).left) ≫ q = k.left ≫
      (projectiveLinePolynomialChart B ⟨ε⟩ ≫ projectiveAppendChart G i B p c)) :
    let E := fun n : ℕ => frame_on_composite f.left (cF.ι.app (op s)).left
      (f.left ≫ (cF.ι.app (op s)).left) rfl
      (matchingModule F cF (wordTransitionUnit G F beta) n)
      (localCharacterTrivialization F cF hcF (wordTransitionUnit G F beta) n hco hn s j hj)
    let H := fun n : ℕ => comparisonCoframe (f.left ≫ (cF.ι.app (op s)).left) q k.left
      (projectiveLinePolynomialChart B ⟨ε⟩ ≫ projectiveAppendChart G i B p c) h
      (matchingModule F cF (wordTransitionUnit G F beta) n)
      (CharacterLine.wordCharacterModule G (G.positiveRootCharacter ^ n) (word ++ [i]))
      (wordCharacterMatchingIso G F cF hcF (word ++ [i]) q n
        point a ha beta hgroup hco hn).symm
      (appendPolynomialFrame G word i V g b c hend B p n ⟨ε⟩)
    ∀ n : ℕ, affineCoframeUnit A (E n) (H n) = (affineCoframeUnit A (E 1) (H 1)) ^ n := by
  intro E H n
  let J₀ : Spec (.of A) ⟶ cF.pt.left := f.left ≫ (cF.ι.app (op s)).left
  let m : Spec (.of A) ⟶ (flagVariety G).scheme := (J₀ ≫ q) ≫ bsdhMap G (word ++ [i])
  let l : (algSpec (.of K)).obj (op A) ⟶ (reductiveVariety G).toOver :=
    f ≫ chartLift G F point a s j hj
  let a₀ : (algSpec (.of K)).obj (op A) ⟶ (oppositeUnipotentVariety G).toOver :=
    f ≫ (algSpec (.of K)).map (F.map (singletonArrow s j hj)).op ≫ a j
  have hl : l = a₀ ≫ flagChartMap G (point j) :=
    refine_lift f ((algSpec (.of K)).map (F.map (singletonArrow s j hj)).op)
      (a j) (flagChartMap G (point j)) (chartLift G F point a s j hj) rfl
  have hlq : l.left ≫ flagQuotient G = m :=
    refined_quotient f.left (chartLift G F point a s j hj).left (flagQuotient G)
      (cF.ι.app (op s)).left q (bsdhMap G (word ++ [i]))
      (lift_quotient G F cF (word ++ [i]) q point a ha s j hj)
  let k₀ : (algSpec (.of K)).obj (op A) ⟶ (reductiveVariety G).toOver :=
    k ≫ appendPolynomialLift G i V g b B p ε
  have hkq : k₀.left ≫ flagQuotient G = m :=
    endpoint_pullback G ((algSpec (.of K)).obj (op A)) (polynomialBase B) k
      (projectiveLinePolynomialChart B ⟨ε⟩ ≫ projectiveAppendChart G i B p c)
      (bsdhMap G (word ++ [i])) (J₀ ≫ q) h.symm
      (appendPolynomialLift G i V g b B p ε)
      ((appendPolynomialLift_endpoint G word i V g b c hend B p ε).trans
        (Category.assoc (projectiveLinePolynomialChart B ⟨ε⟩)
          (projectiveAppendChart G i B p c) (bsdhMap G (word ++ [i]))).symm)
  have hflag : a₀ ≫ flagChartMorphism G (point j) = k₀ ≫ flagQuotientMorphism G :=
    over_quotient_eq a₀ (flagChartMap G (point j)) (flagQuotientMorphism G)
      (flagChartMorphism G (point j)) (flagChartMap_quotient G (point j))
      l k₀ hl m hlq hkq
  let M : ℕ → (Spec (.of A)).Modules := fun r =>
    (pullback J₀).obj (matchingModule F cF (wordTransitionUnit G F beta) r)
  let D : ∀ r, (pullback m).obj
      (CharacterLine.flagCharacterModule G (G.positiveRootCharacter ^ r)) ≅ M r :=
    fun r => flagChartComparison G (word ++ [i]) r J₀ q
      (matchingModule F cF (wordTransitionUnit G F beta) r)
      (wordCharacterMatchingIso G F cF hcF (word ++ [i]) q r
        point a ha beta hgroup hco hn)
  have hE₀ (r : ℕ) := matchingRefinedCoframe_eval G F cF hcF (word ++ [i]) q r
    point a ha beta hgroup hco hn s j hj ((algSpec (.of K)).obj (op A)) f
  have hE : ∀ r, (D r).hom ≫ (E r).hom =
      CharacterLine.characterFrameEvaluation G (G.positiveRootCharacter ^ r)
        ((algSpec (.of K)).obj (op A)) m l hlq := by
    intro r
    exact coframe_evaluation_transfer
      (flagChartComparison G (word ++ [i]) r (f.left ≫ (cF.ι.app (op s)).left) q
        (matchingModule F cF (wordTransitionUnit G F beta) r)
        (wordCharacterMatchingIso G F cF hcF (word ++ [i]) q r
          point a ha beta hgroup hco hn)) (D r)
      (frame_on_composite f.left (cF.ι.app (op s)).left
        (f.left ≫ (cF.ι.app (op s)).left) rfl
        (matchingModule F cF (wordTransitionUnit G F beta) r)
        (localCharacterTrivialization F cF hcF (wordTransitionUnit G F beta)
          r hco hn s j hj)) (E r) _ _ (hE₀ r) rfl rfl rfl
  have hH₀ (r : ℕ) := appendRefinedFlag_eval G word i V g b c hend B p r ε
    ((algSpec (.of K)).obj (op A)) (f.left ≫ (cF.ι.app (op s)).left) q k h
    (matchingModule F cF (wordTransitionUnit G F beta) r)
    (wordCharacterMatchingIso G F cF hcF (word ++ [i]) q r
      point a ha beta hgroup hco hn)
  have hH : ∀ r, (D r).hom ≫ (H r).hom =
      CharacterLine.characterFrameEvaluation G (G.positiveRootCharacter ^ r)
        ((algSpec (.of K)).obj (op A)) m k₀ hkq := by
    intro r
    exact coframe_evaluation_transfer
      (flagChartComparison G (word ++ [i]) r (f.left ≫ (cF.ι.app (op s)).left) q
        (matchingModule F cF (wordTransitionUnit G F beta) r)
        (wordCharacterMatchingIso G F cF hcF (word ++ [i]) q r
          point a ha beta hgroup hco hn)) (D r)
      (comparisonCoframe (f.left ≫ (cF.ι.app (op s)).left) q k.left
        (projectiveLinePolynomialChart B ⟨ε⟩ ≫ projectiveAppendChart G i B p c) h
        (matchingModule F cF (wordTransitionUnit G F beta) r)
        (CharacterLine.wordCharacterModule G (G.positiveRootCharacter ^ r) (word ++ [i]))
        (wordCharacterMatchingIso G F cF hcF (word ++ [i]) q r
          point a ha beta hgroup hco hn).symm
        (appendPolynomialFrame G word i V g b c hend B p r ⟨ε⟩)) (H r)
      _ _ (hH₀ r) rfl rfl rfl
  exact CharacterLine.characterCoframe_unit_power G A (point j) a₀ k₀ hflag m hkq
    l hl hlq M D E H hE hH n

end Matching

end SchubertGeometry.RetainedCharacter
