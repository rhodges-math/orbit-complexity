import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.RetainedCoframePowers
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.RefinedFrameSquares
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Powers of scalar square-coframe ratios

The matching-line scalar square identifies the pulled canonical matching
coframe with the arithmetic refinement coframe. Its ratio with the append
coframe therefore satisfies the same character-power identity.
-/

set_option autoImplicit false
noncomputable section
universe u

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
open private polynomialBase from
  OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.AppendCoordinates
open private singletonIndex from OrbitComplexity.FrobeniusSplitting.Modules.MatchingModule
open private chartLift from
  OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.WordMatchingBase
open private frame_on_composite from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.RefinedAppendUnits

private theorem power_transport {M : Type*} [Monoid M] {D : ℕ → Type*}
    (E F : ∀ n, D n) (c : ∀ n, D n → M) (hEF : ∀ n, E n = F n)
    (hp : ∀ n, c n (E n) = (c 1 (E 1)) ^ n) :
    ∀ n, c n (F n) = (c 1 (F 1)) ^ n := by
  intro n
  calc
    c n (F n) = c n (E n) := congrArg (c n) (hEF n).symm
    _ = (c 1 (E 1)) ^ n := hp n
    _ = (c 1 (F 1)) ^ n := congrArg (fun x : M => x ^ n) (congrArg (c 1) (hEF 1))

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K) {J : Type u}
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
    {R : Type u} [CommRing R]
    (N : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} R)
    [∀ {s t} (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (N.map f).hom.toRingHom))]
    [((N.op ⋙ algSpec (.of R) ⋙ Over.forget (Spec (.of R))) ⋙
      Scheme.forget).IsLocallyDirected]
    (v : N ⋙ forget₂ (CommAlgCat R) CommRingCat ⟶
      F ⋙ forget₂ (CommAlgCat K) CommRingCat)
    (deltaN : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val)
      (k : J) (_ : k ∈ s.val), (N.obj s)ˣ)
    (hd : ∀ s j hj k hk, (v.app s).hom (deltaN s j hj k hk : N.obj s) =
      (wordTransitionUnit G F beta s j hj k hk : F.obj s))
    (cN : Cocone (N.op ⋙ algSpec (.of R))) (hcN : IsColimit cN)
    (qN : cF.pt.left ⟶ cN.pt.left)
    (hqN : ∀ s, Spec.map (v.app s) ≫ (cN.ι.app (op s)).left =
      (cF.ι.app (op s)).left ≫ qN)
    (hcoN : ∀ s j hj k hk l hl,
      deltaN s j hj l hl = deltaN s k hk l hl * deltaN s j hj k hk)
    (hnN : ∀ s t (f : s ⟶ t) j hj k hk,
      Units.map (N.map f).hom.toMonoidHom (deltaN s j hj k hk) =
        deltaN t j ((leOfHom f) hj) k ((leOfHom f) hk))

/-- The ratio of the arithmetic scalar-square coframe and the append coframe
is the corresponding power of its degree-one ratio, under the canonical
matching-line comparison on the same two refined charts. -/
theorem squareCoframe_unit_power
    (A : CommAlgCat.{u} K) (j : J)
    (f : (algSpec (.of K)).obj (op A) ⟶
      (algSpec (.of K)).obj (op (F.obj (singletonIndex j))))
    (P : Scheme.{u}) (t : P ⟶ Spec (.of (N.obj (singletonIndex j))))
    (u : Spec (.of A) ⟶ P)
    (hs : u ≫ t = f.left ≫ Spec.map (v.app (singletonIndex j)))
    (htotal : u ≫ (t ≫ (cN.ι.app (op (singletonIndex j))).left) =
      (f.left ≫ (cF.ι.app (op (singletonIndex j))).left) ≫ qN)
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
    (h : (f.left ≫ (cF.ι.app (op (singletonIndex j))).left) ≫ q = k.left ≫
      (projectiveLinePolynomialChart B ⟨ε⟩ ≫ projectiveAppendChart G i B p c)) :
    let E := fun n : ℕ => squareFrameIso qN
      (f.left ≫ (cF.ι.app (op (singletonIndex j))).left)
      (t ≫ (cN.ι.app (op (singletonIndex j))).left) u htotal
      (matchingModule N cN deltaN n)
      (frame_on_composite t (cN.ι.app (op (singletonIndex j))).left
        (t ≫ (cN.ι.app (op (singletonIndex j))).left) rfl (matchingModule N cN deltaN n)
        (localCharacterTrivialization N cN hcN deltaN n hcoN hnN
          (singletonIndex j) j (Finset.mem_singleton_self j)))
    let H := fun n : ℕ => comparisonCoframe
      (f.left ≫ (cF.ι.app (op (singletonIndex j))).left) q k.left
      (projectiveLinePolynomialChart B ⟨ε⟩ ≫ projectiveAppendChart G i B p c) h
      ((pullback qN).obj (matchingModule N cN deltaN n))
      (CharacterLine.wordCharacterModule G (G.positiveRootCharacter ^ n) (word ++ [i]))
      (retainedWordLineIso G F cF hcF (word ++ [i]) q point a ha beta hgroup hco hn
        N v deltaN hd cN hcN qN hqN hcoN hnN n)
      (appendPolynomialFrame G word i V g b c hend B p n ⟨ε⟩)
    ∀ n : ℕ, affineCoframeUnit A (E n) (H n) = (affineCoframeUnit A (E 1) (H 1)) ^ n := by
  let T := fun n : ℕ => matchingPullbackIso N F cN hcN cF hcF v qN hqN
    deltaN (wordTransitionUnit G F beta) hd n hcoN hnN hco hn
  let Ecan := fun n : ℕ =>
    (pullback (f.left ≫ (cF.ι.app (op (singletonIndex j))).left)).mapIso (T n) ≪≫
      frame_on_composite f.left (cF.ι.app (op (singletonIndex j))).left
        (f.left ≫ (cF.ι.app (op (singletonIndex j))).left) rfl
        (matchingModule F cF (wordTransitionUnit G F beta) n)
        (localCharacterTrivialization F cF hcF (wordTransitionUnit G F beta)
          n hco hn (singletonIndex j) j (Finset.mem_singleton_self j))
  let Esq := fun n : ℕ => squareFrameIso qN
    (f.left ≫ (cF.ι.app (op (singletonIndex j))).left)
    (t ≫ (cN.ι.app (op (singletonIndex j))).left) u htotal
    (matchingModule N cN deltaN n)
    (frame_on_composite t (cN.ι.app (op (singletonIndex j))).left
      (t ≫ (cN.ι.app (op (singletonIndex j))).left) rfl (matchingModule N cN deltaN n)
      (localCharacterTrivialization N cN hcN deltaN n hcoN hnN
        (singletonIndex j) j (Finset.mem_singleton_self j)))
  let H := fun n : ℕ => comparisonCoframe
    (f.left ≫ (cF.ι.app (op (singletonIndex j))).left) q k.left
    (projectiveLinePolynomialChart B ⟨ε⟩ ≫ projectiveAppendChart G i B p c) h
    ((pullback qN).obj (matchingModule N cN deltaN n))
    (CharacterLine.wordCharacterModule G (G.positiveRootCharacter ^ n) (word ++ [i]))
    (retainedWordLineIso G F cF hcF (word ++ [i]) q point a ha beta hgroup hco hn
      N v deltaN hd cN hcN qN hqN hcoN hnN n)
    (appendPolynomialFrame G word i V g b c hend B p n ⟨ε⟩)
  have hp := retainedCoframe_unit_power G F cF hcF word i q point a ha beta hgroup hco hn
    N v deltaN hd cN hcN qN hqN hcoN hnN A (singletonIndex j) j
    (Finset.mem_singleton_self j) f V g b c hend B p ε k h
  have he : ∀ n : ℕ, Ecan n = Esq n := fun n =>
    refinedUnitFrame_scalar N F cN hcN cF hcF v qN hqN deltaN
      (wordTransitionUnit G F beta) hd n hcoN hnN hco hn j f.left t u hs htotal
  have leaf := power_transport Ecan Esq (fun n E => affineCoframeUnit A E (H n))
  exact leaf he hp

end SchubertGeometry.RetainedCharacter
