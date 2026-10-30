import OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.WordChartPreimage
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Coefficients of matching sections on opposition-chart preimages -/

set_option autoImplicit false

noncomputable section
universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Modules
open ReductiveGroups GroupActions FrobeniusSplitting
open FrobeniusSplitting.RetainedCharacter MonoidalCategory
open scoped CategoryTheory.MonObj

namespace SchubertGeometry.RetainedCharacter

open private SchubertGeometry.CharacterLine.pullSection from
  OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.PullbackFrames
open private singletonIndex singletonArrow from
  OrbitComplexity.FrobeniusSplitting.Modules.MatchingModule
open private chartLift from
  OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.WordMatchingBase
open private SchubertGeometry.DeterminantSection.chartAlgebra from
  OrbitComplexity.SchubertGeometry.Frobenius.Determinant.OppositionPolynomial
open private inducedFrame_section left_associate pulled_coefficient preimageFrame_value
  over_appTop_value preimageSnd preimageFst polynomialSection preimageLift
  preimageLift_equation from
  OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.WordChartPreimage

variable {K : Type u} [hK : Field K] [hAlg : IsAlgClosed K] [hChar : CharZero K]
    (G : ReductiveGroupData K)

variable {J : Type u}
    (F : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} K)
    [hFopen : ∀ {s t} (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (F.map f).hom.toRingHom))]
    [hFdir : ((F.op ⋙ algSpec (.of K) ⋙ Over.forget (Spec (.of K))) ⋙
      Scheme.forget).IsLocallyDirected]
    (cF : Cocone (F.op ⋙ algSpec (.of K))) (hcF : IsColimit cF)
    (word : List G.rootBase.support) (q : cF.pt.left ⟶ bsdhScheme G word)
    (point : J → G.points)
    (a : ∀ j, (algSpec (.of K)).obj (op (F.obj (singletonIndex j))) ⟶
      (oppositeUnipotentVariety G).toOver)
    (ha : ∀ j, (a j).left ≫ (flagChartMorphism G (point j)).left =
      (cF.ι.app (op (singletonIndex j))).left ≫ (q ≫ bsdhMap G word))
    (beta : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val)
      (k : J) (_ : k ∈ s.val),
      (algSpec (.of K)).obj (op (F.obj s)) ⟶ (borelVariety G).toOver)
    (hgroup : ∀ s j hj k hk, @chartLift.{u} K hK hAlg hChar G J F point a s j hj =
      @chartLift.{u} K hK hAlg hChar G J F point a s k hk * (beta s j hj k hk ≫ borelInclusion G))
    (hco : ∀ s j hj k hk l hl, @wordTransitionUnit.{u} K hK hAlg hChar G J F beta s j hj l hl =
      @wordTransitionUnit.{u} K hK hAlg hChar G J F beta s k hk l hl * @wordTransitionUnit.{u} K hK
        hAlg hChar G J F beta s j hj k hk)
    (hn : ∀ s t (f : s ⟶ t) j hj k hk,
      Units.map (F.map f).hom.toMonoidHom (@wordTransitionUnit.{u} K hK hAlg hChar G J F beta s j hj
        k hk) =
        @wordTransitionUnit.{u} K hK hAlg hChar G J F beta t j ((leOfHom f) hj) k ((leOfHom f) hk))
    {R : Type u} [hR : CommRing R]
    (N : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} R)
    [hNopen : ∀ {s t} (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (N.map f).hom.toRingHom))]
    [hNdir : ((N.op ⋙ algSpec (.of R) ⋙ Over.forget (Spec (.of R))) ⋙
      Scheme.forget).IsLocallyDirected]
    (v : N ⋙ forget₂ (CommAlgCat R) CommRingCat ⟶
      F ⋙ forget₂ (CommAlgCat K) CommRingCat)
    (deltaN : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val)
      (k : J) (_ : k ∈ s.val), (N.obj s)ˣ)
    (hd : ∀ s j hj k hk, (v.app s).hom (deltaN s j hj k hk : N.obj s) =
      (@wordTransitionUnit.{u} K hK hAlg hChar G J F beta s j hj k hk : F.obj s))
    (cN : Cocone (N.op ⋙ algSpec (.of R))) (hcN : IsColimit cN)
    (qN : cF.pt.left ⟶ cN.pt.left)
    (hqN : ∀ s, Spec.map (v.app s) ≫ (cN.ι.app (op s)).left =
      (cF.ι.app (op s)).left ≫ qN)
    (hcoN : ∀ s j hj k hk l hl,
      deltaN s j hj l hl = deltaN s k hk l hl * deltaN s j hj k hk)
    (hnN : ∀ s t (f : s ⟶ t) j hj k hk,
      Units.map (N.map f).hom.toMonoidHom (deltaN s j hj k hk) =
        deltaN t j ((leOfHom f) hj) k ((leOfHom f) hk))

/-- On the chart inverse image, the matching section has the opposition polynomial coefficient. -/
theorem wordChartPreimage_section
    (hv : ∀ s, Function.Injective (v.app s).hom)
    (P : ∀ s : {s : Finset J // s.Nonempty}, Polynomial (N.obj s))
    (hP : ∀ j, (v.app (singletonIndex j)).hom ((P (singletonIndex j)).coeff 2) =
      @wordRingCoefficient.{u} K hK hAlg hChar G J F point a j)
    (hr : ∀ (s : {s : Finset J // s.Nonempty}) j (hj : j ∈ s.val) k (hk : k ∈ s.val),
      (N.map (singletonArrow s j hj)).hom ((P (singletonIndex j)).coeff 2) =
        (N.map (singletonArrow s k hk)).hom ((P (singletonIndex k)).coeff 2) *
          (deltaN s j hj k hk : N.obj s))
    (i : G.rootBase.support) (n : ℕ) :
    SchubertGeometry.CharacterLine.pullSection (preimageSnd G word q i)
        ((Scheme.Modules.pullback qN).obj (matchingModule N cN deltaN n))
        (SchubertGeometry.CharacterLine.pullSection qN (matchingModule N cN deltaN n)
          (@coefficientMatchingSection.{u} R J hR N cN deltaN
            (fun j => (P (singletonIndex j)).coeff 2) hr n)) ≫
        (@wordChartPreimageFrame.{u} K hK hAlg hChar G J F hFopen hFdir cF hcF
          word q point a ha beta hgroup hco hn R hR N hNopen hNdir
          v deltaN hd cN hcN qN hqN hcoN hnN i n).hom =
      globalSectionsSmul
        (SheafOfModules.unit (wordChartPreimage G word q i).ringCatSheaf)
        ((preimageFst G word q i).appTop
          (polynomialSection G i n)) := by
  have hsection :
      @coefficientMatchingSection.{u} R J hR N cN deltaN
        (fun j => (P (singletonIndex j)).coeff 2) hr n =
      @retainedWordSection.{u} K hK hAlg hChar G J F hFopen hFdir cF hcF
        word q point a ha beta hgroup hco hn R hR N v hv deltaN hd P hP cN n := rfl
  have hs : SchubertGeometry.CharacterLine.pullSection qN (matchingModule N cN deltaN n)
      (@retainedWordSection.{u} K hK hAlg hChar G J F hFopen hFdir cF hcF
        word q point a ha beta hgroup hco hn R hR N v hv deltaN hd P hP cN n) ≫
          (@retainedWordLineIso.{u} K hK hAlg hChar G J F hFopen hFdir cF hcF word q point a ha beta
          hgroup hco hn R hR N hNopen hNdir v deltaN hd cN hcN qN hqN hcoN hnN n).hom =
      SchubertGeometry.CharacterLine.pullSection q (@CharacterLine.wordCharacterModule.{u} K hK hAlg
        hChar G (G.positiveRootCharacter ^ n) word)
        (@CharacterLine.wordDeterminantModuleSection.{u} K hK hAlg hChar G n word) := by
      have hdet :=
        @retainedWordLineIso_section.{u} K hK hAlg hChar G J F hFopen hFdir cF hcF word q
          point a ha beta hgroup hco hn R hR N hNopen hNdir v deltaN hd cN hcN qN hqN
          hcoN hnN hv P hP n
      exact left_associate (pullbackObjUnitIso qN).inv
        ((Scheme.Modules.pullback qN).map
          (@retainedWordSection.{u} K hK hAlg hChar G J F hFopen hFdir cF hcF
            word q point a ha beta hgroup hco hn R hR N v hv deltaN hd P hP cN n))
              (@retainedWordLineIso.{u} K hK hAlg hChar G J F hFopen hFdir cF hcF word q point a ha
              beta hgroup hco hn R hR N hNopen hNdir v deltaN hd cN hcN qN hqN hcoN hnN n).hom
        (SchubertGeometry.CharacterLine.pullSection q (@CharacterLine.wordCharacterModule.{u} K hK
          hAlg hChar G (G.positiveRootCharacter ^ n) word)
          (@CharacterLine.wordDeterminantModuleSection.{u} K hK hAlg hChar G n word)) hdet
  have hpoly : ((DeterminantSection.oppositionPolynomialIso G i).hom.left ≫ (flagChartMap G
    (DeterminantSection.oppositionChartPoint G i)).left).appTop
      (DeterminantSection.positiveDetPowerFunction G n) =
      polynomialSection G i n := by
    have hpoly0 :=
      @DeterminantSection.oppositionPolynomialIso_function K hK hAlg hChar G i n
    exact @over_appTop_value (Spec (.of K))
      (affineVariety K
        (Polynomial (SchubertGeometry.DeterminantSection.chartAlgebra G i))).toOver
      (oppositeUnipotentVariety G).toOver (reductiveVariety G).toOver
      (DeterminantSection.oppositionPolynomialIso G i).hom
      (flagChartMap G (DeterminantSection.oppositionChartPoint G i))
      (DeterminantSection.oppositionPolynomialIso G i).hom.left rfl
      (DeterminantSection.positiveDetPowerFunction G n) (polynomialSection G i n) hpoly0
  have hv0 := pulled_coefficient (preimageFst G word q i)
    (DeterminantSection.oppositionPolynomialIso G i).hom.left (flagChartMap G
      (DeterminantSection.oppositionChartPoint G i)).left
    (DeterminantSection.positiveDetPowerFunction G n)
    (polynomialSection G i n) hpoly
  have hE := @preimageFrame_value.{u} K hK hAlg hChar G cF.pt.left word q i n
    ((preimageFst G word q i).appTop (polynomialSection G i n)) hv0
  have hvalue := @inducedFrame_section.{u} (wordChartPreimage G word q i) cF.pt.left
    (bsdhScheme G word) (preimageSnd G word q i) q ((Scheme.Modules.pullback qN).obj (matchingModule
      N cN deltaN n)) (@CharacterLine.wordCharacterModule.{u} K hK hAlg hChar G
      (G.positiveRootCharacter ^ n) word) (@retainedWordLineIso.{u} K hK hAlg hChar G J F hFopen
      hFdir cF hcF word q point a ha beta hgroup hco hn R hR N hNopen hNdir v deltaN hd cN hcN qN
      hqN hcoN hnN n) (@CharacterLine.wordCharacterFrameIso.{u} K hK hAlg hChar G word
      (G.positiveRootCharacter ^ n) (wordChartPreimage G word q i) (preimageSnd G word q i ≫ q)
      (DeterminantSection.oppositionChartPoint G i) (preimageLift G word q i) (preimageLift_equation
      G word q i))
    (SchubertGeometry.CharacterLine.pullSection qN (matchingModule N cN deltaN n)
      (@retainedWordSection.{u} K hK hAlg hChar G J F hFopen hFdir cF hcF
        word q point a ha beta hgroup hco hn R hR N v hv deltaN hd P hP cN n))
    (@CharacterLine.wordDeterminantModuleSection.{u} K hK hAlg hChar G n word) hs
    ((preimageFst G word q i).appTop (polynomialSection G i n)) hE
  exact (congrArg
    (fun t : SheafOfModules.unit cN.pt.left.ringCatSheaf ⟶ matchingModule N cN deltaN n =>
      SchubertGeometry.CharacterLine.pullSection (preimageSnd G word q i)
        ((Scheme.Modules.pullback qN).obj (matchingModule N cN deltaN n))
        (SchubertGeometry.CharacterLine.pullSection qN (matchingModule N cN deltaN n) t) ≫
      (@wordChartPreimageFrame.{u} K hK hAlg hChar G J F hFopen hFdir cF hcF
        word q point a ha beta hgroup hco hn R hR N hNopen hNdir
        v deltaN hd cN hcN qN hqN hcoN hnN i n).hom)
    hsection).trans hvalue



end SchubertGeometry.RetainedCharacter
