import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordPreimageRefinement
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.RefinedMatchingEvaluation
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.CharacterCoframePowers
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.CoframeEvaluations
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.RetainedCoframePowers
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendCoframeAssociativity
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-!
# Coframe ratios over inverse images of flag charts

The matching coframe and the character coframe on a flag-chart inverse image
have comparison units given by powers of their degree-one comparison unit.
-/

set_option autoImplicit false
noncomputable section
universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Modules
open ReductiveGroups GroupActions FrobeniusSplitting
open FrobeniusSplitting.RetainedCharacter
open scoped CategoryTheory.MonObj
open MonoidalCategory

namespace SchubertGeometry.RetainedCharacter

open private SchubertGeometry.CharacterLine.U from
  OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.PullbackFrames
open private SchubertGeometry.CharacterLine.frameQuotient from
  OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.FrameComposition
open private inducedFrame preimageSnd preimageFst preimageLift preimageLift_equation
  schemeTarget schemeSource
  from OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.WordChartPreimage
open private coframeEvaluationResult from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.CoframeEvaluations
open private endpoint_pullback from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendPowerFrames
open private comparisonCoframe from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendCoframeComparison
open private frame_on_composite from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.RefinedAppendUnits
open private three_pullback_coframe from
  OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.CoframeTransport
open private coframeUnit_transport comparisonCoframe_change from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.RetainedCoframePowers
open private singletonIndex singletonArrow from OrbitComplexity.FrobeniusSplitting.Modules.MatchingModule
open private refined_quotient from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.RefinedMatchingEvaluation
open private chartLift lift_quotient from
  OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.WordMatchingBase

private theorem inducedFrame_composite {P X Y Z : Scheme.{u}}
    (t : P ⟶ X) (k : X ⟶ Y) (q : Y ⟶ Z)
    (j : P ⟶ Y) (h : j = t ≫ k)
    (L : Y.Modules) (M : Z.Modules) (e : L ≅ (Scheme.Modules.pullback q).obj M)
    (E : (Scheme.Modules.pullback (k ≫ q)).obj M ≅ SheafOfModules.unit X.ringCatSheaf) :
    frame_on_composite t k j h L (inducedFrame k q L M e E) =
      comparisonCoframe j q t (k ≫ q)
        ((congrArg (fun a => a ≫ q) h).trans (Category.assoc t k q)) L M e E := by
  subst j
  apply Iso.ext
  have hn := ((pullbackComp t k).inv.naturality e.hom).symm
  have hp := three_pullback_coframe t k q M
    ((pullbackComp t (k ≫ q)).inv.app M ≫
      (Scheme.Modules.pullback t).map E.hom ≫ (pullbackObjUnitIso t).hom)
  simp only [Iso.hom_inv_id_app_assoc] at hp
  change (𝟙 ((Scheme.Modules.pullback (t ≫ k)).obj L)) ≫
      (pullbackComp t k).inv.app L ≫
      (Scheme.Modules.pullback t).map
        ((Scheme.Modules.pullback k).map e.hom ≫
          (pullbackComp k q).hom.app M ≫ E.hom) ≫
      (pullbackObjUnitIso t).hom =
    (Scheme.Modules.pullback (t ≫ k)).map e.hom ≫
      (pullbackComp (t ≫ k) q).hom.app M ≫
      (pullbackCongr (Category.assoc t k q)).hom.app M ≫
      (pullbackComp t (k ≫ q)).inv.app M ≫
      (Scheme.Modules.pullback t).map E.hom ≫ (pullbackObjUnitIso t).hom
  have hm₁ := (Scheme.Modules.pullback t).map_comp
    ((Scheme.Modules.pullback k).map e.hom)
    ((pullbackComp k q).hom.app M ≫ E.hom)
  have hm₂ := (Scheme.Modules.pullback t).map_comp
    ((pullbackComp k q).hom.app M) E.hom
  have hm := hm₁.trans (congrArg (fun z => ((Scheme.Modules.pullback t).map ((Scheme.Modules.pullback k).map e.hom)) ≫ z) hm₂)
  have hm₃ := congrArg (fun z => ((pullbackComp t k).inv.app L) ≫ z ≫ ((pullbackObjUnitIso t).hom)) hm
  have ha := (congrArg (fun z => ((pullbackComp t k).inv.app L) ≫ z)
      (Category.assoc ((Scheme.Modules.pullback t).map ((Scheme.Modules.pullback k).map e.hom)) (((Scheme.Modules.pullback t).map ((pullbackComp k q).hom.app M)) ≫ ((Scheme.Modules.pullback t).map E.hom)) ((pullbackObjUnitIso t).hom))).trans
    (congrArg (fun z => ((pullbackComp t k).inv.app L) ≫ ((Scheme.Modules.pullback t).map ((Scheme.Modules.pullback k).map e.hom)) ≫ z)
      (Category.assoc ((Scheme.Modules.pullback t).map ((pullbackComp k q).hom.app M)) ((Scheme.Modules.pullback t).map E.hom) ((pullbackObjUnitIso t).hom)))
  have hn₁ := congrArg (fun z => z ≫ ((Scheme.Modules.pullback t).map ((pullbackComp k q).hom.app M)) ≫ ((Scheme.Modules.pullback t).map E.hom) ≫ ((pullbackObjUnitIso t).hom)) hn
  have hn₂ := (Category.assoc ((pullbackComp t k).inv.app L) ((Scheme.Modules.pullback t).map ((Scheme.Modules.pullback k).map e.hom)) (((Scheme.Modules.pullback t).map ((pullbackComp k q).hom.app M)) ≫ ((Scheme.Modules.pullback t).map E.hom) ≫ ((pullbackObjUnitIso t).hom))).symm.trans
    (hn₁.trans (Category.assoc ((Scheme.Modules.pullback (t ≫ k)).map e.hom) ((pullbackComp t k).inv.app ((Scheme.Modules.pullback q).obj M)) (((Scheme.Modules.pullback t).map ((pullbackComp k q).hom.app M)) ≫ ((Scheme.Modules.pullback t).map E.hom) ≫ ((pullbackObjUnitIso t).hom))))
  have hp₁ := congrArg (fun z => ((Scheme.Modules.pullback (t ≫ k)).map e.hom) ≫ z) hp
  exact (Category.id_comp (((pullbackComp t k).inv.app L) ≫ ((Scheme.Modules.pullback t).map ((Scheme.Modules.pullback k).map e.hom ≫ (pullbackComp k q).hom.app M ≫ E.hom)) ≫ ((pullbackObjUnitIso t).hom))).trans
    (hm₃.trans (ha.trans (hn₂.trans hp₁)))

private theorem wordCoframe_evaluation {K : Type u}
    [hK : Field K] [hAlg : IsAlgClosed K] [hChar : CharZero K]
    (G : ReductiveGroupData K) (word : List G.rootBase.support) (n : ℕ)
    {X : Scheme.{u}} (P : Over (Spec (.of K)))
    (Q : Scheme.{u}) (baseQ : Q ⟶ Spec (.of K))
    (j : P.left ⟶ X) (q : X ⟶ bsdhScheme G word)
    (f : P ⟶ Over.mk baseQ) (r : Q ⟶ bsdhScheme G word)
    (h : j ≫ q = f.left ≫ r) (M : X.Modules)
    (W : (Scheme.Modules.pullback q).obj
      (CharacterLine.wordCharacterModule G (G.positiveRootCharacter ^ n) word) ≅ M)
    (g : G.points) (a : Over.mk baseQ ⟶ (oppositeUnipotentVariety G).toOver)
    (hchart : a.left ≫ (flagChartMorphism G g).left = r ≫ bsdhMap G word) :
    (flagChartComparison G word n j q M W).hom ≫
        (comparisonCoframe j q f.left r h M
          (CharacterLine.wordCharacterModule G (G.positiveRootCharacter ^ n) word)
          W.symm (CharacterLine.wordCharacterFrameIso G word
            (G.positiveRootCharacter ^ n) r g a.left hchart)).hom =
      CharacterLine.characterFrameEvaluation G (G.positiveRootCharacter ^ n)
        P ((j ≫ q) ≫ bsdhMap G word) (f ≫ (a ≫ flagChartMap G g))
        (@endpoint_pullback.{u} K hK hAlg hChar G (bsdhScheme G word) P (Over.mk baseQ) f r (bsdhMap G word) (j ≫ q)
          h.symm (a ≫ flagChartMap G g)
          (((Category.assoc a.left (flagChartMap G g).left (flagQuotient G)).trans
            (congrArg (fun t => a.left ≫ t)
              (SchubertGeometry.CharacterLine.frameQuotient G g))).trans hchart)) := by
  have he := @SchubertGeometry.CharacterLine.wordCharacterFrameIso_eval.{u}
    K hK hAlg hChar G word (G.positiveRootCharacter ^ n) (Over.mk baseQ) r g a hchart
  have fact := @characterCoframe_evaluation.{u} K hK hAlg hChar G
    (G.positiveRootCharacter ^ n) X (bsdhScheme G word) P Q baseQ
    j q (bsdhMap G word) f r h
    (CharacterLine.wordCharacterModule G (G.positiveRootCharacter ^ n) word) rfl
    M W (CharacterLine.wordCharacterFrameIso G word
      (G.positiveRootCharacter ^ n) r g a.left hchart) (a ≫ flagChartMap G g)
    (((Category.assoc a.left (flagChartMap G g).left (flagQuotient G)).trans
      (congrArg (fun t => a.left ≫ t)
        (SchubertGeometry.CharacterLine.frameQuotient G g))).trans hchart)
    ((pullbackComp r (bsdhMap G word)).hom.app
      (CharacterLine.flagCharacterModule G (G.positiveRootCharacter ^ n))) HEq.rfl he
  exact fact

private theorem wordCoframe_unit_power {K : Type u}
    [hK : Field K] [hAlg : IsAlgClosed K] [hChar : CharZero K]
    (G : ReductiveGroupData K) (word : List G.rootBase.support)
    (A : CommAlgCat.{u} K) (X Q : Scheme.{u}) (baseQ : Q ⟶ Spec (.of K))
    (j : Spec (.of A) ⟶ X) (q : X ⟶ bsdhScheme G word)
    (t : Spec (.of A) ⟶ Q)
    (ht : t ≫ baseQ = ((algSpec (.of K)).obj (op A)).hom)
    (r : Q ⟶ bsdhScheme G word) (h : j ≫ q = t ≫ r) (M : ℕ → X.Modules)
    (W : ∀ d, (Scheme.Modules.pullback q).obj
      (CharacterLine.wordCharacterModule G (G.positiveRootCharacter ^ d) word) ≅ M d)
    (E : ∀ d, (Scheme.Modules.pullback j).obj (M d) ≅
      SheafOfModules.unit (Spec (.of A)).ringCatSheaf)
    (gNew : G.points) (b : Q ⟶ SchubertGeometry.CharacterLine.U G)
    (hb : b ≫ (oppositeUnipotentVariety G).toOver.hom = baseQ)
    (hchart : b ≫ (flagChartMorphism G gNew).left = r ≫ bsdhMap G word)
    (gOld : G.points) (aOld : ((algSpec (.of K)).obj (op A)) ⟶ (oppositeUnipotentVariety G).toOver)
    (hOld : aOld ≫ flagChartMorphism G gOld = ((@Over.homMk Scheme.{u} Scheme.instCategory (Spec (.of K)) ((algSpec (.of K)).obj (op A)) (Over.mk baseQ) t ht) ≫ ((@Over.homMk Scheme.{u} Scheme.instCategory (Spec (.of K)) (Over.mk baseQ) (oppositeUnipotentVariety G).toOver b hb) ≫ flagChartMap G gNew)) ≫ flagQuotientMorphism G)
    (lOld : ((algSpec (.of K)).obj (op A)) ⟶ (reductiveVariety G).toOver)
    (hlOld : lOld = aOld ≫ flagChartMap G gOld)
    (haOld : lOld.left ≫ flagQuotient G = ((j ≫ q) ≫ bsdhMap G word))
    (hE : ∀ d, (flagChartComparison G word d j q (M d) (W d)).hom ≫ (E d).hom =
      CharacterLine.characterFrameEvaluation G (G.positiveRootCharacter ^ d)
        ((algSpec (.of K)).obj (op A)) ((j ≫ q) ≫ bsdhMap G word) lOld haOld)
    (n : ℕ) :
    affineCoframeUnit A (E n) (comparisonCoframe j q t r h (M n) (CharacterLine.wordCharacterModule G (G.positiveRootCharacter ^ n) word) (W n).symm (CharacterLine.wordCharacterFrameIso G word (G.positiveRootCharacter ^ n) r gNew b hchart)) =
      (affineCoframeUnit A (E 1) (comparisonCoframe j q t r h (M 1) (CharacterLine.wordCharacterModule G (G.positiveRootCharacter ^ 1) word) (W 1).symm (CharacterLine.wordCharacterFrameIso G word (G.positiveRootCharacter ^ 1) r gNew b hchart))) ^ n := by
  have hF := fun d => @wordCoframe_evaluation.{u} K hK hAlg hChar G word d
    X ((algSpec (.of K)).obj (op A)) Q baseQ j q (@Over.homMk Scheme.{u} Scheme.instCategory (Spec (.of K)) ((algSpec (.of K)).obj (op A)) (Over.mk baseQ) t ht) r h (M d) (W d) gNew (@Over.homMk Scheme.{u} Scheme.instCategory (Spec (.of K)) (Over.mk baseQ) (oppositeUnipotentVariety G).toOver b hb) hchart
  have fact := @SchubertGeometry.CharacterLine.characterCoframe_unit_power.{u}
    K hK hAlg hChar G A gOld aOld ((@Over.homMk Scheme.{u} Scheme.instCategory (Spec (.of K)) ((algSpec (.of K)).obj (op A)) (Over.mk baseQ) t ht) ≫ ((@Over.homMk Scheme.{u} Scheme.instCategory (Spec (.of K)) (Over.mk baseQ) (oppositeUnipotentVariety G).toOver b hb) ≫ flagChartMap G gNew)) hOld ((j ≫ q) ≫ bsdhMap G word) (@endpoint_pullback.{u} K hK hAlg hChar G (bsdhScheme G word) ((algSpec (.of K)).obj (op A)) (Over.mk baseQ) (@Over.homMk Scheme.{u} Scheme.instCategory (Spec (.of K)) ((algSpec (.of K)).obj (op A)) (Over.mk baseQ) t ht) r (bsdhMap G word) (j ≫ q) h.symm ((@Over.homMk Scheme.{u} Scheme.instCategory (Spec (.of K)) (Over.mk baseQ) (oppositeUnipotentVariety G).toOver b hb) ≫ flagChartMap G gNew) (((Category.assoc b (flagChartMap G gNew).left (flagQuotient G)).trans (congrArg (fun z => b ≫ z) (SchubertGeometry.CharacterLine.frameQuotient G gNew))).trans hchart)) lOld hlOld haOld
    (fun d => (Scheme.Modules.pullback j).obj (M d))
    (fun d => flagChartComparison G word d j q (M d) (W d)) E
    (fun d => (comparisonCoframe j q t r h (M d) (CharacterLine.wordCharacterModule G (G.positiveRootCharacter ^ d) word) (W d).symm (CharacterLine.wordCharacterFrameIso G word (G.positiveRootCharacter ^ d) r gNew b hchart))) hE hF n
  exact fact

private theorem chartLift_factor {K : Type u}
    [hK : Field K] [hAlg : IsAlgClosed K] [hChar : CharZero K]
    (G : ReductiveGroupData K) {J : Type u}
    (F : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} K)
    (point : J → G.points)
    (a : ∀ j, (algSpec (.of K)).obj (op (F.obj (singletonIndex j))) ⟶
      (oppositeUnipotentVariety G).toOver)
    (s : {s : Finset J // s.Nonempty}) (j : J) (hj : j ∈ s.val) :
    chartLift G F point a s j hj =
      ((algSpec (.of K)).map (F.map (singletonArrow s j hj)).op ≫ a j) ≫
        flagChartMap G (point j) := by
  exact (Category.assoc ((algSpec (.of K)).map (F.map (singletonArrow s j hj)).op)
    (a j) (flagChartMap G (point j))).symm

private theorem chartQuotient_eq {K : Type u}
    [hK : Field K] [hAlg : IsAlgClosed K] [hChar : CharZero K]
    (G : ReductiveGroupData K) (P : Over (Spec (.of K))) (g : G.points)
    (a : P ⟶ (oppositeUnipotentVariety G).toOver)
    (k l : P ⟶ (reductiveVariety G).toOver) (hl : l = a ≫ flagChartMap G g)
    (m : P.left ⟶ (flagVariety G).scheme)
    (ha : l.left ≫ flagQuotient G = m) (hk : k.left ≫ flagQuotient G = m) :
    a ≫ flagChartMorphism G g = k ≫ flagQuotientMorphism G := by
  apply CategoryTheory.Over.OverMorphism.ext
  have hf := congrArg (fun z => a.left ≫ z)
    (SchubertGeometry.CharacterLine.frameQuotient G g)
  have hg := (Category.assoc a.left (flagChartMap G g).left (flagQuotient G)).trans hf
  have hleft := congrArg
    (fun z : P ⟶ (reductiveVariety G).toOver => z.left) hl
  have hquotient := congrArg (fun z => z ≫ flagQuotient G) hleft
  exact hg.symm.trans (hquotient.symm.trans (ha.trans hk.symm))

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
    (hgroup : ∀ s j hj k hk, chartLift G F point a s j hj =
      chartLift G F point a s k hk * (beta s j hj k hk ≫ borelInclusion G))
    (hco : ∀ s j hj k hk l hl, wordTransitionUnit G F beta s j hj l hl =
      wordTransitionUnit G F beta s k hk l hl * wordTransitionUnit G F beta s j hj k hk)
    (hn : ∀ s t (f : s ⟶ t) j hj k hk,
      Units.map (F.map f).hom.toMonoidHom (wordTransitionUnit G F beta s j hj k hk) =
        wordTransitionUnit G F beta t j ((leOfHom f) hj) k ((leOfHom f) hk))

private theorem preimageCoframe_unit_power (i : G.rootBase.support)
    (D : WordPreimageRefinement G F cF word q i) (n : ℕ) :
    affineCoframeUnit D.ring (frame_on_composite D.toChart.left (cF.ι.app (op D.index)).left (D.toChart.left ≫ (cF.ι.app (op D.index)).left) rfl (matchingModule F cF (wordTransitionUnit G F beta) n) (localCharacterTrivialization F cF hcF (wordTransitionUnit G F beta) n hco hn D.index D.entry D.mem)) (comparisonCoframe (D.toChart.left ≫ (cF.ι.app (op D.index)).left) q D.toPreimage ((preimageSnd G word q i) ≫ q) ((congrArg (fun z => z ≫ q) D.triangle).trans (Category.assoc D.toPreimage (preimageSnd G word q i) q)) (matchingModule F cF (wordTransitionUnit G F beta) n) (CharacterLine.wordCharacterModule G (G.positiveRootCharacter ^ n) word) (@wordCharacterMatchingIso.{u} K hK hAlg hChar G J F hFopen hFdir cF hcF word q n point a ha beta hgroup hco hn).symm (CharacterLine.wordCharacterFrameIso G word (G.positiveRootCharacter ^ n) ((preimageSnd G word q i) ≫ q) (DeterminantSection.oppositionChartPoint G i) (preimageLift G word q i) (preimageLift_equation G word q i))) =
      (affineCoframeUnit D.ring (frame_on_composite D.toChart.left (cF.ι.app (op D.index)).left (D.toChart.left ≫ (cF.ι.app (op D.index)).left) rfl (matchingModule F cF (wordTransitionUnit G F beta) 1) (localCharacterTrivialization F cF hcF (wordTransitionUnit G F beta) 1 hco hn D.index D.entry D.mem)) (comparisonCoframe (D.toChart.left ≫ (cF.ι.app (op D.index)).left) q D.toPreimage ((preimageSnd G word q i) ≫ q) ((congrArg (fun z => z ≫ q) D.triangle).trans (Category.assoc D.toPreimage (preimageSnd G word q i) q)) (matchingModule F cF (wordTransitionUnit G F beta) 1) (CharacterLine.wordCharacterModule G (G.positiveRootCharacter ^ 1) word) (@wordCharacterMatchingIso.{u} K hK hAlg hChar G J F hFopen hFdir cF hcF word q 1 point a ha beta hgroup hco hn).symm (CharacterLine.wordCharacterFrameIso G word (G.positiveRootCharacter ^ 1) ((preimageSnd G word q i) ≫ q) (DeterminantSection.oppositionChartPoint G i) (preimageLift G word q i) (preimageLift_equation G word q i)))) ^ n := by
  have hfactor := congrArg (fun z => D.toChart ≫ z)
    (@chartLift_factor.{u} K hK hAlg hChar G J F point a D.index D.entry D.mem)
  have hl := hfactor.trans (Category.assoc D.toChart (((algSpec (.of K)).map (F.map (singletonArrow D.index D.entry D.mem)).op) ≫ a D.entry)
    (flagChartMap G (point D.entry))).symm
  have haOld := (refined_quotient D.toChart.left (chartLift G F point a D.index D.entry D.mem).left (flagQuotient G) (cF.ι.app (op D.index)).left q (bsdhMap G word) (lift_quotient G F cF word q point a ha D.index D.entry D.mem))
  have hk := (@endpoint_pullback.{u} K hK hAlg hChar G (bsdhScheme G word) ((algSpec (.of K)).obj (op D.ring)) (Over.mk D.preimageBase) (@Over.homMk Scheme.{u} Scheme.instCategory (Spec (.of K)) ((algSpec (.of K)).obj (op D.ring)) (Over.mk D.preimageBase) D.toPreimage D.base) ((preimageSnd G word q i) ≫ q) (bsdhMap G word) ((D.toChart.left ≫ (cF.ι.app (op D.index)).left) ≫ q) ((congrArg (fun z => z ≫ q) D.triangle).trans (Category.assoc D.toPreimage (preimageSnd G word q i) q)).symm ((@Over.homMk Scheme.{u} Scheme.instCategory (Spec (.of K)) (Over.mk D.preimageBase) (oppositeUnipotentVariety G).toOver (preimageLift G word q i) D.lift_over) ≫ flagChartMap G (DeterminantSection.oppositionChartPoint G i)) (((Category.assoc (preimageLift G word q i) (flagChartMap G (DeterminantSection.oppositionChartPoint G i)).left (flagQuotient G)).trans (congrArg (fun z => preimageLift G word q i ≫ z) (SchubertGeometry.CharacterLine.frameQuotient G (DeterminantSection.oppositionChartPoint G i)))).trans (preimageLift_equation G word q i)))
  have hChart := @chartQuotient_eq.{u} K hK hAlg hChar G ((algSpec (.of K)).obj (op D.ring))
    (point D.entry) (D.toChart ≫ (((algSpec (.of K)).map (F.map (singletonArrow D.index D.entry D.mem)).op) ≫ a D.entry)) ((@Over.homMk Scheme.{u} Scheme.instCategory (Spec (.of K)) ((algSpec (.of K)).obj (op D.ring)) (Over.mk D.preimageBase) D.toPreimage D.base) ≫ ((@Over.homMk Scheme.{u} Scheme.instCategory (Spec (.of K)) (Over.mk D.preimageBase) (oppositeUnipotentVariety G).toOver (preimageLift G word q i) D.lift_over) ≫ flagChartMap G (DeterminantSection.oppositionChartPoint G i))) (D.toChart ≫ chartLift G F point a D.index D.entry D.mem) hl (((D.toChart.left ≫ (cF.ι.app (op D.index)).left) ≫ q) ≫ bsdhMap G word) haOld hk
  have hE := fun d => @matchingRefinedCoframe_eval.{u} K hK hAlg hChar G J
    F hFopen hFdir cF hcF word q d point a ha beta hgroup hco hn
    D.index D.entry D.mem ((algSpec (.of K)).obj (op D.ring)) D.toChart
  have fact := @wordCoframe_unit_power.{u} K hK hAlg hChar G word D.ring
    cF.pt.left (wordChartPreimage G word q i) D.preimageBase (D.toChart.left ≫ (cF.ι.app (op D.index)).left) q D.toPreimage D.base ((preimageSnd G word q i) ≫ q) ((congrArg (fun z => z ≫ q) D.triangle).trans (Category.assoc D.toPreimage (preimageSnd G word q i) q))
    (fun d => (matchingModule F cF (wordTransitionUnit G F beta) d)) (fun d => (@wordCharacterMatchingIso.{u} K hK hAlg hChar G J F hFopen hFdir cF hcF word q d point a ha beta hgroup hco hn)) (fun d => (frame_on_composite D.toChart.left (cF.ι.app (op D.index)).left (D.toChart.left ≫ (cF.ι.app (op D.index)).left) rfl (matchingModule F cF (wordTransitionUnit G F beta) d) (localCharacterTrivialization F cF hcF (wordTransitionUnit G F beta) d hco hn D.index D.entry D.mem)))
    (DeterminantSection.oppositionChartPoint G i) (preimageLift G word q i) D.lift_over (preimageLift_equation G word q i)
    (point D.entry) (D.toChart ≫ (((algSpec (.of K)).map (F.map (singletonArrow D.index D.entry D.mem)).op) ≫ a D.entry)) hChart (D.toChart ≫ chartLift G F point a D.index D.entry D.mem) hl haOld hE n
  exact fact

variable {R : Type u} [hR : CommRing R]
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

private theorem retainedWordLine_factor (n : ℕ) :
    @retainedWordLineIso.{u} K hK hAlg hChar G J F hFopen hFdir cF hcF word q
      point a ha beta hgroup hco hn R hR N hNopen hNdir v deltaN hd cN hcN qN hqN
      hcoN hnN n =
    @matchingPullbackIso.{u} R K J hR hK.toCommRing N F hNopen hFopen hNdir hFdir
      cN hcN cF hcF v qN hqN deltaN (wordTransitionUnit G F beta) hd n
      hcoN hnN hco hn ≪≫
      (@wordCharacterMatchingIso.{u} K hK hAlg hChar G J F hFopen hFdir cF hcF
        word q n point a ha beta hgroup hco hn).symm :=
  rfl


private theorem preimageFrame_factor (i : G.rootBase.support) (n : ℕ) :
    (@wordChartPreimageFrame.{u} K hK hAlg hChar G J F hFopen hFdir cF hcF word q
      point a ha beta hgroup hco hn R hR N hNopen hNdir v deltaN hd cN hcN qN hqN hcoN hnN i n) =
      @inducedFrame.{u} (wordChartPreimage G word q i) cF.pt.left (bsdhScheme G word)
        (preimageSnd G word q i) q ((Scheme.Modules.pullback qN).obj (matchingModule N cN deltaN n)) (CharacterLine.wordCharacterModule G (G.positiveRootCharacter ^ n) word) (@retainedWordLineIso.{u} K hK hAlg hChar G J F hFopen hFdir cF hcF word q
      point a ha beta hgroup hco hn R hR N hNopen hNdir v deltaN hd cN hcN qN hqN hcoN hnN n) (CharacterLine.wordCharacterFrameIso G word (G.positiveRootCharacter ^ n) ((preimageSnd G word q i) ≫ q)
      (DeterminantSection.oppositionChartPoint G i) (preimageLift G word q i)
      (preimageLift_equation G word q i)) :=
  rfl

private theorem preimageCoframe_composite (i : G.rootBase.support) (n : ℕ)
    (s : {s : Finset J // s.Nonempty}) (A : CommAlgCat.{u} K)
    (f : ((algSpec (.of K)).obj (op A)) ⟶ (algSpec (.of K)).obj (op (F.obj s)))
    (t : Spec (.of A) ⟶ wordChartPreimage G word q i)
    (htri : (f.left ≫ (cF.ι.app (op s)).left) = t ≫ (preimageSnd G word q i)) :
    frame_on_composite t (preimageSnd G word q i) (f.left ≫ (cF.ι.app (op s)).left) htri ((Scheme.Modules.pullback qN).obj (matchingModule N cN deltaN n)) (@wordChartPreimageFrame.{u} K hK hAlg hChar G J F hFopen hFdir cF hcF word q point a ha beta hgroup hco hn R hR N hNopen hNdir v deltaN hd cN hcN qN hqN hcoN hnN i n) =
      (Scheme.Modules.pullback (f.left ≫ (cF.ι.app (op s)).left)).mapIso (@matchingPullbackIso.{u} R K J hR hK.toCommRing N F hNopen hFopen hNdir hFdir cN hcN cF hcF v qN hqN deltaN (wordTransitionUnit G F beta) hd n hcoN hnN hco hn) ≪≫
        comparisonCoframe (f.left ≫ (cF.ι.app (op s)).left) q t ((preimageSnd G word q i) ≫ q) ((congrArg (fun z => z ≫ q) htri).trans (Category.assoc t (preimageSnd G word q i) q)) (matchingModule F cF (wordTransitionUnit G F beta) n) (CharacterLine.wordCharacterModule G (G.positiveRootCharacter ^ n) word) (@wordCharacterMatchingIso.{u} K hK hAlg hChar G J F hFopen hFdir cF hcF word q n point a ha beta hgroup hco hn).symm (CharacterLine.wordCharacterFrameIso G word (G.positiveRootCharacter ^ n) ((preimageSnd G word q i) ≫ q) (DeterminantSection.oppositionChartPoint G i) (preimageLift G word q i) (preimageLift_equation G word q i)) := by
  have hFK := @preimageFrame_factor.{u} K hK hAlg hChar G J F hFopen hFdir cF hcF
    word q point a ha beta hgroup hco hn R hR N hNopen hNdir v deltaN hd
    cN hcN qN hqN hcoN hnN i n
  have hfirst := congrArg (fun E => frame_on_composite t (preimageSnd G word q i) (f.left ≫ (cF.ι.app (op s)).left) htri ((Scheme.Modules.pullback qN).obj (matchingModule N cN deltaN n)) E) hFK
  have hmid := @inducedFrame_composite.{u} (Spec (.of A)) (wordChartPreimage G word q i)
    cF.pt.left (bsdhScheme G word) t (preimageSnd G word q i) q (f.left ≫ (cF.ι.app (op s)).left) htri ((Scheme.Modules.pullback qN).obj (matchingModule N cN deltaN n)) (CharacterLine.wordCharacterModule G (G.positiveRootCharacter ^ n) word) (@retainedWordLineIso.{u} K hK hAlg hChar G J F hFopen hFdir cF hcF word q point a ha beta hgroup hco hn R hR N hNopen hNdir v deltaN hd cN hcN qN hqN hcoN hnN n) (CharacterLine.wordCharacterFrameIso G word (G.positiveRootCharacter ^ n) ((preimageSnd G word q i) ≫ q) (DeterminantSection.oppositionChartPoint G i) (preimageLift G word q i) (preimageLift_equation G word q i))
  have hlast := @comparisonCoframe_change.{u} (Spec (.of A)) cF.pt.left
    (bsdhScheme G word) (wordChartPreimage G word q i)
    (f.left ≫ (cF.ι.app (op s)).left) q t ((preimageSnd G word q i) ≫ q) ((congrArg (fun z => z ≫ q) htri).trans (Category.assoc t (preimageSnd G word q i) q)) ((Scheme.Modules.pullback qN).obj (matchingModule N cN deltaN n)) (matchingModule F cF (wordTransitionUnit G F beta) n) (CharacterLine.wordCharacterModule G (G.positiveRootCharacter ^ n) word) (@matchingPullbackIso.{u} R K J hR hK.toCommRing N F hNopen hFopen hNdir hFdir cN hcN cF hcF v qN hqN deltaN (wordTransitionUnit G F beta) hd n hcoN hnN hco hn) (@retainedWordLineIso.{u} K hK hAlg hChar G J F hFopen hFdir cF hcF word q point a ha beta hgroup hco hn R hR N hNopen hNdir v deltaN hd cN hcN qN hqN hcoN hnN n) (@wordCharacterMatchingIso.{u} K hK hAlg hChar G J F hFopen hFdir cF hcF word q n point a ha beta hgroup hco hn).symm
    (@retainedWordLine_factor.{u} K hK hAlg hChar G J F hFopen hFdir cF hcF
      word q point a ha beta hgroup hco hn R hR N hNopen hNdir v deltaN hd
      cN hcN qN hqN hcoN hnN n) (CharacterLine.wordCharacterFrameIso G word (G.positiveRootCharacter ^ n) ((preimageSnd G word q i) ≫ q) (DeterminantSection.oppositionChartPoint G i) (preimageLift G word q i) (preimageLift_equation G word q i))
  have fact := hfirst.trans (hmid.trans hlast)
  exact fact


/-- The coframe ratio on the matching line over a flag-chart inverse image
is the corresponding power of its degree-one ratio. -/
theorem wordPreimage_coframe_power (i : G.rootBase.support)
    (D : WordPreimageRefinement G F cF word q i) (n : ℕ) :
    affineCoframeUnit D.ring (((Scheme.Modules.pullback (D.toChart.left ≫ (cF.ι.app (op D.index)).left)).mapIso (@matchingPullbackIso.{u} R K J hR hK.toCommRing N F hNopen hFopen hNdir hFdir cN hcN cF hcF v qN hqN deltaN (wordTransitionUnit G F beta) hd n hcoN hnN hco hn)) ≪≫ (frame_on_composite D.toChart.left (cF.ι.app (op D.index)).left (D.toChart.left ≫ (cF.ι.app (op D.index)).left) rfl (matchingModule F cF (wordTransitionUnit G F beta) n) (localCharacterTrivialization F cF hcF (wordTransitionUnit G F beta) n hco hn D.index D.entry D.mem))) (frame_on_composite D.toPreimage (preimageSnd G word q i) (D.toChart.left ≫ (cF.ι.app (op D.index)).left) D.triangle ((Scheme.Modules.pullback qN).obj (matchingModule N cN deltaN n)) (@wordChartPreimageFrame.{u} K hK hAlg hChar G J F hFopen hFdir cF hcF word q point a ha beta hgroup hco hn R hR N hNopen hNdir v deltaN hd cN hcN qN hqN hcoN hnN i n)) =
      (affineCoframeUnit D.ring (((Scheme.Modules.pullback (D.toChart.left ≫ (cF.ι.app (op D.index)).left)).mapIso (@matchingPullbackIso.{u} R K J hR hK.toCommRing N F hNopen hFopen hNdir hFdir cN hcN cF hcF v qN hqN deltaN (wordTransitionUnit G F beta) hd 1 hcoN hnN hco hn)) ≪≫ (frame_on_composite D.toChart.left (cF.ι.app (op D.index)).left (D.toChart.left ≫ (cF.ι.app (op D.index)).left) rfl (matchingModule F cF (wordTransitionUnit G F beta) 1) (localCharacterTrivialization F cF hcF (wordTransitionUnit G F beta) 1 hco hn D.index D.entry D.mem))) (frame_on_composite D.toPreimage (preimageSnd G word q i) (D.toChart.left ≫ (cF.ι.app (op D.index)).left) D.triangle ((Scheme.Modules.pullback qN).obj (matchingModule N cN deltaN 1)) (@wordChartPreimageFrame.{u} K hK hAlg hChar G J F hFopen hFdir cF hcF word q point a ha beta hgroup hco hn R hR N hNopen hNdir v deltaN hd cN hcN qN hqN hcoN hnN i 1))) ^ n := by
  have hScalarN := @preimageCoframe_composite.{u} K hK hAlg hChar G J F hFopen hFdir cF hcF
    word q point a ha beta hgroup hco hn R hR N hNopen hNdir v deltaN hd
    cN hcN qN hqN hcoN hnN i n D.index D.ring D.toChart D.toPreimage D.triangle
  have hScalarOne := @preimageCoframe_composite.{u} K hK hAlg hChar G J F hFopen hFdir cF hcF
    word q point a ha beta hgroup hco hn R hR N hNopen hNdir v deltaN hd
    cN hcN qN hqN hcoN hnN i 1 D.index D.ring D.toChart D.toPreimage D.triangle
  have hTransferN := @coframeUnit_transport.{u} D.ring D.ring.commRing
    ((Scheme.Modules.pullback (D.toChart.left ≫ (cF.ι.app (op D.index)).left)).obj ((Scheme.Modules.pullback qN).obj (matchingModule N cN deltaN n))) ((Scheme.Modules.pullback (D.toChart.left ≫ (cF.ι.app (op D.index)).left)).obj (matchingModule F cF (wordTransitionUnit G F beta) n)) ((Scheme.Modules.pullback (D.toChart.left ≫ (cF.ι.app (op D.index)).left)).mapIso (@matchingPullbackIso.{u} R K J hR hK.toCommRing N F hNopen hFopen hNdir hFdir cN hcN cF hcF v qN hqN deltaN (wordTransitionUnit G F beta) hd n hcoN hnN hco hn)) (frame_on_composite D.toChart.left (cF.ι.app (op D.index)).left (D.toChart.left ≫ (cF.ι.app (op D.index)).left) rfl (matchingModule F cF (wordTransitionUnit G F beta) n) (localCharacterTrivialization F cF hcF (wordTransitionUnit G F beta) n hco hn D.index D.entry D.mem)) (comparisonCoframe (D.toChart.left ≫ (cF.ι.app (op D.index)).left) q D.toPreimage ((preimageSnd G word q i) ≫ q) ((congrArg (fun z => z ≫ q) D.triangle).trans (Category.assoc D.toPreimage (preimageSnd G word q i) q)) (matchingModule F cF (wordTransitionUnit G F beta) n) (CharacterLine.wordCharacterModule G (G.positiveRootCharacter ^ n) word) (@wordCharacterMatchingIso.{u} K hK hAlg hChar G J F hFopen hFdir cF hcF word q n point a ha beta hgroup hco hn).symm (CharacterLine.wordCharacterFrameIso G word (G.positiveRootCharacter ^ n) ((preimageSnd G word q i) ≫ q) (DeterminantSection.oppositionChartPoint G i) (preimageLift G word q i) (preimageLift_equation G word q i))) (((Scheme.Modules.pullback (D.toChart.left ≫ (cF.ι.app (op D.index)).left)).mapIso (@matchingPullbackIso.{u} R K J hR hK.toCommRing N F hNopen hFopen hNdir hFdir cN hcN cF hcF v qN hqN deltaN (wordTransitionUnit G F beta) hd n hcoN hnN hco hn)) ≪≫ (frame_on_composite D.toChart.left (cF.ι.app (op D.index)).left (D.toChart.left ≫ (cF.ι.app (op D.index)).left) rfl (matchingModule F cF (wordTransitionUnit G F beta) n) (localCharacterTrivialization F cF hcF (wordTransitionUnit G F beta) n hco hn D.index D.entry D.mem))) (frame_on_composite D.toPreimage (preimageSnd G word q i) (D.toChart.left ≫ (cF.ι.app (op D.index)).left) D.triangle ((Scheme.Modules.pullback qN).obj (matchingModule N cN deltaN n)) (@wordChartPreimageFrame.{u} K hK hAlg hChar G J F hFopen hFdir cF hcF word q point a ha beta hgroup hco hn R hR N hNopen hNdir v deltaN hd cN hcN qN hqN hcoN hnN i n)) rfl hScalarN
  have hTransferOne := @coframeUnit_transport.{u} D.ring D.ring.commRing
    ((Scheme.Modules.pullback (D.toChart.left ≫ (cF.ι.app (op D.index)).left)).obj ((Scheme.Modules.pullback qN).obj (matchingModule N cN deltaN 1))) ((Scheme.Modules.pullback (D.toChart.left ≫ (cF.ι.app (op D.index)).left)).obj (matchingModule F cF (wordTransitionUnit G F beta) 1)) ((Scheme.Modules.pullback (D.toChart.left ≫ (cF.ι.app (op D.index)).left)).mapIso (@matchingPullbackIso.{u} R K J hR hK.toCommRing N F hNopen hFopen hNdir hFdir cN hcN cF hcF v qN hqN deltaN (wordTransitionUnit G F beta) hd 1 hcoN hnN hco hn)) (frame_on_composite D.toChart.left (cF.ι.app (op D.index)).left (D.toChart.left ≫ (cF.ι.app (op D.index)).left) rfl (matchingModule F cF (wordTransitionUnit G F beta) 1) (localCharacterTrivialization F cF hcF (wordTransitionUnit G F beta) 1 hco hn D.index D.entry D.mem)) (comparisonCoframe (D.toChart.left ≫ (cF.ι.app (op D.index)).left) q D.toPreimage ((preimageSnd G word q i) ≫ q) ((congrArg (fun z => z ≫ q) D.triangle).trans (Category.assoc D.toPreimage (preimageSnd G word q i) q)) (matchingModule F cF (wordTransitionUnit G F beta) 1) (CharacterLine.wordCharacterModule G (G.positiveRootCharacter ^ 1) word) (@wordCharacterMatchingIso.{u} K hK hAlg hChar G J F hFopen hFdir cF hcF word q 1 point a ha beta hgroup hco hn).symm (CharacterLine.wordCharacterFrameIso G word (G.positiveRootCharacter ^ 1) ((preimageSnd G word q i) ≫ q) (DeterminantSection.oppositionChartPoint G i) (preimageLift G word q i) (preimageLift_equation G word q i))) (((Scheme.Modules.pullback (D.toChart.left ≫ (cF.ι.app (op D.index)).left)).mapIso (@matchingPullbackIso.{u} R K J hR hK.toCommRing N F hNopen hFopen hNdir hFdir cN hcN cF hcF v qN hqN deltaN (wordTransitionUnit G F beta) hd 1 hcoN hnN hco hn)) ≪≫ (frame_on_composite D.toChart.left (cF.ι.app (op D.index)).left (D.toChart.left ≫ (cF.ι.app (op D.index)).left) rfl (matchingModule F cF (wordTransitionUnit G F beta) 1) (localCharacterTrivialization F cF hcF (wordTransitionUnit G F beta) 1 hco hn D.index D.entry D.mem))) (frame_on_composite D.toPreimage (preimageSnd G word q i) (D.toChart.left ≫ (cF.ι.app (op D.index)).left) D.triangle ((Scheme.Modules.pullback qN).obj (matchingModule N cN deltaN 1)) (@wordChartPreimageFrame.{u} K hK hAlg hChar G J F hFopen hFdir cF hcF word q point a ha beta hgroup hco hn R hR N hNopen hNdir v deltaN hd cN hcN qN hqN hcoN hnN i 1)) rfl hScalarOne
  have hPower := @preimageCoframe_unit_power.{u} K hK hAlg hChar G J F hFopen hFdir
    cF hcF word q point a ha beta hgroup hco hn i D n
  exact hTransferN.trans (hPower.trans (congrArg (fun z => z ^ n) hTransferOne.symm))

end SchubertGeometry.RetainedCharacter
