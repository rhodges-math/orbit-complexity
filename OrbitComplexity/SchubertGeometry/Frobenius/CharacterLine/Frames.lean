import OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.Trivialization
import OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.Charts
import TauCeti.AlgebraicGeometry.Modules.Pullback
import Batteries.Tactic.Lint

set_option autoImplicit false

/-! # Regular frames of the full-character module -/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits ReductiveGroups GroupActions Opposite
open CartesianMonoidalCategory MonoidalCategory
open FrobeniusSplitting.CharacterLine
open scoped CategoryTheory.MonObj

noncomputable section
universe u v

namespace SchubertGeometry.CharacterLine

@[reassoc]
private theorem equalizer_coordinate {C D : Type*} [Category C] [Category D]
    (R : C ⥤ D) {X Y : C} (a b : X ⟶ Y) [HasEqualizer a b]
    [HasEqualizer (R.map a) (R.map b)] [PreservesLimit (parallelPair a b) R]
    {X' Y' : D} (a' b' : X' ⟶ Y') [HasEqualizer a' b']
    (eX : R.obj X ≅ X') (eY : R.obj Y ≅ Y')
    (ha : R.map a ≫ eY.hom = eX.hom ≫ a')
    (hb : R.map b ≫ eY.hom = eX.hom ≫ b') :
    (PreservesEqualizer.iso R a b).hom ≫
        (HasLimit.isoOfNatIso
          (parallelPairIso (R.map a) (R.map b) a' b' eX eY ha hb)).hom ≫
        equalizer.ι a' b' = R.map (equalizer.ι a b) ≫ eX.hom := by
  have hc : (HasLimit.isoOfNatIso
      (parallelPairIso (R.map a) (R.map b) a' b' eX eY ha hb)).hom ≫
      equalizer.ι a' b' = equalizer.ι (R.map a) (R.map b) ≫ eX.hom :=
    HasLimit.isoOfNatIso_hom_π
      (parallelPairIso (R.map a) (R.map b) a' b' eX eY ha hb) WalkingParallelPair.zero
  rw [hc, ← Category.assoc, PreservesEqualizer.iso_hom, equalizerComparison_comp_π]

private theorem equalizer_frame {C D : Type*} [Category C] [Category D]
    (R : C ⥤ D) {X Y : C} (a b : X ⟶ Y) [HasEqualizer a b]
    [HasEqualizer (R.map a) (R.map b)] [PreservesLimit (parallelPair a b) R]
    {X' Y' V : D} (a' b' : X' ⟶ Y') [HasEqualizer a' b']
    (eX : R.obj X ≅ X') (eY : R.obj Y ≅ Y')
    (ha : R.map a ≫ eY.hom = eX.hom ≫ a')
    (hb : R.map b ≫ eY.hom = eX.hom ≫ b')
    (e : V ≅ equalizer a' b') (t : X' ⟶ V)
    (ht : e.inv = equalizer.ι a' b' ≫ t) :
    (PreservesEqualizer.iso R a b ≪≫
      HasLimit.isoOfNatIso (parallelPairIso (R.map a) (R.map b) a' b' eX eY ha hb) ≪≫
        e.symm).hom = R.map (equalizer.ι a b) ≫ eX.hom ≫ t := by
  simp only [Iso.trans_hom, Iso.symm_hom, ht]
  simpa only [Category.assoc] using congrArg (fun f => f ≫ t)
    (equalizer_coordinate R a b a' b' eX eY ha hb)

private theorem openSquare_evaluation {U Y P X : Scheme.{u}}
    (p : P ⟶ U) (k : P ⟶ X) (j : U ⟶ Y) (q : X ⟶ Y)
    [IsOpenImmersion j] [IsOpenImmersion k]
    (H : IsPullback p k j q) (s : U ⟶ P) (t : U ⟶ X)
    (hs : s ≫ p = 𝟙 U) (ht : s ≫ k = t) (h : 𝟙 U ≫ j = t ≫ q) :
    (openFunctionsBaseChange p k j q H).hom ≫
        relativeFunctionsMap U (X := Over.mk (𝟙 U)) (Y := Over.mk p)
          (Over.homMk s hs) =
      openFunctionsPullback (𝟙 U) t j q h := by
  let R := Scheme.Modules.restrictFunctor j
  let M : Over.mk q ⟶ Over.mk q := 𝟙 (Over.mk q)
  let N : Over.mk (𝟙 U) ⟶ Over.mk p := Over.homMk s hs
  have hk : N.left ≫ k = t ≫ M.left := ht.trans (Category.comp_id t).symm
  have hn := openFunctionsPullback_natural j (𝟙 U) p q q t k h H.w M N hk
  have hid : relativeFunctionsMap Y (X := Over.mk q) (Y := Over.mk q) M = 𝟙 _ :=
    (relativeFunctions Y).map_id (op (Over.mk q))
  have hmap : R.map (relativeFunctionsMap Y (X := Over.mk q) (Y := Over.mk q) M) =
      𝟙 (R.obj (relativeFunctionsObj Y (Over.mk q))) :=
    (congrArg R.map hid).trans (R.map_id (relativeFunctionsObj Y (Over.mk q)))
  have hb : (openFunctionsBaseChange p k j q H).hom = openFunctionsPullback p k j q H.w :=
    openFunctionsBaseChange_hom p k j q H
  exact (congrArg (fun f => f ≫ relativeFunctionsMap U
    (X := Over.mk (𝟙 U)) (Y := Over.mk p) N) hb).trans
      (hn.symm.trans ((congrArg (fun f => f ≫ openFunctionsPullback (𝟙 U) t j q h)
        hmap).trans (Category.id_comp _)))

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

private abbrev U := (oppositeUnipotentVariety G).toOver
private abbrev B := (borelVariety G).toOver
private abbrev E := U G ⊗ B G

private theorem sectionSquare (g : G.points) :
    𝟙 (U G).left ≫ (flagChartMorphism G g).left =
      (flagChartMap G g).left ≫ flagQuotient G := by
  have h : (flagChartMorphism G g).left =
      (flagChartMap G g).left ≫ (flagQuotientMorphism G).left :=
    congrArg (fun q : U G ⟶ (flagVariety G).toOver => q.left)
      (flagChartMap_quotient G g).symm
  have hq : (flagQuotientMorphism G).left = flagQuotient G := rfl
  exact (Category.id_comp (flagChartMorphism G g).left).trans
    (h.trans (congrArg (fun q => (flagChartMap G g).left ≫ q) hq))

private def identitySection :
    Over.mk (𝟙 (U G).left) ⟶ Over.mk (fst (U G) (B G)).left :=
  Over.homMk (lift (𝟙 (U G)) (1 : U G ⟶ B G)).left (by
    change (lift (𝟙 (U G)) (1 : U G ⟶ B G) ≫ fst (U G) (B G)).left =
      (𝟙 (U G) : U G ⟶ U G).left
    exact congrArg (fun q : U G ⟶ U G => q.left)
      (lift_fst (𝟙 (U G)) (1 : U G ⟶ B G)))

private theorem identity_chart (g : G.points) :
    (identitySection G).left ≫ (characterTorsorChart G g).left =
      (flagChartMap G g).left := by
  change (lift (𝟙 (U G)) (1 : U G ⟶ B G) ≫
      (flagTorsorIso G g).hom ≫
        pullback.snd (flagChartMorphism G g) (flagQuotientMorphism G)).left = _
  rw [flagTorsorIso_group, MonObj.comp_mul]
  simp only [lift_fst_assoc, lift_snd_assoc, Category.id_comp, MonObj.one_comp, mul_one]

/-- Evaluation on the original regular flag section, on all inverse-image opens. -/
def flagCharacterEvaluation (g : G.points) :
    (Scheme.Modules.restrictFunctor (flagChartMorphism G g).left).obj
        ((Scheme.Modules.pushforward (flagQuotient G)).obj
          (SheafOfModules.unit (reductiveVariety G).scheme.ringCatSheaf)) ⟶
      SheafOfModules.unit (U G).left.ringCatSheaf :=
  openFunctionsPullback (𝟙 (U G).left) (flagChartMap G g).left
      (flagChartMorphism G g).left (flagQuotient G) (sectionSquare G g) ≫
    (Scheme.Modules.pushforwardId (U G).left).hom.app
      (SheafOfModules.unit (U G).left.ringCatSheaf)

/-- The character trivialization is restriction to the identity Borel factor. -/
theorem flagCharacterChartIso_eval (g : G.points) (chi : G.characters) :
    (flagCharacterChartIso G g chi).hom =
      (Scheme.Modules.restrictFunctor (flagChartMorphism G g).left).map
          (flagCharacterInclusion G chi) ≫ flagCharacterEvaluation G g := by
  let R := Scheme.Modules.restrictFunctor (flagChartMorphism G g).left
  let : PreservesLimitsOfSize.{u, u} R :=
    FrobeniusSplitting.RetainedCharacter.restrictPreservesLimits (flagChartMorphism G g).left
  let e : R.obj (relativeFunctionsObj (flagVariety G).scheme
      (Over.mk (flagQuotient G))) ≅
      relativeFunctionsObj (U G).left (Over.mk (fst (U G) (B G)).left) :=
    openFunctionsBaseChange (fst (U G) (B G)).left
    (characterTorsorChart G g).left (flagChartMorphism G g).left (flagQuotient G)
    ((characterTorsorPullback G g).map (Over.forget (Spec (.of K))))
  have he : e.hom ≫ relativeFunctionsMap (U G).left
      (X := Over.mk (𝟙 (U G).left)) (Y := Over.mk (fst (U G) (B G)).left)
      (identitySection G) =
      openFunctionsPullback (𝟙 (U G).left) (flagChartMap G g).left
        (flagChartMorphism G g).left (flagQuotient G) (sectionSquare G g) := by
    exact openSquare_evaluation (fst (U G) (B G)).left
      (characterTorsorChart G g).left (flagChartMorphism G g).left (flagQuotient G)
      ((characterTorsorPullback G g).map (Over.forget (Spec (.of K))))
      (identitySection G).left (flagChartMap G g).left (identitySection G).w
      (identity_chart G g) (sectionSquare G g)
  have hc : (flagCharacterChartIso G g chi).hom =
      R.map (flagCharacterInclusion G chi) ≫ e.hom ≫
        relativeFunctionsMap (U G).left
          (X := Over.mk (𝟙 (U G).left)) (Y := Over.mk (fst (U G) (B G)).left)
          (identitySection G) ≫
          (Scheme.Modules.pushforwardId (U G).left).hom.app
            (SheafOfModules.unit (U G).left.ringCatSheaf) := by
    dsimp only [flagCharacterChartIso, id]
    apply equalizer_frame
    rfl
  let t := (Scheme.Modules.pushforwardId (U G).left).hom.app
    (SheafOfModules.unit (U G).left.ringCatSheaf)
  let s := relativeFunctionsMap (U G).left
    (X := Over.mk (𝟙 (U G).left)) (Y := Over.mk (fst (U G) (B G)).left)
    (identitySection G)
  have ha : R.map (flagCharacterInclusion G chi) ≫ e.hom ≫ s ≫ t =
      R.map (flagCharacterInclusion G chi) ≫ (e.hom ≫ s) ≫ t :=
    congrArg (fun f => R.map (flagCharacterInclusion G chi) ≫ f)
      (Category.assoc e.hom s t).symm
  have hh := congrArg (fun f => R.map (flagCharacterInclusion G chi) ≫ f ≫ t) he
  exact hc.trans (ha.trans hh)

/-- Pullback to a flag frame trivializes the full-character module. -/
def flagCharacterPullbackIso (g : G.points) (chi : G.characters)
    {X : Scheme.{u}} (a : X ⟶ (U G).left) :
    (Scheme.Modules.pullback (a ≫ (flagChartMorphism G g).left)).obj
      (flagCharacterModule G chi) ≅
      SheafOfModules.unit X.ringCatSheaf :=
  ((Scheme.Modules.pullbackComp a (flagChartMorphism G g).left).app
    (flagCharacterModule G chi)).symm ≪≫
    (Scheme.Modules.pullback a).mapIso
      (((Scheme.Modules.restrictFunctorIsoPullback (flagChartMorphism G g).left).app
        (flagCharacterModule G chi)).symm ≪≫ flagCharacterChartIso G g chi) ≪≫
    Scheme.Modules.pullbackObjUnitIso a

/-- The original endpoint equation induces a frame of the character module on a word chart. -/
def wordCharacterFrameIso (word : List G.rootBase.support) (chi : G.characters)
    {X : Scheme.{u}} (k : X ⟶ bsdhScheme G word) (g : G.points) (a : X ⟶ (U G).left)
    (h : a ≫ (flagChartMorphism G g).left = k ≫ bsdhMap G word) :
    (Scheme.Modules.pullback k).obj (wordCharacterModule G chi word) ≅
      SheafOfModules.unit X.ringCatSheaf :=
  (Scheme.Modules.pullbackComp k (bsdhMap G word)).app (flagCharacterModule G chi) ≪≫
    (Scheme.Modules.pullbackCongr h.symm).app (flagCharacterModule G chi) ≪≫
    flagCharacterPullbackIso G g chi a

end SchubertGeometry.CharacterLine
