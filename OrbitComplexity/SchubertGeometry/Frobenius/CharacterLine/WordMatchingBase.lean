import OrbitComplexity.SchubertGeometry.Frobenius.BorelSectionCharacter
import OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.FrameRule
import OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.FrameComposition
import OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.PullbackFrames
import OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.UnitFrames
import OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.CoframeTransport
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint
/-! # Word character frames on an affine endpoint cover -/
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroupActions ReductiveGroups Opposite
open Scheme.Modules
open FrobeniusSplitting.CharacterLine FrobeniusSplitting.RetainedCharacter
open scoped CategoryTheory.MonObj
noncomputable section
universe u
namespace SchubertGeometry.RetainedCharacter
private theorem precompose_rule {C : Type*} [Category C] {A B D : C}
    (b : A ⟶ B) (f g : B ⟶ D) (s t : D ⟶ D)
    (h : f = g ≫ s) (hs : s = t) : b ≫ f = (b ≫ g) ≫ t :=
  (congrArg (fun e => b ≫ e) h).trans
    ((Category.assoc b g s).symm.trans (congrArg (fun e => (b ≫ g) ≫ e) hs))
open private singletonIndex singletonArrow localFunctions
  from OrbitComplexity.FrobeniusSplitting.Modules.MatchingModule
open private CoframeTransport.frameIso CoframeTransport.pullCoframe
  CoframeTransport.adjunct_congr CoframeTransport.frameIso_hom
  CoframeTransport.frameIso_evaluation CoframeTransport.evaluation_base_change
  from OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.CoframeTransport
open private adjunct_composite frameQuotient
  from OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.FrameComposition
open private pullSection pullSection_comp pullSection_congr pair_substitute
  from OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.PullbackFrames
open private restrict_adjunct
  from OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.NativeFrame
open private assoc_four
  from OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.UnitFrames
private theorem adjunct_restriction {P Q S : Scheme.{u}} (c : P ⟶ S)
    (f : Q ⟶ P) (d : Q ⟶ S) (h : f ≫ c = d) (M : S.Modules)
    (e : (Scheme.Modules.pullback c).obj M ⟶ SheafOfModules.unit P.ringCatSheaf) :
    (pullbackPushforwardAdjunction c).homEquiv M _ e ≫
        relativeFunctionsMap S (X := Over.mk d) (Y := Over.mk c) (Over.homMk f h) =
      (pullbackPushforwardAdjunction d).homEquiv M _
        ((pullbackCongr h.symm).hom.app M ≫ CoframeTransport.pullCoframe f c M e) := by
  have h₀ := adjunct_composite f c M e
  have h₁ := CoframeTransport.adjunct_congr h M (SheafOfModules.unit Q.ringCatSheaf)
    (CoframeTransport.pullCoframe f c M e)
  have h₂ := (congrArg (fun z => z ≫
    (pushforwardCongr h).hom.app (SheafOfModules.unit Q.ringCatSheaf)) h₀.symm).trans h₁
  let b := (pushforward c).map
    (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)
  let k := (pushforwardComp f c).hom.app (SheafOfModules.unit Q.ringCatSheaf)
  let v := (pushforwardCongr h).hom.app (SheafOfModules.unit Q.ringCatSheaf)
  change (pullbackPushforwardAdjunction c).homEquiv M _ e ≫ b ≫ k ≫ v = _
  change (((pullbackPushforwardAdjunction c).homEquiv M _ e ≫ b ≫ k) ≫ v) = _ at h₂
  exact (assoc_four _ b k v).symm.trans h₂
private theorem map_coordinate {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {A B P : C} {T : D} (f : A ⟶ B) (k : B ⟶ P)
    (c : A ⟶ P) (v : F.obj P ⟶ T) (h : f ≫ k = c) :
    F.map f ≫ F.map k ≫ v = F.map c ≫ v := by
  rw [← Category.assoc, ← F.map_comp, h]
private theorem iso_of_frame {C : Type*} [Category C] {A B P : C}
    (f : A ⟶ B) (k : B ⟶ P) [IsIso k] (e : A ≅ P) (h : f ≫ k = e.hom) :
    IsIso f := IsIso.of_isIso_fac_right h
private theorem adjunct_frame {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {H : D ⥤ C} (adj : F ⊣ H) (M : C) (N : D)
    (e : F.obj M ⟶ N) : F.map (adj.homEquiv M N e) ≫ adj.counit.app N = e :=
  (adj.homEquiv M N).symm_apply_apply e
private theorem coordinate_rule {C : Type*} [Category C] {A B : C}
    {x y e f : A ⟶ B} {s : B ⟶ B} (h₀ : x = e) (h₁ : y = f)
    (he : e = f ≫ s) : x = y ≫ s :=
  h₀.trans (he.trans (congrArg (fun z => z ≫ s) h₁.symm))
private theorem section_adjunct {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules)
    (s : SheafOfModules.unit Y.ringCatSheaf ⟶ M)
    (e : (Scheme.Modules.pullback f).obj M ⟶ SheafOfModules.unit X.ringCatSheaf) (r : Γ(X, ⊤))
    (h : pullSection f M s ≫ e = globalSectionsSmul (SheafOfModules.unit _) r) :
    s ≫ (pullbackPushforwardAdjunction f).homEquiv M _ e =
      relativeCoefficient Y (Over.mk f) r := by
  let U := pullbackObjUnitIso f
  have he : (Scheme.Modules.pullback f).map s ≫ e = U.hom ≫ globalSectionsSmul _ r := by
    change (U.inv ≫ (Scheme.Modules.pullback f).map s) ≫ e =
      globalSectionsSmul (SheafOfModules.unit X.ringCatSheaf) r at h
    exact U.inv_comp_eq.mp ((Category.assoc U.inv _ e).symm.trans h)
  exact ((pullbackPushforwardAdjunction f).homEquiv_naturality_left s e).symm.trans
    ((congrArg ((pullbackPushforwardAdjunction f).homEquiv _ _) he).trans
      (((pullbackPushforwardAdjunction f).homEquiv_naturality_right U.hom _).trans
        (congrArg (fun z => z ≫ (pushforward f).map (globalSectionsSmul _ r))
          (pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitIso_hom f))))
private theorem pullSection_hom {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : Z.Modules) (s : SheafOfModules.unit Z.ringCatSheaf ⟶ M) :
    pullSection f ((Scheme.Modules.pullback g).obj M) (pullSection g M s) ≫
        (pullbackComp f g).hom.app M = pullSection (f ≫ g) M s := by
  rw [← pullSection_comp f g M s]
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
private theorem section_matching {C : Type*} [Category C] {U A B D T : C}
    (s : U ⟶ A) (u : A ⟶ B) (f : B ⟶ D) (k : D ⟶ T) (c : B ⟶ T) (d : U ⟶ B)
    (h : f ≫ k = c) (hs : s ≫ u = d) : s ≫ (u ≫ f) ≫ k = d ≫ c := by
  simpa only [Category.assoc, h] using congrArg (fun z => z ≫ c) hs
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)
private theorem coordinate_restrict {L : Scheme.{u}} (chi : G.characters)
    (P Q : Over (Spec (.of K))) (c : P.left ⟶ L) [IsOpenImmersion c]
    (f : Q ⟶ P) (d : Q.left ⟶ L) (hf : f.left ≫ c = d)
    (r : L ⟶ (flagVariety G).scheme) (g : G.points)
    (a : P ⟶ (oppositeUnipotentVariety G).toOver)
    (ha : a.left ≫ (flagChartMorphism G g).left = c ≫ r)
    (h₀ : (a ≫ flagChartMap G g).left ≫ flagQuotient G = c ≫ r)
    (h₁ : (f ≫ a ≫ flagChartMap G g).left ≫ flagQuotient G = d ≫ r) :
    (restrictAdjunction c).homEquiv ((Scheme.Modules.pullback r).obj
        (CharacterLine.flagCharacterModule G chi)) (SheafOfModules.unit P.left.ringCatSheaf)
        (CoframeTransport.frameIso r c a.left (flagChartMorphism G g).left
          (CharacterLine.flagCharacterModule G chi) ha
          (CharacterLine.flagCharacterPullbackIso G g chi a.left)).hom ≫
        relativeFunctionsMap L (X := Over.mk d) (Y := Over.mk c) (Over.homMk f.left hf) =
      (pullbackPushforwardAdjunction d).homEquiv ((Scheme.Modules.pullback r).obj
        (CharacterLine.flagCharacterModule G chi)) (SheafOfModules.unit Q.left.ringCatSheaf)
        ((pullbackComp d r).hom.app (CharacterLine.flagCharacterModule G chi) ≫
          CharacterLine.characterFrameEvaluation G chi Q (d ≫ r)
            (f ≫ a ≫ flagChartMap G g) h₁) := by
  let M := (Scheme.Modules.pullback r).obj (CharacterLine.flagCharacterModule G chi)
  let e := (CoframeTransport.frameIso r c a.left (flagChartMorphism G g).left
    (CharacterLine.flagCharacterModule G chi) ha
    (CharacterLine.flagCharacterPullbackIso G g chi a.left)).hom
  have he := CoframeTransport.frameIso_evaluation G chi P c r g a ha
  have hb := CoframeTransport.evaluation_base_change G chi P Q f c r d hf
    (a ≫ flagChartMap G g) h₀
  have hp := congrArg (fun z => (pullbackCongr hf.symm).hom.app M ≫
    CoframeTransport.pullCoframe f.left c M z) he
  have ht := adjunct_restriction c f.left d hf M
    ((restrictFunctorIsoPullback c).inv.app M ≫ e)
  exact (congrArg (fun z => z ≫ relativeFunctionsMap L
    (X := Over.mk d) (Y := Over.mk c) (Over.homMk f.left hf))
      (restrict_adjunct c M _ e).symm).trans
        (ht.trans (congrArg ((pullbackPushforwardAdjunction d).homEquiv M _)
          (hp.trans hb)))
section Matching
variable {J : Type u}
    (F : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} K)
    [hopen : ∀ {s t} (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (F.map f).hom.toRingHom))]
    [hdir : ((F.op ⋙ algSpec (.of K) ⋙ Over.forget (Spec (.of K))) ⋙
      Scheme.forget).IsLocallyDirected]
    (cF : Cocone (F.op ⋙ algSpec (.of K))) (hcF : IsColimit cF)
    (word : List G.rootBase.support) (q : cF.pt.left ⟶ bsdhScheme G word) (n : ℕ)
    (point : J → G.points)
    (a : ∀ j, (algSpec (.of K)).obj (.op (F.obj (singletonIndex j))) ⟶
      (oppositeUnipotentVariety G).toOver)
    (ha : ∀ j, (a j).left ≫ (flagChartMorphism G (point j)).left =
      (cF.ι.app (.op (singletonIndex j))).left ≫ (q ≫ bsdhMap G word))
private abbrev leg (s : {s : Finset J // s.Nonempty}) :
    Spec (.of (F.obj s)) ⟶ cF.pt.left := (cF.ι.app (.op s)).left
omit [IsAlgClosed K] [CharZero K] in
include hcF in
private theorem legOpen (s : {s : Finset J // s.Nonempty}) :
    IsOpenImmersion (leg F cF s) := (retained_prior_charts F cF hcF).1 s
private abbrev flagPullback : cF.pt.left.Modules :=
  (Scheme.Modules.pullback (q ≫ bsdhMap G word)).obj
    (CharacterLine.flagCharacterModule G (G.positiveRootCharacter ^ n))
private def chartFrame (j : J) :
    (@restrictFunctor _ _ (leg F cF (singletonIndex j))
      (legOpen F cF hcF (singletonIndex j))).obj (flagPullback G F cF word q n) ≅
      SheafOfModules.unit (Spec (.of (F.obj (singletonIndex j)))).ringCatSheaf := by
  let : IsOpenImmersion (leg F cF (singletonIndex j)) := legOpen F cF hcF (singletonIndex j)
  exact CoframeTransport.frameIso (q ≫ bsdhMap G word) (leg F cF (singletonIndex j)) (a j).left
    (flagChartMorphism G (point j)).left
    (CharacterLine.flagCharacterModule G (G.positiveRootCharacter ^ n)) (ha j)
    (CharacterLine.flagCharacterPullbackIso G (point j)
      (G.positiveRootCharacter ^ n) (a j).left)
private def chartCoordinate (j : J) :
    flagPullback G F cF word q n ⟶ localFunctions F cF j := by
  let : IsOpenImmersion (leg F cF (singletonIndex j)) := legOpen F cF hcF (singletonIndex j)
  exact (restrictAdjunction (leg F cF (singletonIndex j))).homEquiv _ _
    (chartFrame G F cF hcF word q n point a ha j).hom
private def chartLift (s : {s : Finset J // s.Nonempty}) (j : J) (hj : j ∈ s.val) :
    (algSpec (.of K)).obj (.op (F.obj s)) ⟶ (reductiveVariety G).toOver :=
  (algSpec (.of K)).map (F.map (singletonArrow s j hj)).op ≫ a j ≫ flagChartMap G (point j)
omit hopen hdir in
include ha in
private theorem singleton_quotient (j : J) :
    (a j ≫ flagChartMap G (point j)).left ≫ flagQuotient G =
      leg F cF (singletonIndex j) ≫ (q ≫ bsdhMap G word) :=
  ((Category.assoc (a j).left (flagChartMap G (point j)).left (flagQuotient G)).trans
    (congrArg (fun z => (a j).left ≫ z) (frameQuotient G (point j)))).trans (ha j)
omit hopen hdir in
include ha in
private theorem lift_quotient (s : {s : Finset J // s.Nonempty})
    (j : J) (hj : j ∈ s.val) :
    (chartLift G F point a s j hj).left ≫ flagQuotient G =
      leg F cF s ≫ (q ≫ bsdhMap G word) := by
  let f := (algSpec (.of K)).map (F.map (singletonArrow s j hj)).op
  have hjq := singleton_quotient G F cF word q point a ha j
  exact (Category.assoc f.left _ _).trans
    ((congrArg (fun z => f.left ≫ z) hjq).trans
      ((Category.assoc f.left _ _).symm.trans
        (congrArg (fun z => z ≫ (q ≫ bsdhMap G word))
          (nodeMap F cF (singletonArrow s j hj)).w)))
private theorem coordinate_at (s : {s : Finset J // s.Nonempty})
    (j : J) (hj : j ∈ s.val) :
    type_of% (@coordinate_restrict K _ _ _ G cF.pt.left (G.positiveRootCharacter ^ n)
      ((algSpec (.of K)).obj (.op (F.obj (singletonIndex j))))
      ((algSpec (.of K)).obj (.op (F.obj s))) (leg F cF (singletonIndex j))
      (legOpen F cF hcF (singletonIndex j))
      ((algSpec (.of K)).map (F.map (singletonArrow s j hj)).op) (leg F cF s)
      (nodeMap F cF (singletonArrow s j hj)).w (q ≫ bsdhMap G word) (point j)
      (a j) (ha j) (singleton_quotient G F cF word q point a ha j)
      (lift_quotient G F cF word q point a ha s j hj)) :=
  @coordinate_restrict K _ _ _ G cF.pt.left (G.positiveRootCharacter ^ n)
      ((algSpec (.of K)).obj (.op (F.obj (singletonIndex j))))
      ((algSpec (.of K)).obj (.op (F.obj s))) (leg F cF (singletonIndex j))
      (legOpen F cF hcF (singletonIndex j))
      ((algSpec (.of K)).map (F.map (singletonArrow s j hj)).op) (leg F cF s)
      (nodeMap F cF (singletonArrow s j hj)).w (q ≫ bsdhMap G word) (point j)
      (a j) (ha j) (singleton_quotient G F cF word q point a ha j)
      (lift_quotient G F cF word q point a ha s j hj)
variable
    (beta : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val)
      (k : J) (_ : k ∈ s.val),
      (algSpec (.of K)).obj (.op (F.obj s)) ⟶ (borelVariety G).toOver)
    (hgroup : ∀ s j hj k hk, chartLift G F point a s j hj =
      chartLift G F point a s k hk * (beta s j hj k hk ≫ borelInclusion G))
/-- The full positive Borel character of a transition between regular group lifts. -/
def wordTransitionUnit (s : {s : Finset J // s.Nonempty})
    (j : J) (hj : j ∈ s.val) (k : J) (hk : k ∈ s.val) : (F.obj s)ˣ :=
  ProjectiveLine.positiveBorelSection G (F.obj s) (beta s j hj k hk)
end Matching
end SchubertGeometry.RetainedCharacter
