import OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.WordMatchingBase
import OrbitComplexity.SchubertGeometry.Normality.BottSamelson.CharacterCoefficients
import OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.UnitTrivialization
import OrbitComplexity.FrobeniusSplitting.Normality.Covers.IntersectionModelCover
import OrbitComplexity.FrobeniusSplitting.Modules.Sections
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint
/-! # Word character frames and retained transition coefficients -/
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroupActions ReductiveGroups Opposite
open Scheme.Modules
open FrobeniusSplitting.CharacterLine FrobeniusSplitting.RetainedCharacter
open scoped CategoryTheory.MonObj
noncomputable section
universe u
namespace SchubertGeometry.RetainedCharacter
open private singletonIndex singletonArrow localFunctions coefficientSection
  from OrbitComplexity.FrobeniusSplitting.Modules.MatchingModule
open private precompose_rule map_coordinate iso_of_frame adjunct_frame coordinate_rule
  section_adjunct pullSection_hom section_matching leg legOpen flagPullback chartFrame
  chartCoordinate chartLift singleton_quotient lift_quotient coordinate_at
  from OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.WordMatchingBase
open private CoframeTransport.frameIso CoframeTransport.frameIso_hom
  from OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.CoframeTransport
open private pullSection pullSection_congr pair_substitute
  from OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.PullbackFrames
open private restrict_adjunct
  from OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.NativeFrame
open private section_character_power
  from OrbitComplexity.SchubertGeometry.Normality.BottSamelson.CharacterCoefficients
open private coconeCover
  from OrbitComplexity.FrobeniusSplitting.Normality.Covers.IntersectionModelCover
private theorem section_in_frame {X Y Z U : Scheme.{u}} (r : X ⟶ Z) (c : Y ⟶ X)
    [IsOpenImmersion c] (a : Y ⟶ U) (q : U ⟶ Z) (M : Z.Modules)
    (h : a ≫ q = c ≫ r)
    (e : (Scheme.Modules.pullback (a ≫ q)).obj M ≅ SheafOfModules.unit Y.ringCatSheaf)
    (s : SheafOfModules.unit Z.ringCatSheaf ⟶ M) (z : Γ(Y, ⊤))
    (hz : pullSection (a ≫ q) M s ≫ e.hom =
      globalSectionsSmul (SheafOfModules.unit Y.ringCatSheaf) z) :
    pullSection r M s ≫ (restrictAdjunction c).homEquiv _ _
        (CoframeTransport.frameIso r c a q M h e).hom =
      relativeCoefficient X (Over.mk c) z := by
  have he := CoframeTransport.frameIso_hom r c a q M h e
  have hc := pullSection_hom c r M s
  have hg := pullSection_congr h.symm M s
  have hframe := (congrArg (fun v => pullSection c _ (pullSection r M s) ≫ v) he).trans
    ((pair_substitute hc ((pullbackCongr h.symm).hom.app M ≫ e.hom)).trans
      ((pair_substitute hg e.hom).trans hz))
  have hs := section_adjunct c _ (pullSection r M s)
    ((restrictFunctorIsoPullback c).inv.app _ ≫
      (CoframeTransport.frameIso r c a q M h e).hom) z hframe
  exact (congrArg (fun t => pullSection r M s ≫ t)
    (restrict_adjunct c _ _ (CoframeTransport.frameIso r c a q M h e).hom).symm).trans hs

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)
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
variable
    (beta : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val)
      (k : J) (_ : k ∈ s.val),
      (algSpec (.of K)).obj (.op (F.obj s)) ⟶ (borelVariety G).toOver)
    (hgroup : ∀ s j hj k hk, chartLift G F point a s j hj =
      chartLift G F point a s k hk * (beta s j hj k hk ≫ borelInclusion G))
section CharacterMatching
set_option maxHeartbeats 200000
run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "WordMatching: lift_matching"
    (← IO.getStderr).flush
omit hopen hdir in
include hgroup in
private theorem lift_matching (s : {s : Finset J // s.Nonempty})
    (j : J) (hj : j ∈ s.val) (k : J) (hk : k ∈ s.val) :
    CharacterLine.characterFrameEvaluation G (G.positiveRootCharacter ^ n)
        ((algSpec (.of K)).obj (.op (F.obj s))) (leg F cF s ≫ (q ≫ bsdhMap G word))
        (chartLift G F point a s j hj) (lift_quotient G F cF word q point a ha s j hj) =
      CharacterLine.characterFrameEvaluation G (G.positiveRootCharacter ^ n)
        ((algSpec (.of K)).obj (.op (F.obj s))) (leg F cF s ≫ (q ≫ bsdhMap G word))
        (chartLift G F point a s k hk) (lift_quotient G F cF word q point a ha s k hk) ≫
          globalSectionsSmul
            (SheafOfModules.unit ((algSpec (.of K)).obj (.op (F.obj s))).left.ringCatSheaf)
            ((beta s j hj k hk).left.appTop
              (CharacterLine.borelCharacterSection G (G.positiveRootCharacter ^ n))) :=
  CharacterLine.characterFrameEvaluation_rule G (G.positiveRootCharacter ^ n)
      ((algSpec (.of K)).obj (.op (F.obj s))) (leg F cF s ≫ (q ≫ bsdhMap G word))
      (chartLift G F point a s j hj) (chartLift G F point a s k hk) (beta s j hj k hk)
      (lift_quotient G F cF word q point a ha s j hj)
      (lift_quotient G F cF word q point a ha s k hk) (hgroup s j hj k hk)
run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "WordMatching: power_coefficient"
    (← IO.getStderr).flush
omit hopen hdir in
private theorem power_coefficient (s : {s : Finset J // s.Nonempty})
    (j : J) (hj : j ∈ s.val) (k : J) (hk : k ∈ s.val) :
    type_of% (section_character_power G (F.obj s) (beta s j hj k hk) n) :=
  section_character_power G (F.obj s) (beta s j hj k hk) n
run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "WordMatching: frame_matching"
    (← IO.getStderr).flush
omit hopen hdir in
include hgroup in
private theorem frame_matching (s : {s : Finset J // s.Nonempty})
    (j : J) (hj : j ∈ s.val) (k : J) (hk : k ∈ s.val) :
    type_of% (precompose_rule (C := ((algSpec (.of K)).obj (.op (F.obj s))).left.Modules)
    ((pullbackComp (leg F cF s) (q ≫ bsdhMap G word)).hom.app
      (CharacterLine.flagCharacterModule G (G.positiveRootCharacter ^ n))) _ _ _ _
      (lift_matching G F cF word q n point a ha beta hgroup s j hj k hk)
      (congrArg (globalSectionsSmul (SheafOfModules.unit _))
        (power_coefficient G F n beta s j hj k hk))) :=
  precompose_rule (C := ((algSpec (.of K)).obj (.op (F.obj s))).left.Modules)
    ((pullbackComp (leg F cF s) (q ≫ bsdhMap G word)).hom.app
      (CharacterLine.flagCharacterModule G (G.positiveRootCharacter ^ n))) _ _ _ _
      (lift_matching G F cF word q n point a ha beta hgroup s j hj k hk)
      (congrArg (globalSectionsSmul (SheafOfModules.unit _))
        (power_coefficient G F n beta s j hj k hk))
run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "WordMatching: adjunct_matching"
    (← IO.getStderr).flush
omit hopen hdir in
include hgroup in
private theorem adjunct_matching (s : {s : Finset J // s.Nonempty})
    (j : J) (hj : j ∈ s.val) (k : J) (hk : k ∈ s.val) :
    type_of% ((congrArg ((pullbackPushforwardAdjunction (leg F cF s)).homEquiv _ _)
      (frame_matching G F cF word q n point a ha beta hgroup s j hj k hk)).trans
      ((pullbackPushforwardAdjunction (leg F cF s)).homEquiv_naturality_right _ _)) :=
  (congrArg ((pullbackPushforwardAdjunction (leg F cF s)).homEquiv _ _)
      (frame_matching G F cF word q n point a ha beta hgroup s j hj k hk)).trans
      ((pullbackPushforwardAdjunction (leg F cF s)).homEquiv_naturality_right _ _)
run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "WordMatching: coordinates_match"
    (← IO.getStderr).flush
include hgroup in
private theorem coordinates_match (s : {s : Finset J // s.Nonempty})
    (j : J) (hj : j ∈ s.val) (k : J) (hk : k ∈ s.val) :
    chartCoordinate G F cF hcF word q n point a ha j ≫
        relativeFunctionsMap cF.pt.left (nodeMap F cF (singletonArrow s j hj)) =
      chartCoordinate G F cF hcF word q n point a ha k ≫
        relativeFunctionsMap cF.pt.left (nodeMap F cF (singletonArrow s k hk)) ≫
          relativeFunctionsSmul cF.pt.left (node F cF s)
            (coefficientSection F cF s ((wordTransitionUnit G F beta s j hj k hk
              : F.obj s) ^ n)) :=
  (coordinate_rule (C := cF.pt.left.Modules) (coordinate_at G F cF hcF word q n point a ha s j hj)
      (coordinate_at G F cF hcF word q n point a ha s k hk)
      (adjunct_matching G F cF word q n point a ha beta hgroup s j hj k hk)).trans
    (Category.assoc (obj := cF.pt.left.Modules) _ _ _)

end CharacterMatching
private def flagMatchingHom : flagPullback G F cF word q n ⟶
    matchingModule F cF (wordTransitionUnit G F beta) n :=
  lift F cF (wordTransitionUnit G F beta) n (chartCoordinate G F cF hcF word q n point a ha)
    (coordinates_match G F cF hcF word q n point a ha beta hgroup)
private theorem flagMatching_coordinate (j : J) :
    flagMatchingHom G F cF hcF word q n point a ha beta hgroup ≫
        coordinate F cF (wordTransitionUnit G F beta) n j =
      chartCoordinate G F cF hcF word q n point a ha j :=
  lift_coordinate F cF (wordTransitionUnit G F beta) n _ _ j
omit [IsAlgClosed K] [CharZero K] in
include hcF in
private theorem singleton_cover (x : cF.pt.left) :
    ∃ (j : J) (y : Spec (.of (F.obj (singletonIndex j)))),
      leg F cF (singletonIndex j) y = x := by
  let D := F.op ⋙ algSpec (.of K) ⋙ Over.forget (Spec (.of K))
  let C := (Over.forget (Spec (.of K))).mapCocone cF
  let : ∀ {s t} (f : s ⟶ t), IsOpenImmersion (D.map f) := fun f => hopen f.unop
  let hC : IsColimit C := isColimitOfPreserves (Over.forget (Spec (.of K))) hcF
  let U := coconeCover D C hC
  obtain ⟨s, y, hy⟩ := U.exists_eq x
  change D.obj s at y
  change leg F cF s.unop y = x at hy
  obtain ⟨j, hj⟩ := s.unop.property
  refine ⟨j, (nodeMap F cF (singletonArrow s.unop j hj)).left y, ?_⟩
  exact (congrArg (fun z => z y) (nodeMap F cF (singletonArrow s.unop j hj)).w).trans hy
variable
    (hco : ∀ s j hj k hk l hl, wordTransitionUnit G F beta s j hj l hl =
      wordTransitionUnit G F beta s k hk l hl * wordTransitionUnit G F beta s j hj k hk)
    (hn : ∀ s t (f : s ⟶ t) j hj k hk,
      Units.map (F.map f).hom.toMonoidHom (wordTransitionUnit G F beta s j hj k hk) =
        wordTransitionUnit G F beta t j ((leOfHom f) hj) k ((leOfHom f) hk))
run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "WordMatching: flagMatching_isIso"
    (← IO.getStderr).flush
include hco hn in
private theorem flagMatching_isIso :
    IsIso (flagMatchingHom G F cF hcF word q n point a ha beta hgroup) := by
  let : ∀ j, IsOpenImmersion (leg F cF (singletonIndex j)) :=
    fun j => legOpen F cF hcF (singletonIndex j)
  apply FrobeniusSplitting.isIso_on_open_family
    (fun j => Spec (.of (F.obj (singletonIndex j))))
    (fun j => leg F cF (singletonIndex j)) (singleton_cover F cF hcF)
  intro j
  let c := leg F cF (singletonIndex j)
  let : IsOpenImmersion c := legOpen F cF hcF (singletonIndex j)
  let T := restrictFunctor c
  let k := coordinate F cF (wordTransitionUnit G F beta) n j
  let N : (Spec (.of (F.obj (singletonIndex j)))).Modules :=
    SheafOfModules.unit (Spec (.of (F.obj (singletonIndex j)))).ringCatSheaf
  let v := (restrictAdjunction c).counit.app N
  have hK : IsIso (C := (Spec (.of (F.obj (singletonIndex j)))).Modules) (T.map k) :=
    selectedCoordinate_isIso F cF hcF (wordTransitionUnit G F beta) n hco hn
      (singletonIndex j) j (Finset.mem_singleton_self j)
  have hV : IsIso (C := (Spec (.of (F.obj (singletonIndex j)))).Modules) v :=
    ((restrictFunctorAdjCounitIso c).app N).isIso_hom
  let : IsIso (C := (Spec (.of (F.obj (singletonIndex j)))).Modules) (T.map k ≫ v) :=
    IsIso.comp_isIso' (C := (Spec (.of (F.obj (singletonIndex j)))).Modules) hK hV
  have h := (map_coordinate T _ k _ v
    (flagMatching_coordinate G F cF hcF word q n point a ha beta hgroup j)).trans
      (adjunct_frame (restrictAdjunction c) _ N
        (chartFrame G F cF hcF word q n point a ha j).hom)
  exact iso_of_frame (C := (Spec (.of (F.obj (singletonIndex j)))).Modules)
    _ _ (chartFrame G F cF hcF word q n point a ha j) h
/-- The word character line is the matching line of its full Borel transition character. -/
def wordCharacterMatchingIso :
    (Scheme.Modules.pullback q).obj
        (CharacterLine.wordCharacterModule G (G.positiveRootCharacter ^ n) word) ≅
      matchingModule F cF (wordTransitionUnit G F beta) n := by
  letI : IsIso (flagMatchingHom G F cF hcF word q n point a ha beta hgroup) :=
    flagMatching_isIso G F cF hcF word q n point a ha beta hgroup hco hn
  exact (pullbackComp q (bsdhMap G word)).app
    (CharacterLine.flagCharacterModule G (G.positiveRootCharacter ^ n)) ≪≫
      asIso (flagMatchingHom G F cF hcF word q n point a ha beta hgroup)
run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "WordMatching: chartSection_coordinate"
    (← IO.getStderr).flush
private theorem chartSection_coordinate (j : J) :
    pullSection (q ≫ bsdhMap G word)
        (CharacterLine.flagCharacterModule G (G.positiveRootCharacter ^ n))
        (CharacterLine.flagDeterminantModuleSection G n) ≫
      chartCoordinate G F cF hcF word q n point a ha j =
        relativeCoefficient cF.pt.left (node F cF (singletonIndex j))
          ((a j ≫ flagChartMap G (point j)).left.appTop
            (DeterminantSection.positiveDetPowerFunction G n)) := by
  let c := leg F cF (singletonIndex j)
  let : IsOpenImmersion c := legOpen F cF hcF (singletonIndex j)
  let r := q ≫ bsdhMap G word
  let L := CharacterLine.flagCharacterModule G (G.positiveRootCharacter ^ n)
  let s := CharacterLine.flagDeterminantModuleSection G n
  exact section_in_frame r c (a j).left
    (flagChartMorphism G (point j)).left L (ha j)
    (CharacterLine.flagCharacterPullbackIso G (point j)
      (G.positiveRootCharacter ^ n) (a j).left) s _
    (CharacterLine.flagDeterminantPullback_frame G n (point j) (a j).left)

/-- The original determinant section has its original regular coefficient in each word frame. -/
theorem wordDeterminant_matching_coordinate (j : J) :
    (pullbackObjUnitIso q).inv ≫
        (Scheme.Modules.pullback q).map (CharacterLine.wordDeterminantModuleSection G n word) ≫
        (wordCharacterMatchingIso G F cF hcF word q n point a ha beta hgroup hco hn).hom ≫
        coordinate F cF (wordTransitionUnit G F beta) n j =
      relativeCoefficient cF.pt.left (node F cF (singletonIndex j))
        ((a j ≫ flagChartMap G (point j)).left.appTop
          (DeterminantSection.positiveDetPowerFunction G n)) := by
  let L := CharacterLine.flagCharacterModule G (G.positiveRootCharacter ^ n)
  let s := CharacterLine.flagDeterminantModuleSection G n
  let t := CharacterLine.wordDeterminantModuleSection G n word
  change pullSection q _ t ≫
    ((pullbackComp q (bsdhMap G word)).hom.app L ≫
      flagMatchingHom G F cF hcF word q n point a ha beta hgroup) ≫
        coordinate F cF (wordTransitionUnit G F beta) n j = _
  exact (section_matching (C := cF.pt.left.Modules) _ _ _ _ _ _
    (flagMatching_coordinate G F cF hcF word q n point a ha beta hgroup j)
    (pullSection_hom q (bsdhMap G word) L s)).trans
      (chartSection_coordinate G F cF hcF word q n point a ha j)
end Matching

end SchubertGeometry.RetainedCharacter
