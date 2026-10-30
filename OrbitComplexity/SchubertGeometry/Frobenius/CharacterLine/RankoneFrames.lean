import OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.FrameComposition
import OrbitComplexity.SchubertGeometry.LineBundles.Characters.CharacterModules
import OrbitComplexity.SchubertGeometry.LineBundles.Modules.PolynomialBridge
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Character coframes on the two rank-one charts -/

open AlgebraicGeometry CategoryTheory ReductiveGroups GroupActions
open AlgebraicGeometry.Scheme.Modules

set_option autoImplicit false

noncomputable section
universe u

namespace SchubertGeometry.CharacterLine

open private line affine chart chartModule structureModule chartCounit
  from OrbitComplexity.SchubertGeometry.IntegralProjectiveLine.Transition

open private positive_section negative_section
  from OrbitComplexity.SchubertGeometry.LineBundles.Characters.AssociatedTransition


run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "RankoneFrames: inverse_precompose"

private theorem inverse_precompose {C : Type*} [Category C] {A B D : C}
    (q : A ⟶ B) (p : B ⟶ A) (hqp : q ≫ p = 𝟙 A)
    (t : B ⟶ D) (s : A ⟶ D) (h : t = p ≫ s) : q ≫ t = s :=
  (congrArg (fun v => q ≫ v) h).trans
    ((Category.assoc q p s).symm.trans
      ((congrArg (fun v => v ≫ s) hqp).trans (Category.id_comp s)))

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "RankoneFrames: quotient_factor"

private theorem quotient_factor {C : Type*} [Category C] {A B D E T : C}
    (a : A ⟶ B) (t : B ⟶ D) (p : A ⟶ E) (s : E ⟶ D)
    (q : D ⟶ T) (j : B ⟶ T) (ha : a ≫ t = p ≫ s) (hq : t ≫ q = j) :
    a ≫ j = p ≫ (s ≫ q) :=
  (congrArg (fun v => a ≫ v) hq.symm).trans
    ((Category.assoc a t q).symm.trans
      ((congrArg (fun v => v ≫ q) ha).trans (Category.assoc p s q)))

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "RankoneFrames: frameIso"

private def frameIso {X Y Z U : Scheme.{u}} (r : X ⟶ Z) (c : Y ⟶ X)
    [IsOpenImmersion c] (a : Y ⟶ U) (q : U ⟶ Z) (M : Z.Modules)
    (h : a ≫ q = c ≫ r)
    (e : (pullback (a ≫ q)).obj M ≅ SheafOfModules.unit Y.ringCatSheaf) :
    (restrictFunctor c).obj ((pullback r).obj M) ≅
      SheafOfModules.unit Y.ringCatSheaf :=
  (restrictFunctorIsoPullback c).app ((pullback r).obj M) ≪≫
    (pullbackComp c r).app M ≪≫ (pullbackCongr h.symm).app M ≪≫ e

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "RankoneFrames: adjunct_counit"

private theorem adjunct_counit {X Y : Scheme.{u}} (c : X ⟶ Y)
    [IsOpenImmersion c] (M : Y.Modules) (N : X.Modules)
    (e : (restrictFunctor c).obj M ⟶ N) :
    (restrictFunctor c).map ((restrictAdjunction c).homEquiv M N e) ≫
      (restrictFunctorAdjCounitIso c).hom.app N = e :=
  ((restrictAdjunction c).homEquiv M N).symm_apply_apply e

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "RankoneFrames: rankoneFlagMap"

/-- The standard inclusion of the simple Schubert projective line in the flag variety. -/
def rankoneFlagMap (i : G.rootBase.support) :
    line K ⟶ (flagVariety G).scheme :=
  ((simpleSchubertIso G i).inv ≫
    schubertInclusion G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).left

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "RankoneFrames: rankoneCharacterModule"

/-- The original full character module pulled back to the simple Schubert line. -/
def rankoneCharacterModule (i : G.rootBase.support) (chi : G.characters) :
    (line K).Modules :=
  (pullback (rankoneFlagMap G i)).obj (flagCharacterModule G chi)

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "RankoneFrames: polynomialGa"

private def polynomialGa :
    (affineVariety K (Polynomial K)).toOver ⟶ (additiveVariety K).toOver :=
  affineMorphism (gaPolynomialEquiv K).toAlgHom

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "RankoneFrames: polynomialGa_inverse"

omit [IsAlgClosed K] [CharZero K] in
private theorem polynomialGa_inverse :
    (polynomialGa (K := K)).left ≫
      Spec.map (CommRingCat.ofHom (gaPolynomialEquiv K).symm.toRingHom) =
        𝟙 (affine K) := by
  change Spec.map (CommRingCat.ofHom (gaPolynomialEquiv K).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (gaPolynomialEquiv K).symm.toRingHom) = _
  rw [← Spec.map_comp]
  have h : (CommRingCat.ofHom (gaPolynomialEquiv K).symm.toRingHom) ≫
      (CommRingCat.ofHom (gaPolynomialEquiv K).toRingHom) =
        𝟙 (CommRingCat.of (Polynomial K)) := by
    exact congrArg (fun f : Polynomial K →+* Polynomial K => CommRingCat.ofHom f)
      (RingHom.ext (fun x : Polynomial K => (gaPolynomialEquiv K).apply_symm_apply x))
  exact (congrArg (fun f => Spec.map f) h).trans (Spec.map_id _)

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "RankoneFrames: rootPoint"

private def rootPoint (i : G.rootBase.support) (j : ULift.{u} (Fin 2)) : G.points :=
  Fin.cases ((G.reflectionPoint i.val)⁻¹) (fun _ => 1) j.down

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "RankoneFrames: rootFactor"

private def rootFactor (i : G.rootBase.support) (j : ULift.{u} (Fin 2)) :
    (affineVariety K (Polynomial K)).toOver ⟶ (oppositeUnipotentVariety G).toOver :=
  polynomialGa (K := K) ≫ Fin.cases (simplePositiveOppositeFactor G i)
    (fun _ => simpleNegativeOppositeFactor G i) j.down

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "RankoneFrames: rootSection"

private def rootSection (i : G.rootBase.support) (j : ULift.{u} (Fin 2)) :
    (additiveVariety K).toOver ⟶ (reductiveVariety G).toOver :=
  Fin.cases (simplePositiveSection G i) (fun _ => simpleNegativeSection G i) j.down

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "RankoneFrames: rootFactor_section"

private theorem rootFactor_section (i : G.rootBase.support) (j : ULift.{u} (Fin 2)) :
    rootFactor G i j ≫ flagChartMap G (rootPoint G i j) =
      polynomialGa (K := K) ≫ rootSection G i j := by
  obtain ⟨j⟩ := j
  fin_cases j
  · exact (Category.assoc _ _ _).trans
      (congrArg (fun f => polynomialGa (K := K) ≫ f) (positive_section G i))
  · exact (Category.assoc _ _ _).trans
      (congrArg (fun f => polynomialGa (K := K) ≫ f) (negative_section G i))

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "RankoneFrames: polynomialSection_chart"

private theorem polynomialSection_chart (i : G.rootBase.support)
    (j : ULift.{u} (Fin 2)) :
    (polynomialGa (K := K)).left ≫
      (rootSection G i j ≫ flagQuotientMorphism G).left =
        chart K j ≫ rankoneFlagMap G i := by
  obtain ⟨j⟩ := j
  fin_cases j
  · exact inverse_precompose _ _ (polynomialGa_inverse (K := K)) _ _
      (ProjectiveLine.simplePositiveSection_polynomial G i)
  · exact inverse_precompose _ _ (polynomialGa_inverse (K := K)) _ _
      (ProjectiveLine.simpleNegativeSection_polynomial G i)

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "RankoneFrames: rootFactor_chart"

private theorem rootFactor_chart (i : G.rootBase.support) (j : ULift.{u} (Fin 2)) :
    (rootFactor G i j).left ≫ (flagChartMorphism G (rootPoint G i j)).left =
      chart K j ≫ rankoneFlagMap G i := by
  have hq : (flagChartMap G (rootPoint G i j)).left ≫ flagQuotient G =
      (flagChartMorphism G (rootPoint G i j)).left :=
    congrArg (fun f : (oppositeUnipotentVariety G).toOver ⟶
      (flagVariety G).toOver => f.left) (flagChartMap_quotient G (rootPoint G i j))
  have hs := congrArg (fun f : (affineVariety K (Polynomial K)).toOver ⟶
    (reductiveVariety G).toOver => f.left) (rootFactor_section G i j)
  exact (quotient_factor (rootFactor G i j).left
    (flagChartMap G (rootPoint G i j)).left (polynomialGa (K := K)).left
    (rootSection G i j).left (flagQuotient G)
    (flagChartMorphism G (rootPoint G i j)).left hs hq).trans
      (polynomialSection_chart G i j)

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "RankoneFrames: rankoneCharacterFrame"

/-- The character coframe given by the root lift on either standard chart. -/
def rankoneCharacterFrame (i : G.rootBase.support) (chi : G.characters)
    (j : ULift.{u} (Fin 2)) :
    (restrictFunctor (chart K j)).obj (rankoneCharacterModule G i chi) ≅
      structureModule (affine K) :=
  frameIso (rankoneFlagMap G i) (chart K j) (rootFactor G i j).left
    (flagChartMorphism G (rootPoint G i j)).left (flagCharacterModule G chi)
    (rootFactor_chart G i j)
    (flagCharacterPullbackIso G (rootPoint G i j) chi (rootFactor G i j).left)

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "RankoneFrames: rankoneCharacterCoordinate"

/-- The chart coordinate on the original character module, adjoint to its root coframe. -/
def rankoneCharacterCoordinate (i : G.rootBase.support) (chi : G.characters)
    (j : ULift.{u} (Fin 2)) :
    rankoneCharacterModule G i chi ⟶ chartModule K j :=
  (restrictAdjunction (chart K j)).homEquiv
    (rankoneCharacterModule G i chi)
    (structureModule (affine K))
    (rankoneCharacterFrame G i chi j).hom

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "RankoneFrames: rankoneCharacterCoordinate_frame"

/-- Restriction followed by the chart counit recovers the root coframe. -/
theorem rankoneCharacterCoordinate_frame (i : G.rootBase.support) (chi : G.characters)
    (j : ULift.{u} (Fin 2)) :
    (restrictFunctor (chart K j)).map
        (rankoneCharacterCoordinate G i chi j) ≫ chartCounit K j =
      (rankoneCharacterFrame G i chi j).hom :=
  adjunct_counit (chart K j) (rankoneCharacterModule G i chi)
    (structureModule (affine K))
    (rankoneCharacterFrame G i chi j).hom

end SchubertGeometry.CharacterLine
