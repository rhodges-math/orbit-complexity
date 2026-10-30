import OrbitComplexity.SchubertGeometry.LineBundles.Characters.CharacterOverlap
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Descent of the inverse character along the rank-one Borel overlap -/

set_option autoImplicit false

noncomputable section
namespace SchubertGeometry.ProjectiveLine
open ReductiveGroups TauCeti GroupActions AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u v w

open private characterSection
  from OrbitComplexity.SchubertGeometry.LineBundles.Characters.CharacterOverlap

open private line overlap overlapMap transitionSection
  from OrbitComplexity.SchubertGeometry.IntegralProjectiveLine.Transition

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "CharacterLine: characterRestriction"

private def characterRestriction {X Y : Scheme.{u}} (f : X ⟶ Y) {M : Y.Modules}
    (a : M ⟶ (Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf))
    (r : Γ(X, ⊤)) :
    M ⟶ (Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf) :=
  a ≫ (Scheme.Modules.pushforward f).map
    (Scheme.Modules.globalSectionsSmul (SheafOfModules.unit X.ringCatSheaf) r)

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "CharacterLine: characterRestriction_congr"

private theorem characterRestriction_congr {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M : Y.Modules}
    (a : M ⟶ (Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf))
    {r s : Γ(X, ⊤)} (h : r = s) :
    characterRestriction f a r = characterRestriction f a s :=
  congrArg (fun t : Γ(X, ⊤) => characterRestriction f a t) h

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "CharacterLine: pullbackIsoOfEq"

private def pullbackIsoOfEq {D : Type v} [Category.{w} D] {A B C : D}
    (f : A ⟶ C) (g h : B ⟶ C) [HasPullback f g] [HasPullback f h]
    (e : g = h) : pullback f g ≅ pullback f h :=
  pullback.congrHom (rfl : f = f) e

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "CharacterLine: characterDescentModule"

/-- Matching inverse-character fibre coordinates along the regular Borel overlap. -/
def characterDescentModule (i : G.rootBase.support) (chi : G.characters) :
    (line K).Modules :=
  pullback (leftRestriction K)
    (characterRestriction (overlapMap K) (rightRestriction K) (characterSection G i chi))

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "CharacterLine: oddCharacterDescentIso"

/-- The character descent is the specified Laurent-transition module on the charts. -/
def oddCharacterDescentIso (p : ℕ) (hp : Odd p) (i : G.rootBase.support) :
    characterDescentModule G i (G.oddRootCharacter p) ≅
      projectiveTransitionModule K (p - 1) := by
  have hs : characterSection G i (G.oddRootCharacter p) = transitionSection K (p - 1) :=
    congrArg (fun f : LaurentPolynomial K =>
      (Scheme.ΓSpecIso (.of (LaurentPolynomial K))).inv f)
      (characterOverlapLaurent_odd G p hp i)
  exact pullbackIsoOfEq (leftRestriction K)
    (characterRestriction (overlapMap K) (rightRestriction K)
      (characterSection G i (G.oddRootCharacter p)))
    (characterRestriction (overlapMap K) (rightRestriction K) (transitionSection K (p - 1)))
    (characterRestriction_congr (overlapMap K) (rightRestriction K) hs)


end SchubertGeometry.ProjectiveLine
