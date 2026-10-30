import OrbitComplexity.SchubertGeometry.LineBundles.Characters.AssociatedTransition
import OrbitComplexity.SchubertGeometry.LineBundles.Characters.CharacterDescent
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # The line module from the associated-character frames -/

set_option autoImplicit false

noncomputable section
namespace SchubertGeometry.ProjectiveLine
open ReductiveGroups TauCeti GroupActions AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

open private line overlap overlapMap
  from OrbitComplexity.SchubertGeometry.IntegralProjectiveLine.Transition

open private characterSection
  from OrbitComplexity.SchubertGeometry.LineBundles.Characters.CharacterOverlap

open private characterRestriction characterRestriction_congr pullbackIsoOfEq
  from OrbitComplexity.SchubertGeometry.LineBundles.Characters.CharacterDescent

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "CharacterLine: characterModuleSection"

/-- Pullback of the Borel character function along the regular frame transition. -/
def characterModuleSection (i : G.rootBase.support) (chi : G.characters) :
    Γ(overlap K, ⊤) :=
  (Spec.map (CommRingCat.ofHom
      (AddMonoidAlgebra.toMultiplicativeAlgEquiv (R := K) K ℤ).symm.toRingHom) ≫
    (simpleOverlapMorphism G i).left).appTop
      ((Scheme.ΓSpecIso (.of G.borelAlgebra)).inv
        (borelCharacterMap G chi (MonoidAlgebra.single (Multiplicative.ofAdd 1) 1)))

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "CharacterLine: characterModuleSection_eq"

/-- The geometric transition section equals the previously computed Laurent character. -/
theorem characterModuleSection_eq (i : G.rootBase.support) (chi : G.characters) :
    SchubertGeometry.ProjectiveLine.characterModuleSection G i chi =
      (Scheme.ΓSpecIso (.of (LaurentPolynomial K))).inv
        (characterOverlapLaurent G i chi) := by
  let e := (AddMonoidAlgebra.toMultiplicativeAlgEquiv (R := K) K ℤ).symm
  let b : G.borelAlgebra →ₐ[K] LaurentPolynomial K :=
    e.toAlgHom.comp (simpleOverlapCoordinate G i)
  have hb : Spec.map (CommRingCat.ofHom e.toRingHom) ≫
      (simpleOverlapMorphism G i).left = Spec.map (CommRingCat.ofHom b.toRingHom) :=
    (Spec.map_comp (CommRingCat.ofHom (simpleOverlapCoordinate G i).toRingHom)
      (CommRingCat.ofHom e.toRingHom)).symm
  change (Spec.map (CommRingCat.ofHom e.toRingHom) ≫
    (simpleOverlapMorphism G i).left).appTop _ = _
  rw [hb]
  exact congrArg (fun m : CommRingCat.of G.borelAlgebra ⟶ Γ(overlap K, ⊤) =>
    m (borelCharacterMap G chi (MonoidAlgebra.single (Multiplicative.ofAdd 1) 1)))
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom b.toRingHom)).symm

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "CharacterLine: characterLineModule"

/-- Linear fibre coordinates in the associated charts match by the pulled-back character. -/
def characterLineModule (i : G.rootBase.support) (chi : G.characters) :
    (line K).Modules :=
  pullback (leftRestriction K)
    (characterRestriction (overlapMap K) (rightRestriction K) (characterModuleSection G i chi))

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "CharacterLine: characterLineModuleIso"

/-- The matching module is the character descent with the identical transition section. -/
def characterLineModuleIso (i : G.rootBase.support) (chi : G.characters) :
    SchubertGeometry.ProjectiveLine.characterLineModule G i chi ≅ characterDescentModule G i chi :=
      by
  have hs : characterModuleSection G i chi = characterSection G i chi :=
    characterModuleSection_eq G i chi
  exact pullbackIsoOfEq (leftRestriction K)
    (characterRestriction (overlapMap K) (rightRestriction K) (characterModuleSection G i chi))
    (characterRestriction (overlapMap K) (rightRestriction K) (characterSection G i chi))
    (characterRestriction_congr (overlapMap K) (rightRestriction K) hs)

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "CharacterLine: oddCharacterLineIso"

/-- The same odd full-lattice character gives the specified degree-p-minus-one line module. -/
def oddCharacterLineIso (p : ℕ) (hp : Odd p) (i : G.rootBase.support) :
    SchubertGeometry.ProjectiveLine.characterLineModule G i (G.oddRootCharacter p) ≅
      SchubertGeometry.ProjectiveLine.projectiveTransitionModule K (p - 1) :=
  SchubertGeometry.ProjectiveLine.characterLineModuleIso G i (G.oddRootCharacter p) ≪≫
    oddCharacterDescentIso G p hp i


end SchubertGeometry.ProjectiveLine
