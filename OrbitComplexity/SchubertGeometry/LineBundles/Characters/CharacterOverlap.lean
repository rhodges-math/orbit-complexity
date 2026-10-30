import OrbitComplexity.SchubertGeometry.LineBundles.Modules.OverlapCoordinate
import OrbitComplexity.SchubertGeometry.IntegralProjectiveLine.Transition
import Batteries.Tactic.Lint

/-! # Character functions on the rank-one Borel overlap -/

set_option autoImplicit false

noncomputable section
namespace SchubertGeometry.ProjectiveLine
open ReductiveGroups TauCeti GroupActions AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

private abbrev line (K : Type u) [Field K] :=
  projectiveScheme K (ULift.{u} (Fin 2))
private abbrev overlap (K : Type u) [Field K] := Spec (.of (LaurentPolynomial K))
run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "CharacterLine: overlapMap"

private def overlapMap : overlap K ⟶ line K :=
  Spec.map (CommRingCat.ofHom Polynomial.toLaurent) ≫ projectiveLinePolynomialChart K ⟨0⟩

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "CharacterLine: characterOverlapLaurent"

/-- The overlap character as a regular Laurent function. -/
def characterOverlapLaurent (i : G.rootBase.support) (chi : G.characters) :
    LaurentPolynomial K :=
  (AddMonoidAlgebra.toMultiplicativeAlgEquiv (R := K) K ℤ).symm
    (simpleOverlapCoordinate G i (borelCharacterMap G chi
      (MonoidAlgebra.single (Multiplicative.ofAdd 1) 1)))

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "CharacterLine: laurent_monomial"

omit [IsAlgClosed K] [CharZero K] in
private theorem laurent_monomial (n : ℤ) :
    (AddMonoidAlgebra.toMultiplicativeAlgEquiv (R := K) K ℤ)
      (LaurentPolynomial.T n) = MonoidAlgebra.single (Multiplicative.ofAdd n) 1 := by
  simp only [AddMonoidAlgebra.toMultiplicativeAlgEquiv, AlgEquiv.coe_mk,
    AddMonoidAlgebra.toMultiplicative, Equiv.coe_fn_mk, LaurentPolynomial.T,
    AddMonoidAlgebra.coeff_single, Finsupp.mapDomain_single, MonoidAlgebra.ofCoeff_single]

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "CharacterLine: characterOverlapLaurent_odd"

/-- The same odd character supplies the transition of degree p minus one. -/
theorem characterOverlapLaurent_odd (p : ℕ) (hp : Odd p) (i : G.rootBase.support) :
    characterOverlapLaurent G i (G.oddRootCharacter p) =
      LaurentPolynomial.T ((p - 1 : ℕ) : ℤ) := by
  apply (AddMonoidAlgebra.toMultiplicativeAlgEquiv (R := K) K ℤ).injective
  rw [characterOverlapLaurent, AlgEquiv.apply_symm_apply,
    simpleOverlapCoordinate_character G p hp, laurent_monomial]

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "CharacterLine: characterSection"

private def characterSection (i : G.rootBase.support) (chi : G.characters) :
    Γ(overlap K, ⊤) :=
  (Scheme.ΓSpecIso (.of (LaurentPolynomial K))).inv (characterOverlapLaurent G i chi)


end SchubertGeometry.ProjectiveLine
