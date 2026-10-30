import OrbitComplexity.SchubertGeometry.Frobenius.Determinant.Power
import OrbitComplexity.SchubertGeometry.LineBundles.Characters.CharacterModules

/-! # The line of an integral power of the fixed positive character -/

noncomputable section
namespace SchubertGeometry.ProjectiveLine
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits ReductiveGroups TauCeti
universe u

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

private theorem power_borel_coefficient (N : ℕ) :
    borelCharacterMap G (G.positiveRootCharacter ^ N)
        (MonoidAlgebra.single (Multiplicative.ofAdd 1) 1) =
      borelCharacterMap G G.positiveRootCharacter
        (MonoidAlgebra.single (Multiplicative.ofAdd 1) 1) ^ N := by
  have h := DeterminantSection.positiveDetPower_borel_restriction G N
  rw [DeterminantSection.positiveDetPower, map_pow,
    DeterminantSection.positiveDet_borel_restriction] at h
  exact h.symm

private theorem positive_laurent (i : G.rootBase.support) :
    characterOverlapLaurent G i G.positiveRootCharacter = LaurentPolynomial.T (2 : ℤ) := by
  have hchi : G.oddRootCharacter 3 = G.positiveRootCharacter := by
    change G.positiveRootCharacter ^ 1 = G.positiveRootCharacter
    exact pow_one _
  have h := characterOverlapLaurent_odd G 3 (by decide) i
  rw [hchi] at h
  exact h

private theorem power_laurent (N : ℕ) (i : G.rootBase.support) :
    characterOverlapLaurent G i (G.positiveRootCharacter ^ N) =
      LaurentPolynomial.T ((2 * N : ℕ) : ℤ) := by
  have hpow : characterOverlapLaurent G i (G.positiveRootCharacter ^ N) =
      characterOverlapLaurent G i G.positiveRootCharacter ^ N := by
    unfold characterOverlapLaurent
    rw [power_borel_coefficient G N, map_pow, map_pow]
  rw [hpow, positive_laurent G i, LaurentPolynomial.T_pow]
  congr 1
  simp only [Nat.cast_mul, Nat.cast_ofNat, mul_comm]

private theorem power_transition (N : ℕ) (i : G.rootBase.support) :
    SchubertGeometry.ProjectiveLine.characterModuleSection G i (G.positiveRootCharacter ^ N) =
      (Scheme.ΓSpecIso (.of (LaurentPolynomial K))).inv
        (LaurentPolynomial.T ((2 * N : ℕ) : ℤ)) :=
  (SchubertGeometry.ProjectiveLine.characterModuleSection_eq G i (G.positiveRootCharacter ^
    N)).trans
    (congrArg (Scheme.ΓSpecIso (.of (LaurentPolynomial K))).inv (power_laurent G N i))

/-- The fixed-character power gives the line of degree 2N before choosing a prime. -/
def characterPowerLineIso (N : ℕ) (i : G.rootBase.support) :
    SchubertGeometry.ProjectiveLine.characterLineModule G i (G.positiveRootCharacter ^ N) ≅
      SchubertGeometry.ProjectiveLine.projectiveTransitionModule K (2 * N) :=
  pullback.congrHom rfl (by rw [power_transition G N i]; rfl)

end SchubertGeometry.ProjectiveLine
