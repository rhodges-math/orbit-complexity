import OrbitComplexity.SchubertGeometry.Deodhar.ParameterProduct
import OrbitComplexity.BruhatIntervals.Words.Prefix
import Mathlib.Algebra.MvPolynomial.Equiv

/-! # Parameters of the empty word prefix

The empty prefix has no selected coordinates, so its parameter variety is the base spectrum.
-/

open CategoryTheory AlgebraicGeometry GroupActions BruhatIntervals
noncomputable section
namespace SchubertGeometry
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroups.ReductiveGroupData K) {word : List G.rootBase.support}
  (expression : Subexpression word)

private instance initialIndex_empty : IsEmpty (deodharIndex G (expression.take 0)) where
  false j := by
    have hj := j.down.val.isLt
    simp only [List.length_take, Nat.zero_min, Nat.not_lt_zero] at hj

private theorem initial_open : deodharParameterOpen G (expression.take 0) = ⊤ := by
  change PrimeSpectrum.basicOpen (∏ j ∈ deodharEqualPositions G (expression.take 0),
    (MvPolynomial.X j : MvPolynomial (deodharIndex G (expression.take 0)) K)) = ⊤
  rw [Finset.eq_empty_of_isEmpty (deodharEqualPositions G (expression.take 0))]
  simp only [Finset.prod_empty, PrimeSpectrum.basicOpen_one]

/-- The empty prefix parameter variety is the spectrum of the base field. -/
def deodharInitialIso :
    (deodharParameters G (expression.take 0)).toOver ≅ (affineVariety K K).toOver := by
  change ((affineSpaceVariety K (deodharIndex G (expression.take 0))).openSubvariety
    (deodharParameterOpen G (expression.take 0))).toOver ≅ _
  rw [initial_open]
  let e : ((affineSpaceVariety K (deodharIndex G (expression.take 0))).openSubvariety
      (⊤ : (affineSpaceVariety K (deodharIndex G (expression.take 0))).scheme.Opens)).toOver ≅
        (affineSpaceVariety K (deodharIndex G (expression.take 0))).toOver :=
    Over.isoMk (affineSpaceVariety K (deodharIndex G (expression.take 0))).scheme.topIso (by rfl)
  exact e ≪≫ ((algSpec (CommRingCat.of K)).mapIso
    (CommAlgCat.isoMk (MvPolynomial.isEmptyAlgEquiv K
      (deodharIndex G (expression.take 0)))).op).symm

end SchubertGeometry
