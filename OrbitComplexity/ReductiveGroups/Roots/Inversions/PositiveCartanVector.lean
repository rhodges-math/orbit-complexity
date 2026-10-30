import OrbitComplexity.ReductiveGroups.Roots.Inversions.PositiveRootConnectedSupport
import Mathlib.LinearAlgebra.RootSystem.Finite.Nondegenerate

/-!
# Positive Cartan Vector

The finite root form excludes a nonzero nonnegative simple-coordinate
vector with nonpositive Cartan pairings on its occupied vertices. Unlike
the root-sum obstruction, the vector need not itself be a root. -/

noncomputable section
namespace ReductiveGroups
attribute [local instance] Classical.decEq
open scoped BigOperators

variable {ι R M N : Type*} [CommRing R] [CharZero R] [IsDomain R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [Finite ι] [P.IsCrystallographic]

/-- Positive definiteness of the finite root form forces a positive
Cartan column pairing at some occupied simple coordinate. -/
theorem SimpleCartan.pairing_of_nonnegative_coefficients
    (b : P.Base) (c : b.support → ℤ) (hc : ∀ i, 0 ≤ c i)
    (hne : ∃ i, 0 < c i) :
    ∃ j : b.support, 0 < c j ∧
      0 < ∑ i : b.support, c i * P.pairingIn ℤ (i : ι) (j : ι) := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  let B := P.posRootForm ℤ
  let x : P.rootSpan ℤ := ∑ i : b.support, c i • b.toWeightBasisInt i
  have hb (i : b.support) : b.toWeightBasisInt i = P.rootSpanMem ℤ (i : ι) := by
    apply Subtype.ext
    simp
  have hx : x ≠ 0 := by
    obtain ⟨i, hi⟩ := hne
    intro hz
    have he := congrArg (fun y : P.rootSpan ℤ => b.toWeightBasisInt.repr y i) hz
    simp [x, Finsupp.finsetSum_apply, Finsupp.single_apply] at he
    omega
  have hpair (i j : b.support) :
      2 * B.posForm (b.toWeightBasisInt i) (b.toWeightBasisInt j) =
        P.pairingIn ℤ (i : ι) (j : ι) * B.rootLength (j : ι) := by
    rw [hb i, hb j]
    apply FaithfulSMul.algebraMap_injective ℤ R
    simpa only [map_mul, map_ofNat, RootPairing.RootPositiveForm.algebraMap_posForm,
      RootPairing.algebraMap_pairingIn, RootPairing.RootPositiveForm.algebraMap_rootLength]
      using B.two_mul_apply_root_root (i : ι) (j : ι)
  have hcolumn (j : b.support) :
      2 * B.posForm x (b.toWeightBasisInt j) =
        (∑ i : b.support, c i * P.pairingIn ℤ (i : ι) (j : ι)) *
          B.rootLength (j : ι) := by
    simp only [x, map_sum, LinearMap.sum_apply, map_smul,
      LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    calc
      2 * (c i * B.posForm (b.toWeightBasisInt i) (b.toWeightBasisInt j)) =
          c i * (2 * B.posForm (b.toWeightBasisInt i) (b.toWeightBasisInt j)) := by ring
      _ = c i * (P.pairingIn ℤ (i : ι) (j : ι) * B.rootLength (j : ι)) := by rw [hpair]
      _ = c i * P.pairingIn ℤ (i : ι) (j : ι) * B.rootLength (j : ι) := by ring
  by_contra hnone
  push Not at hnone
  have hnonpos : B.posForm x x ≤ 0 := by
    change B.posForm x (∑ j : b.support, c j • b.toWeightBasisInt j) ≤ 0
    rw [map_sum]
    apply Finset.sum_nonpos
    intro j _
    rw [map_smul, smul_eq_mul]
    by_cases hz : c j = 0
    · simp [hz]
    · have hj : 0 < c j := lt_of_le_of_ne (hc j) (Ne.symm hz)
      have hp := hnone j hj
      have hlen := B.rootLength_pos (j : ι)
      have hjform : B.posForm x (b.toWeightBasisInt j) ≤ 0 := by
        have he := hcolumn j
        have hm := mul_nonpos_of_nonpos_of_nonneg hp hlen.le
        omega
      exact mul_nonpos_of_nonneg_of_nonpos (hc j) hjform
  have hpos : 0 < B.posForm x x := P.posRootForm_posForm_pos_of_ne_zero ℤ hx
  omega

end ReductiveGroups
