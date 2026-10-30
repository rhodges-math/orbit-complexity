import TauCeti.LinearAlgebra.RootSystem.Coxeter.Matrix
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.RootSystem.Finite.CanonicalBilinear
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! # Real forms of crystallographic root systems

The positive integral root form extends to real simple-root coordinates. Dividing simple
roots by their positive lengths gives independent vectors with the cosine Gram matrix
of the Coxeter exponents.

## Main results

* `normalizedSimpleRoot_independent`: normalized simple coordinates remain independent.
* `normalizedSimpleRoot_pairing`: their form is the Coxeter cosine Gram matrix.
-/

namespace BruhatIntervals

private theorem normalized_pairing {a b c : ℝ} {p : ℤ}
    (ha : 0 < a) (hb : 0 < b) (hc : c ≤ 0)
    (hp : p ∈ ({0, 1, 2, 3} : Set ℤ)) (heq : 4 * c ^ 2 = p * a * b) :
    c / (Real.sqrt a * Real.sqrt b) =
      -Real.cos (Real.pi / (TauCeti.coxeterOrder p : ℝ)) := by
  let d := Real.sqrt a * Real.sqrt b
  have hd : 0 < d := mul_pos (Real.sqrt_pos.2 ha) (Real.sqrt_pos.2 hb)
  have hd2 : d ^ 2 = a * b := by
    rw [mul_pow, Real.sq_sqrt ha.le, Real.sq_sqrt hb.le]
  have hnorm : 4 * (c / d) ^ 2 = (p : ℝ) := by
    rw [div_pow, ← mul_div_assoc, heq, hd2]
    field_simp
  have hsign : c / d ≤ 0 := div_nonpos_of_nonpos_of_nonneg hc hd.le
  have hp0 : 0 ≤ (p : ℝ) := by
    rcases hp with rfl | rfl | rfl | rfl <;> norm_num
  have hroot := Real.sq_sqrt hp0
  have hfactor : (2 * (c / d) + Real.sqrt (p : ℝ)) *
      (2 * (c / d) - Real.sqrt (p : ℝ)) = 0 := by nlinarith
  have hvalue : c / d = -Real.sqrt (p : ℝ) / 2 := by
    rcases mul_eq_zero.mp hfactor with h | h <;> linarith [Real.sqrt_nonneg (p : ℝ)]
  change c / d = _
  rw [hvalue]
  rcases hp with rfl | rfl | rfl | rfl <;>
    norm_num [TauCeti.coxeterOrder_zero, TauCeti.coxeterOrder_one,
      TauCeti.coxeterOrder_two, TauCeti.coxeterOrder_three, Real.cos_pi_div_two,
      Real.cos_pi_div_three, Real.cos_pi_div_four, Real.cos_pi_div_six] <;> ring

noncomputable section

variable {ι K M N : Type*} [Field K] [CharZero K]
  [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
  {P : RootPairing ι K M N} [Fintype ι] [P.IsCrystallographic]
  (b : P.Base)

/-- Extend the integral root form to real coordinates in the simple-root basis. -/
def rootPairingForm : LinearMap.BilinForm ℝ (b.support →₀ ℝ) :=
  Finsupp.linearCombination ℝ (fun i => Finsupp.linearCombination ℝ (fun j =>
    ((P.posRootForm ℤ).posForm (P.rootSpanMem ℤ i) (P.rootSpanMem ℤ j) : ℝ)))

/-- The real root form on simple coordinate vectors is the integral root pairing. -/
theorem rootPairingForm_single (i j : b.support) :
    rootPairingForm b (Finsupp.single i 1) (Finsupp.single j 1) =
      ((P.posRootForm ℤ).posForm (P.rootSpanMem ℤ i) (P.rootSpanMem ℤ j) : ℝ) := by
  simp only [rootPairingForm, Finsupp.linearCombination_single, one_smul]

/-- The real extension of the integral root form is symmetric. -/
theorem rootPairingForm_isSymm : (rootPairingForm b).IsSymm := by
  apply (LinearMap.BilinForm.isSymm_iff_basis Finsupp.basisSingleOne).mpr
  intro i j
  change rootPairingForm b (Finsupp.single i 1) (Finsupp.single j 1) =
    rootPairingForm b (Finsupp.single j 1) (Finsupp.single i 1)
  rw [rootPairingForm_single, rootPairingForm_single]
  exact congrArg (fun z : ℤ => (z : ℝ))
    (((P.posRootForm ℤ).isSymm_posForm).eq (P.rootSpanMem ℤ i) (P.rootSpanMem ℤ j))

private theorem two_mul_integral (i j : ι) :
    2 * (P.posRootForm ℤ).posForm (P.rootSpanMem ℤ i) (P.rootSpanMem ℤ j) =
      P.pairingIn ℤ i j *
        (P.posRootForm ℤ).posForm (P.rootSpanMem ℤ j) (P.rootSpanMem ℤ j) := by
  apply FaithfulSMul.algebraMap_injective ℤ K
  simp only [map_mul, map_ofNat, RootPairing.RootPositiveForm.algebraMap_posForm,
    RootPairing.algebraMap_pairingIn]
  exact (P.posRootForm ℤ).two_mul_apply_root_root i j

/-- Each simple-root coordinate vector is normalized by its positive root length. -/
def normalizedSimpleRoot (i : b.support) : b.support →₀ ℝ :=
  (Real.sqrt ((P.posRootForm ℤ).rootLength i : ℝ))⁻¹ • Finsupp.single i 1

/-- Positive root-length normalization preserves independence of the simple coordinates. -/
theorem normalizedSimpleRoot_independent : LinearIndependent ℝ (normalizedSimpleRoot b) := by
  have hpos (i : b.support) : 0 < ((P.posRootForm ℤ).rootLength i : ℝ) := by
    exact_mod_cast (P.posRootForm ℤ).rootLength_pos (i : ι)
  let w : b.support → ℝˣ := fun i => Units.mk0
    (Real.sqrt ((P.posRootForm ℤ).rootLength i : ℝ))⁻¹
    (inv_ne_zero (ne_of_gt (Real.sqrt_pos.2 (hpos i))))
  exact (Finsupp.linearIndependent_single_one (R := ℝ) (ι := b.support)).units_smul w

/-- Normalized simple roots have the cosine Gram matrix of their Coxeter exponents. -/
theorem normalizedSimpleRoot_pairing (i j : b.support) :
    rootPairingForm b (normalizedSimpleRoot b i) (normalizedSimpleRoot b j) =
      -Real.cos (Real.pi / (TauCeti.coxeterMatrixOfBase P b i j : ℝ)) := by
  let B := P.posRootForm ℤ
  let ri := P.rootSpanMem ℤ (i : ι)
  let rj := P.rootSpanMem ℤ (j : ι)
  have hi : 0 < (B.rootLength i : ℝ) := by exact_mod_cast B.rootLength_pos i
  have hj : 0 < (B.rootLength j : ℝ) := by exact_mod_cast B.rootLength_pos j
  have hform : rootPairingForm b (normalizedSimpleRoot b i) (normalizedSimpleRoot b j) =
      (B.posForm ri rj : ℝ) / (Real.sqrt (B.rootLength i : ℝ) *
        Real.sqrt (B.rootLength j : ℝ)) := by
    simp only [normalizedSimpleRoot, LinearMap.BilinForm.smul_left,
      LinearMap.BilinForm.smul_right, rootPairingForm_single]
    dsimp only [B, ri, rj]
    ring
  rw [hform]
  by_cases hij : i = j
  · subst j
    rw [(TauCeti.coxeterMatrixOfBase P b).diagonal]
    change (B.rootLength i : ℝ) /
      (Real.sqrt (B.rootLength i : ℝ) * Real.sqrt (B.rootLength i : ℝ)) = _
    rw [Real.mul_self_sqrt hi.le, div_self hi.ne']
    simp only [Nat.cast_one, div_one, Real.cos_pi, neg_neg]
  · rw [TauCeti.coxeterMatrixOfBase_apply]
    apply normalized_pairing hi hj
    · exact_mod_cast (B.posForm_apply_root_root_le_zero_iff (i := (i : ι))
        (j := (j : ι))).2 (b.cartanMatrix_le_zero_of_ne i j hij)
    · exact TauCeti.cartanMatrix_mul_cartanMatrix_mem_of_ne P b hij
    · have hsym : B.posForm rj ri = B.posForm ri rj := B.isSymm_posForm.eq rj ri
      have hleft := two_mul_integral (P := P) (i : ι) (j : ι)
      have hright := two_mul_integral (P := P) (j : ι) (i : ι)
      have heq : 4 * (B.posForm ri rj) ^ 2 =
          (b.cartanMatrix i j * b.cartanMatrix j i) * B.rootLength i * B.rootLength j := by
        calc
          _ = (2 * B.posForm ri rj) * (2 * B.posForm rj ri) := by rw [hsym]; ring
          _ = (P.pairingIn ℤ i j * B.rootLength j) *
              (P.pairingIn ℤ j i * B.rootLength i) := by
                dsimp only [B, ri, rj, RootPairing.RootPositiveForm.rootLength]
                rw [hleft, hright]
          _ = _ := by
            change _ = (P.pairingIn ℤ i j * P.pairingIn ℤ j i) *
              B.rootLength i * B.rootLength j
            ring
      exact_mod_cast heq

/-- Reflection in a normalized simple root has its Cartan coefficient on every basis vector. -/
theorem normalizedSimpleRoot_reflection (i j : b.support) :
    Finsupp.single j (1 : ℝ) -
      (2 * rootPairingForm b (normalizedSimpleRoot b i) (Finsupp.single j 1)) •
        normalizedSimpleRoot b i =
      Finsupp.single j 1 - (P.pairingIn ℤ j i : ℝ) • Finsupp.single i 1 := by
  let B := P.posRootForm ℤ
  have hi : 0 < (B.rootLength i : ℝ) := by exact_mod_cast B.rootLength_pos i
  have hx : Real.sqrt (B.rootLength i : ℝ) ≠ 0 := (Real.sqrt_pos.2 hi).ne'
  have hc : 2 * (B.posForm (P.rootSpanMem ℤ i) (P.rootSpanMem ℤ j) : ℝ) =
      (P.pairingIn ℤ j i : ℝ) * (B.rootLength i : ℝ) := by
    have hs : B.posForm (P.rootSpanMem ℤ i) (P.rootSpanMem ℤ j) =
        B.posForm (P.rootSpanMem ℤ j) (P.rootSpanMem ℤ i) :=
      B.isSymm_posForm.eq (P.rootSpanMem ℤ i) (P.rootSpanMem ℤ j)
    rw [hs]
    exact_mod_cast two_mul_integral (P := P) (j : ι) (i : ι)
  have hcoeff : (2 * ((Real.sqrt (B.rootLength i : ℝ))⁻¹ *
      (B.posForm (P.rootSpanMem ℤ i) (P.rootSpanMem ℤ j) : ℝ))) *
        (Real.sqrt (B.rootLength i : ℝ))⁻¹ = (P.pairingIn ℤ j i : ℝ) := by
    field_simp
    rw [Real.sq_sqrt hi.le]
    exact hc.trans (mul_comm _ _)
  simp only [normalizedSimpleRoot, LinearMap.BilinForm.smul_left, rootPairingForm_single,
    smul_smul]
  rw [hcoeff]

end

end BruhatIntervals
