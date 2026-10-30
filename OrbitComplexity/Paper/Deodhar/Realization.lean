import OrbitComplexity.Paper.Deodhar.RootActions
import OrbitComplexity.BruhatIntervals.Realizations.RootForms
import OrbitComplexity.BruhatIntervals.Realizations.Basic
import OrbitComplexity.BruhatIntervals.Realizations.Sign
import Mathlib.Data.Finsupp.Order
import Batteries.Tactic.Lint
import OrbitComplexity.ReductiveGroups.Roots.Coxeter.PresentationWordPropertyCoxeter
import TauCeti.LinearAlgebra.RootSystem.BraidRelation

/-! # The normalized Weyl realization

The integral Weyl action extends to real simple-root coordinates. Its simple generators
act by the normalized root reflections, and the Gram entries equal the Coxeter cosine entries.
-/

namespace SchubertOrbits
noncomputable section
variable {ι K M N : Type*} [Field K] [CharZero K]
  [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
  {P : RootPairing ι K M N} [Fintype ι] [P.IsCrystallographic]
  (b : P.Base)

private theorem action_reflection (i : b.support) (x : b.support →₀ ℝ) :
    rootCoordinateAction b (RootPairing.weylGroup.ofIdx P i) x =
      x - (2 * BruhatIntervals.rootPairingForm b
        (BruhatIntervals.normalizedSimpleRoot b i) x) •
          BruhatIntervals.normalizedSimpleRoot b i := by
  have h : (rootCoordinateAction b (RootPairing.weylGroup.ofIdx P i)).toLinearMap =
      LinearMap.id - ((2 : ℝ) • (BruhatIntervals.rootPairingForm b
        (BruhatIntervals.normalizedSimpleRoot b i))).smulRight
          (BruhatIntervals.normalizedSimpleRoot b i) := by
    apply (Finsupp.basisSingleOne : Module.Basis b.support ℝ (b.support →₀ ℝ)).ext
    intro j
    change rootCoordinateAction b (RootPairing.weylGroup.ofIdx P i)
      (Finsupp.single j 1) = Finsupp.single j 1 -
        (2 * BruhatIntervals.rootPairingForm b (BruhatIntervals.normalizedSimpleRoot b i)
          (Finsupp.single j 1)) • BruhatIntervals.normalizedSimpleRoot b i
    rw [rootCoordinateAction_simple, BruhatIntervals.normalizedSimpleRoot_reflection]
  exact congrArg (fun f : (b.support →₀ ℝ) →ₗ[ℝ] (b.support →₀ ℝ) => f x) h

variable [P.IsReduced]

/-- The Weyl group has its normalized real geometric root realization. -/
def weylRealization : BruhatIntervals.Realization (ReductiveGroups.weylCoxeterSystem b)
    (V := b.support →₀ ℝ) where
  simpleRoot := BruhatIntervals.normalizedSimpleRoot b
  root_independent := BruhatIntervals.normalizedSimpleRoot_independent b
  form := BruhatIntervals.rootPairingForm b
  form_isSymm := BruhatIntervals.rootPairingForm_isSymm b
  form_root i j := by
    rw [ReductiveGroups.simpleCoxeterMatrix_apply,
      RootPairing.weylGroup.orderOf_ofIdx_mul_ofIdx_eq_coxeterMatrixOfBase P b i j]
    exact BruhatIntervals.normalizedSimpleRoot_pairing b i j
  action := rootCoordinateAction b
  action_simple i x := by
    rw [ReductiveGroups.weylCoxeterSystem_simple]
    exact action_reflection b i x

private theorem positive_root_form_pos
    {S W V : Type*} [Group W] {matrix : CoxeterMatrix S}
    {cs : CoxeterSystem matrix W} [AddCommGroup V] [Module ℝ V]
    (R : BruhatIntervals.Realization cs (V := V)) (weight : V)
    (hchamber : ∀ i, 0 < R.form (R.simpleRoot i) weight)
    {x : V} (hx : x ∈ R.positiveRoots) : 0 < R.form x weight := by
  classical
  obtain ⟨hroot, coefficients, hc, hcoefficients⟩ := R.mem_positiveRoots.mp hx
  have hcne : coefficients ≠ 0 := by
    intro hz
    apply R.root_ne_zero hroot
    rw [← hcoefficients, hz]
    simp
  have hpair : R.form x weight =
      coefficients.sum (fun i a => a * R.form (R.simpleRoot i) weight) := by
    rw [← hcoefficients, Finsupp.linearCombination_apply]
    simp only [Finsupp.sum, map_sum, map_smul, LinearMap.sum_apply,
      LinearMap.smul_apply, smul_eq_mul]
  rw [hpair]
  refine Finsupp.sum_pos ?_ hcne
  intro i hi
  exact mul_pos (lt_of_le_of_ne (hc i) (Ne.symm (Finsupp.mem_support_iff.mp hi)))
    (hchamber i)

private theorem chamber_regular
    {S W V : Type*} [Group W] {matrix : CoxeterMatrix S}
    {cs : CoxeterSystem matrix W} [AddCommGroup V] [Module ℝ V]
    (R : BruhatIntervals.Realization cs (V := V)) (weight : V)
    (hchamber : ∀ i, 0 < R.form (R.simpleRoot i) weight)
    (w : W) (α : {x : V // x ∈ R.positiveRoots}) :
    R.form α.val (R.action w weight) ≠ 0 := by
  have hroot := R.action_mem_roots w⁻¹ α.property.1
  have hpair : R.form α.val (R.action w weight) =
      R.form (R.action w⁻¹ α.val) weight := by
    have hinvariant := R.action_form w (R.action w⁻¹ α.val) weight
    simpa only [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel,
      map_one, LinearEquiv.coe_one, id_eq] using hinvariant
  rw [hpair]
  rcases R.root_sign hroot with hp | hn
  · exact ne_of_gt (positive_root_form_pos R weight hchamber hp)
  · intro hz
    have hp := positive_root_form_pos R weight hchamber hn
    exact (lt_irrefl (0 : ℝ)) (by
      simpa only [map_neg, LinearMap.neg_apply, hz, neg_zero] using hp)

/-- Twice rho has strictly positive pairing with every normalized simple root. -/
theorem realTwoRho_simple_pos (i : b.support) :
    0 < (weylRealization b).form ((weylRealization b).simpleRoot i) (realTwoRho b) := by
  have haction := (weylRealization b).action_simple i (realTwoRho b)
  change rootCoordinateAction b ((ReductiveGroups.weylCoxeterSystem b).simple i)
      (realTwoRho b) = realTwoRho b -
        (2 * (weylRealization b).form ((weylRealization b).simpleRoot i)
          (realTwoRho b)) • (weylRealization b).simpleRoot i at haction
  rw [ReductiveGroups.weylCoxeterSystem_simple, rootCoordinateAction_twoRho,
    realRoot_simple] at haction
  have hcoordinate := congrArg (fun x : b.support →₀ ℝ => x i) haction
  have heq : (realTwoRho b) i - 2 = (realTwoRho b) i -
      (2 * (weylRealization b).form ((weylRealization b).simpleRoot i) (realTwoRho b)) *
        (Real.sqrt ((P.posRootForm ℤ).rootLength i : ℝ))⁻¹ := by
    simpa only [Finsupp.sub_apply, Finsupp.smul_apply, Finsupp.single_eq_same,
      smul_eq_mul, weylRealization, BruhatIntervals.normalizedSimpleRoot, mul_one] using
      hcoordinate
  have hlength : 0 < ((P.posRootForm ℤ).rootLength i : ℝ) := by
    exact_mod_cast (P.posRootForm ℤ).rootLength_pos (i : ι)
  have hinv : 0 < (Real.sqrt ((P.posRootForm ℤ).rootLength i : ℝ))⁻¹ :=
    inv_pos.mpr (Real.sqrt_pos.mpr hlength)
  have hproduct :
      (2 * (weylRealization b).form ((weylRealization b).simpleRoot i) (realTwoRho b)) *
        (Real.sqrt ((P.posRootForm ℤ).rootLength i : ℝ))⁻¹ = 2 := by linarith
  have hpositive : 0 <
      2 * (weylRealization b).form ((weylRealization b).simpleRoot i) (realTwoRho b) :=
    (mul_pos_iff_of_pos_right hinv).mp (by rw [hproduct]; norm_num)
  linarith

/-- Every positive-root pairing with a Weyl translate of twice rho is nonzero. -/
theorem realTwoRho_regular (w : P.weylGroup)
    (α : {x : b.support →₀ ℝ // x ∈ (weylRealization b).positiveRoots}) :
    (weylRealization b).form α.val ((weylRealization b).action w (realTwoRho b)) ≠ 0 := by
  exact @chamber_regular b.support P.weylGroup (b.support →₀ ℝ) inferInstance
    (ReductiveGroups.simpleCoxeterMatrix b) (ReductiveGroups.weylCoxeterSystem b)
    inferInstance inferInstance (weylRealization b) (realTwoRho b)
    (realTwoRho_simple_pos b) w α

end
end SchubertOrbits
