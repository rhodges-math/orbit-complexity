import Batteries.Tactic.Lint
import OrbitComplexity.BruhatIntervals.Realizations.RootForms
import OrbitComplexity.ReductiveGroups.Roots.Coxeter.RootLatticeAction
import OrbitComplexity.ReductiveGroups.Roots.Characters.PositivePairing
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.Basic.Real.Basic

/-! # Weyl actions on real root coordinates

The integral root-lattice action extends by scalars to the reals. Its simple-root matrices
and root permutation agree with the original Weyl action.
-/

open scoped TensorProduct

noncomputable section
namespace SchubertOrbits

variable {ι K M N : Type*} [Field K] [CharZero K]
  [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
  {P : RootPairing ι K M N} (b : P.Base)

/-- The integral Weyl action extends to real simple-root coordinates. -/
def rootCoordinateAction : P.weylGroup →* ((b.support →₀ ℝ) ≃ₗ[ℝ] (b.support →₀ ℝ)) where
  toFun w := ((b.toWeightBasisInt.baseChange ℝ).repr).symm.trans
    (((ReductiveGroups.rootLatticeAction P w).baseChange ℤ ℝ).trans
      (b.toWeightBasisInt.baseChange ℝ).repr)
  map_one' := by
    simp only [map_one, LinearEquiv.baseChange_one]
    apply LinearEquiv.ext
    intro x
    change (b.toWeightBasisInt.baseChange ℝ).repr
      ((b.toWeightBasisInt.baseChange ℝ).repr.symm x) = x
    exact (b.toWeightBasisInt.baseChange ℝ).repr.apply_symm_apply x
  map_mul' a c := by
    simp only [map_mul, LinearEquiv.baseChange_mul]
    apply LinearEquiv.ext
    intro x
    simp only [LinearEquiv.trans_apply, LinearEquiv.mul_apply,
      LinearEquiv.symm_apply_apply]

/-- A simple Weyl reflection has its integer Cartan matrix after real scalar extension. -/
theorem rootCoordinateAction_simple [P.IsCrystallographic] (i j : b.support) :
    rootCoordinateAction b (RootPairing.weylGroup.ofIdx P i)
      (Finsupp.single j 1) = Finsupp.single j 1 -
        (P.pairingIn ℤ j i : ℝ) • Finsupp.single i 1 := by
  simp only [rootCoordinateAction, MonoidHom.coe_mk, OneHom.coe_mk,
    LinearEquiv.trans_apply, Module.Basis.repr_symm_single_one,
    Module.Basis.baseChange_apply, LinearEquiv.baseChange_tmul,
    ReductiveGroups.rootLatticeAction_simple_basis]
  rw [TensorProduct.tmul_sub, TensorProduct.tmul_smul]
  simp only [map_sub, map_zsmul, ← Module.Basis.baseChange_apply, Module.Basis.repr_self]
  rw [Int.cast_smul_eq_zsmul]

/-- Real root coordinates are the scalar extensions of integral simple-root coordinates. -/
def realRoot (r : ι) : b.support →₀ ℝ :=
  (b.toWeightBasisInt.baseChange ℝ).repr (1 ⊗ₜ[ℤ] P.rootSpanMem ℤ r)

/-- Real coordinate entries are the integer root coordinates cast into the reals. -/
theorem realRoot_apply (r : ι) (j : b.support) :
    realRoot b r j = (b.toWeightBasisInt.repr (P.rootSpanMem ℤ r) j : ℝ) := by
  simp [realRoot, Module.Basis.baseChange_repr_tmul, zsmul_eq_mul]

/-- The extended Weyl action transports real roots by the root permutation. -/
theorem rootCoordinateAction_root (w : P.weylGroup) (r : ι) :
    rootCoordinateAction b w (realRoot b r) = realRoot b (P.weylGroupToPerm w r) := by
  simp only [rootCoordinateAction, MonoidHom.coe_mk, OneHom.coe_mk, realRoot,
    LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, LinearEquiv.baseChange_tmul,
    ReductiveGroups.rootLatticeAction_root]

/-- Simple real roots are the corresponding coordinate basis vectors. -/
theorem realRoot_simple (i : b.support) : realRoot b (i : ι) = Finsupp.single i 1 := by
  have hb : P.rootSpanMem ℤ (i : ι) = b.toWeightBasisInt i :=
    Subtype.ext (b.coe_toWeightBasisInt_apply i).symm
  rw [realRoot, hb, ← Module.Basis.baseChange_apply, Module.Basis.repr_self]

variable [Fintype ι] [P.IsCrystallographic]

/-- The real vector twice rho is the sum of the unnormalized positive roots. -/
def realTwoRho : b.support →₀ ℝ := by
  classical
  exact ∑ r ∈ Finset.univ.filter b.IsPos, realRoot b r

omit [Fintype ι] in
private theorem rootCoordinateAction_reflect_root (i r : ι) :
    rootCoordinateAction b (RootPairing.weylGroup.ofIdx P i) (realRoot b r) =
      realRoot b r - (P.pairingIn ℤ r i : ℝ) • realRoot b i := by
  simp only [rootCoordinateAction, MonoidHom.coe_mk, OneHom.coe_mk, realRoot,
    LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, LinearEquiv.baseChange_tmul,
    ReductiveGroups.rootLatticeAction_reflect_root]
  rw [TensorProduct.tmul_sub, TensorProduct.tmul_smul]
  simp only [map_sub, map_zsmul, Int.cast_smul_eq_zsmul]

/-- A simple reflection subtracts twice its unnormalized root from twice rho. -/
theorem rootCoordinateAction_twoRho [P.IsReduced] (i : b.support) :
    rootCoordinateAction b (RootPairing.weylGroup.ofIdx P i) (realTwoRho b) =
      realTwoRho b - (2 : ℝ) • realRoot b i := by
  classical
  have hsum : (∑ r ∈ Finset.univ.filter b.IsPos, (P.pairingIn ℤ r i.val : ℝ)) = 2 := by
    exact_mod_cast ReductiveGroups.positive_pairing_sum P b i
  calc
    _ = ∑ r ∈ Finset.univ.filter b.IsPos,
        (realRoot b r - (P.pairingIn ℤ r i.val : ℝ) • realRoot b i.val) := by
      simp only [realTwoRho, map_sum, rootCoordinateAction_reflect_root]
    _ = realTwoRho b -
        (∑ r ∈ Finset.univ.filter b.IsPos, (P.pairingIn ℤ r i.val : ℝ)) •
          realRoot b i.val := by
      rw [Finset.sum_sub_distrib, ← Finset.sum_smul]
      rfl
    _ = _ := by rw [hsum]

private theorem rootLength_weyl (w : P.weylGroup) (r : ι) :
    (P.posRootForm ℤ).rootLength (P.weylGroupToPerm w r) =
      (P.posRootForm ℤ).rootLength r := by
  apply FaithfulSMul.algebraMap_injective ℤ K
  simp only [RootPairing.RootPositiveForm.algebraMap_rootLength]
  rw [← P.weylGroup_apply_root w r]
  exact RootPairing.InvariantForm.apply_weylGroup_smul
    (B := (P.posRootForm ℤ).toInvariantForm) P w (P.root r) (P.root r)

/-- Root coordinates normalized to have squared length one. -/
def normalizedRoot (r : ι) : b.support →₀ ℝ :=
  (Real.sqrt ((P.posRootForm ℤ).rootLength r : ℝ))⁻¹ • realRoot b r

/-- The normalized roots at simple indices are the normalized simple coordinate vectors. -/
theorem normalizedRoot_simple (i : b.support) :
    normalizedRoot b (i : ι) = BruhatIntervals.normalizedSimpleRoot b i := by
  simp only [normalizedRoot, realRoot_simple, BruhatIntervals.normalizedSimpleRoot]

/-- The real Weyl action permutes normalized roots by the original root permutation. -/
theorem rootCoordinateAction_normalized (w : P.weylGroup) (r : ι) :
    rootCoordinateAction b w (normalizedRoot b r) =
      normalizedRoot b (P.weylGroupToPerm w r) := by
  simp only [normalizedRoot, map_smul, rootCoordinateAction_root, rootLength_weyl]

/-- The normalized root coordinates are the scaled integral coordinates. -/
theorem normalizedRoot_apply (r : ι) (j : b.support) :
    normalizedRoot b r j = (Real.sqrt ((P.posRootForm ℤ).rootLength r : ℝ))⁻¹ *
      (b.toWeightBasisInt.repr (P.rootSpanMem ℤ r) j : ℝ) := by
  rw [normalizedRoot, Finsupp.smul_apply, realRoot_apply]
  rfl

end SchubertOrbits
end
