import Mathlib.LinearAlgebra.RootSystem.Base
import Mathlib.LinearAlgebra.RootSystem.WeylGroup

/-!
# The integral Weyl action on the root lattice

The natural Weyl action preserves the integer span of the roots. Its restriction
is an integer-linear representation, with the usual Cartan formula on simple roots.
-/

noncomputable section
namespace ReductiveGroups
variable {ι R M N : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N)

private theorem weyl_mem_rootSpan (w : P.weylGroup) {x : M} (hx : x ∈ P.rootSpan ℤ) :
    w • x ∈ P.rootSpan ℤ := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    rw [P.weylGroup_apply_root]
    exact (P.rootSpanMem ℤ _).property
  | zero => simpa only [smul_zero] using (P.rootSpan ℤ).zero_mem
  | add x y _ _ ihx ihy =>
    rw [smul_add]
    exact (P.rootSpan ℤ).add_mem ihx ihy
  | smul n x _ ih =>
    change ((P.weylGroupRootRep w).restrictScalars ℤ) (n • x) ∈ P.rootSpan ℤ
    rw [map_smul]
    exact (P.rootSpan ℤ).smul_mem n ih

private def rootLatticeEquiv (w : P.weylGroup) : P.rootSpan ℤ ≃ₗ[ℤ] P.rootSpan ℤ where
  toFun x := ⟨w • x.val, weyl_mem_rootSpan P w x.property⟩
  invFun x := ⟨w⁻¹ • x.val, weyl_mem_rootSpan P w⁻¹ x.property⟩
  left_inv x := Subtype.ext (inv_smul_smul w x.val)
  right_inv x := Subtype.ext (smul_inv_smul w x.val)
  map_add' x y := Subtype.ext (smul_add w x.val y.val)
  map_smul' n x := Subtype.ext (((P.weylGroupRootRep w).restrictScalars ℤ).map_smul n x.val)

/-- The Weyl action restricts to integer-linear automorphisms of the integral root span. -/
def rootLatticeAction : P.weylGroup →* (P.rootSpan ℤ ≃ₗ[ℤ] P.rootSpan ℤ) where
  toFun := rootLatticeEquiv P
  map_one' := by
    apply LinearEquiv.ext
    intro x
    exact Subtype.ext (one_smul P.weylGroup x.val)
  map_mul' a b := by
    apply LinearEquiv.ext
    intro x
    exact Subtype.ext (mul_smul a b x.val)

/-- The restricted integral action has the original Weyl action as its ambient value. -/
theorem rootLatticeAction_coe (w : P.weylGroup) (x : P.rootSpan ℤ) :
    (rootLatticeAction P w x : M) = w • x.val := rfl

/-- The restricted action sends each integral root to its Weyl-permuted root. -/
theorem rootLatticeAction_root (w : P.weylGroup) (i : ι) :
    rootLatticeAction P w (P.rootSpanMem ℤ i) =
      P.rootSpanMem ℤ (P.weylGroupToPerm w i) :=
  Subtype.ext (P.weylGroup_apply_root w i)

variable [CharZero R] [P.IsCrystallographic]

omit [CharZero R] in
/-- Integral reflection on a root uses the integer Cartan pairing. -/
theorem rootLatticeAction_reflect_root (i j : ι) :
    rootLatticeAction P (RootPairing.weylGroup.ofIdx P i) (P.rootSpanMem ℤ j) =
      P.rootSpanMem ℤ j - P.pairingIn ℤ j i • P.rootSpanMem ℤ i := by
  apply Subtype.ext
  change P.reflection i (P.root j) = P.root j - P.pairingIn ℤ j i • P.root i
  exact P.reflection_apply_root' ℤ

/-- Simple reflections act on the integral simple-root basis by their integer Cartan matrices. -/
theorem rootLatticeAction_simple_basis (b : P.Base) (i j : b.support) :
    rootLatticeAction P (RootPairing.weylGroup.ofIdx P i.val) (b.toWeightBasisInt j) =
      b.toWeightBasisInt j - P.pairingIn ℤ j.val i.val • b.toWeightBasisInt i := by
  have hb (k : b.support) : b.toWeightBasisInt k = P.rootSpanMem ℤ k.val :=
    Subtype.ext (b.coe_toWeightBasisInt_apply k)
  simpa only [hb] using rootLatticeAction_reflect_root P i.val j.val

end ReductiveGroups
