import Mathlib.Algebra.Lie.Sl2
import Mathlib.Algebra.Lie.Derivation.Basic
import Mathlib.Algebra.Lie.AdjointAction.Derivation
import Mathlib.RingTheory.Nilpotent.Exp
import Mathlib.Algebra.Algebra.Rat

/-!
# Sl 2 Adjoint Reflection

The adjoint Weyl-word calculation on an `sl₂` triple. -/

noncomputable section

namespace ReductiveGroups

open LieAlgebra

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]

/-- The Lie algebra automorphism `exp (ad x)` of `L`, for an element `x` with nilpotent adjoint
action, over a field of characteristic zero. -/
def nilpotentAdjointExponential (x : L) (hn : IsNilpotent (ad K L x)) : L ≃ₗ⁅K⁆ L := by
  letI : Module ℚ L := Module.compHom L (algebraMap ℚ K)
  letI : Module ℚ (Module.End K L) :=
    Module.compHom (Module.End K L) (algebraMap ℚ K)
  letI : LieAlgebra ℚ L :=
    { lie_smul := by
        intro q a b
        exact LieAlgebra.lie_smul (R := K) (algebraMap ℚ K q) a b }
  have hd : IsNilpotent ((LieDerivation.ad K L x).toLinearMap) := by
    convert hn using 1
    ext y
    simp
  exact LieDerivation.exp (LieDerivation.ad K L x) hd

private theorem exp_ad_apply_of_sq_zero (x y : L)
    (hn : IsNilpotent (ad K L x))
    (hsq : ⁅x, ⁅x, y⁆⁆ = 0) :
    nilpotentAdjointExponential x hn y = y + ⁅x, y⁆ := by
  let : Module ℚ L := Module.compHom L (algebraMap ℚ K)
  let : Module ℚ (Module.End K L) :=
    Module.compHom (Module.End K L) (algebraMap ℚ K)
  have hp : ((ad K L x) ^ 2) y = 0 := by
    simpa [Module.End.pow_apply] using hsq
  unfold nilpotentAdjointExponential
  simp only [LieDerivation.exp_map_apply]
  have heq : ((LieDerivation.ad K L x).toLinearMap) = ad K L x := by
    ext z
    simp
  rw [heq]
  have hps : ((ad K L x) ^ 2) • y = 0 := by
    simpa only [Module.End.smul_def] using hp
  have hexp := IsNilpotent.exp_smul_eq_sum hps hn
  simp only [Module.End.smul_def] at hexp
  simpa [Finset.sum_range_succ, Module.End.smul_def] using hexp

private theorem exp_ad_apply_of_cube_zero (x y : L)
    (hn : IsNilpotent (ad K L x))
    (hcube : ⁅x, ⁅x, ⁅x, y⁆⁆⁆ = 0) :
    nilpotentAdjointExponential x hn y =
      y + ⁅x, y⁆ + (2 : K)⁻¹ • ⁅x, ⁅x, y⁆⁆ := by
  let : Module ℚ L := Module.compHom L (algebraMap ℚ K)
  let : Module ℚ (Module.End K L) :=
    Module.compHom (Module.End K L) (algebraMap ℚ K)
  have hp : ((ad K L x) ^ 3) y = 0 := by
    simpa [Module.End.pow_apply] using hcube
  unfold nilpotentAdjointExponential
  simp only [LieDerivation.exp_map_apply]
  have heq : ((LieDerivation.ad K L x).toLinearMap) = ad K L x := by
    ext z
    simp
  rw [heq]
  have hps : ((ad K L x) ^ 3) • y = 0 := by
    simpa only [Module.End.smul_def] using hp
  have hexp := IsNilpotent.exp_smul_eq_sum hps hn
  simp only [Module.End.smul_def] at hexp
  have hhalf (z : L) : ((2 : ℚ)⁻¹) • z = (2 : K)⁻¹ • z := by
    change (algebraMap ℚ K ((2 : ℚ)⁻¹)) • z = _
    norm_num
  simpa [Finset.sum_range_succ, Module.End.smul_def, Module.End.pow_apply,
    hhalf] using hexp

/-- The three nilpotent adjoint exponentials give the rank-one reflection
on a vector whose `e` and `f` brackets have opposite weights. -/
theorem sl2_adjoint_reflection (h e f t : L) (a : K)
    (hs : IsSl2Triple h e f)
    (he : IsNilpotent (ad K L e)) (hf : IsNilpotent (ad K L (-f)))
    (hte : ⁅t, e⁆ = a • e) (htf : ⁅t, f⁆ = (-a) • f) :
    nilpotentAdjointExponential e he
        (nilpotentAdjointExponential (-f) hf (nilpotentAdjointExponential e he t)) =
      t - a • h := by
  have het : ⁅e, t⁆ = (-a) • e := by
    calc
      ⁅e, t⁆ = -⁅t, e⁆ := (lie_skew e t).symm
      _ = (-a) • e := by rw [hte, neg_smul]
  have hft : ⁅f, t⁆ = a • f := by
    calc
      ⁅f, t⁆ = -⁅t, f⁆ := (lie_skew f t).symm
      _ = a • f := by rw [htf, neg_smul, neg_neg]
  have heh : ⁅e, h⁆ = (-(2 : K)) • e := by
    calc
      ⁅e, h⁆ = -⁅h, e⁆ := (lie_skew e h).symm
      _ = (-(2 : K)) • e := by rw [hs.lie_h_e_smul K, neg_smul]
  have hfh : ⁅f, h⁆ = (2 : K) • f := by
    calc
      ⁅f, h⁆ = -⁅h, f⁆ := (lie_skew f h).symm
      _ = (2 : K) • f := by rw [hs.lie_lie_smul_f K, neg_neg]
  have hfe : ⁅f, e⁆ = -h := by
    calc
      ⁅f, e⁆ = -⁅e, f⁆ := (lie_skew f e).symm
      _ = -h := by rw [hs.lie_e_f]
  have hee : ⁅e, e⁆ = 0 := lie_self e
  have hff : ⁅f, f⁆ = 0 := lie_self f
  have he1 : nilpotentAdjointExponential e he t = t - a • e := by
    rw [exp_ad_apply_of_sq_zero e t he]
    · rw [het]; simp [sub_eq_add_neg]
    · rw [het, lie_smul, hee, smul_zero]
  have hmid1 : ⁅-f, t - a • e⁆ = (-a) • f - a • h := by
    simp [lie_sub, lie_smul, hft, hfe, neg_smul]
  have hmid2 : ⁅-f, ⁅-f, t - a • e⁆⁆ = (2 * a) • f := by
    rw [hmid1]
    simp [lie_sub, lie_smul, hfh, smul_smul]
    module
  have hmid3 : ⁅-f, ⁅-f, ⁅-f, t - a • e⁆⁆⁆ = 0 := by
    rw [hmid2]
    simp [lie_smul]
  have hmid : nilpotentAdjointExponential (-f) hf (t - a • e) = t - a • e - a • h := by
    rw [exp_ad_apply_of_cube_zero (-f) (t - a • e) hf hmid3, hmid2, hmid1]
    module
  have hlast1 : ⁅e, t - a • e - a • h⁆ = a • e := by
    simp [lie_sub, lie_smul, het, heh, smul_smul]
    module
  have hlast2 : ⁅e, ⁅e, t - a • e - a • h⁆⁆ = 0 := by
    rw [hlast1, lie_smul, hee, smul_zero]
  rw [he1, hmid, exp_ad_apply_of_sq_zero e (t - a • e - a • h) he hlast2,
    hlast1]
  module

end ReductiveGroups
