import OrbitComplexity.ReductiveGroups.Lie.Exponential.NilpotentExponentialConjugation
import Mathlib.Algebra.Lie.AdjointAction.Derivation

/-!
# Injective Adjoint Exponential

Transfer a finite adjoint exponential through an injective Lie representation. -/

noncomputable section
namespace ReductiveGroups

open LieAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K L A : Type*} [Field K] [CharZero K]
  [LieRing L] [LieAlgebra K L] [Ring A] [Algebra K A]

omit [CharZero K] in
/-- An injective Lie representation reflects nilpotence of the adjoint of a
represented associative-nilpotent element. -/
theorem InjectiveAdjointExponential.ad_of_injective_representation
    (f : L →ₗ⁅K⁆ A) (hf : Function.Injective f) (x : L)
    (hx : IsNilpotent (f x)) : IsNilpotent (LieAlgebra.ad K L x) := by
  have htarget : IsNilpotent (associativeAdjoint (K := K) (f x)) :=
    associativeAdjoint_nilpotent hx
  have hinter : associativeAdjoint (K := K) (f x) ∘ₗ f.toLinearMap =
      f.toLinearMap ∘ₗ LieAlgebra.ad K L x := by
    rw [associativeAdjoint_eq_ad]
    ext y
    exact (f.map_lie x y).symm
  obtain ⟨m, hm⟩ := htarget
  refine ⟨m, ?_⟩
  ext y
  have hpow := LinearMap.congr_fun
    (Module.End.commute_pow_left_of_commute hinter m) y
  have hz : f (((LieAlgebra.ad K L x) ^ m) y) = 0 := by
    simpa [hm] using hpow.symm
  exact hf (by simpa using hz)

/-- The finite exponential of a nilpotent Lie adjoint as a Lie
automorphism, with scalar parameter `t`. -/
def nilpotentLieAdjointExponential (x : L)
    (hx : IsNilpotent (LieAlgebra.ad K L x)) (t : K) : L ≃ₗ⁅K⁆ L := by
  letI : Module ℚ L := Module.compHom L (algebraMap ℚ K)
  letI : LieAlgebra ℚ L :=
    { lie_smul := by
        intro q a b
        exact LieAlgebra.lie_smul (R := K) (algebraMap ℚ K q) a b }
  have ht : IsNilpotent (LieAlgebra.ad K L (t • x)) := by
    simpa using hx.smul t
  have hd : IsNilpotent ((LieDerivation.ad K L (t • x)).toLinearMap) := by
    have heq : (LieDerivation.ad K L (t • x)).toLinearMap =
        LieAlgebra.ad K L (t • x) := by
      ext y
      simp
    rw [heq]
    exact ht
  exact LieDerivation.exp (LieDerivation.ad K L (t • x)) hd

/-- The represented finite adjoint exponential is conjugation by the finite
associative exponential, with the same scalar sign on both sides. -/
theorem NilpotentLieAdjointExponential.representation
    (f : L →ₗ⁅K⁆ A) (hf : Function.Injective f) (x : L)
    (hx : IsNilpotent (f x)) (t : K) (y : L) :
    f (nilpotentLieAdjointExponential x
      (InjectiveAdjointExponential.ad_of_injective_representation f hf x hx) t y) =
      associativeExponential (K := K) (t • f x) * f y *
        associativeExponential (K := K) (-(t • f x)) := by
  let : Module ℚ L := Module.compHom L (algebraMap ℚ K)
  let : Module ℚ A := Module.compHom A (algebraMap ℚ K)
  let : Module ℚ (Module.End K L) :=
    Module.compHom (Module.End K L) (algebraMap ℚ K)
  let : Module ℚ (Module.End K A) :=
    Module.compHom (Module.End K A) (algebraMap ℚ K)
  have hsource : IsNilpotent (LieAlgebra.ad K L (t • x)) := by
    simpa using (InjectiveAdjointExponential.ad_of_injective_representation f hf x hx).smul t
  have himage : IsNilpotent (f (t • x)) := by
    rw [map_smul]
    exact hx.smul t
  have htarget : IsNilpotent (associativeAdjoint (K := K) (f (t • x))) :=
    associativeAdjoint_nilpotent himage
  have hinter : associativeAdjoint (K := K) (f (t • x)) ∘ₗ f.toLinearMap =
      f.toLinearMap ∘ₗ LieAlgebra.ad K L (t • x) := by
    rw [associativeAdjoint_eq_ad]
    ext z
    exact (f.map_lie (t • x) z).symm
  have hcomm := Module.End.commute_exp_left_of_commute hsource htarget hinter
  have heq : f (nilpotentLieAdjointExponential x
      (InjectiveAdjointExponential.ad_of_injective_representation f hf x hx) t y) =
      associativeAdjointExponential (K := K) (f (t • x)) (f y) := by
    change f (IsNilpotent.exp ((LieDerivation.ad K L (t • x)).toLinearMap) y) =
      IsNilpotent.exp (associativeAdjoint (K := K) (f (t • x))) (f y)
    have hd : (LieDerivation.ad K L (t • x)).toLinearMap =
        LieAlgebra.ad K L (t • x) := by
      ext z
      simp
    rw [hd]
    exact (LinearMap.congr_fun hcomm y).symm
  rw [associativeAdjoint_exp_apply himage] at heq
  simpa only [map_smul, map_neg] using heq

end ReductiveGroups
