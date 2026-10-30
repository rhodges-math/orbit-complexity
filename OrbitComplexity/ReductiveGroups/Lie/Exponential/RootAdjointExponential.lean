import OrbitComplexity.ReductiveGroups.Lie.Roots.CanonicalRootWeightRealization
import Mathlib.RingTheory.Nilpotent.Exp

/-!
# Root Adjoint Exponential

The finite exponential of a root-vector adjoint action in a split Lie algebra. -/

noncomputable section

namespace ReductiveGroups

open LieAlgebra LieAlgebra.IsKilling LieModule

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [LieAlgebra.IsKilling K L] [FiniteDimensional K L]
  (H : LieSubalgebra K L) [H.IsCartanSubalgebra] [IsTriangularizable K H L]

/-- The exponential of the scaled adjoint derivation of a nonzero root vector. -/
def rootAdjointExponential (χ : H → K) (hχ : χ ≠ 0)
    (x : L) (hx : x ∈ rootSpace H χ) (n : K) : L ≃ₗ⁅K⁆ L := by
  letI : Module ℚ L := Module.compHom L (algebraMap ℚ K)
  letI : LieAlgebra ℚ L :=
    { lie_smul := by
        intro t a b
        exact LieAlgebra.lie_smul (R := K) (algebraMap ℚ K t) a b }
  let z : L := (-n) • x
  have hz : z ∈ rootSpace H χ := (rootSpace H χ).smul_mem (-n) hx
  have hn : IsNilpotent (ad K L z) :=
    LieAlgebra.isNilpotent_ad_of_mem_rootSpace H hχ hz
  have hd : IsNilpotent ((LieDerivation.ad K L z).toLinearMap) := by
    have heq : ((LieDerivation.ad K L z).toLinearMap) = ad K L z := by
      ext y
      simp
    rw [heq]
    exact hn
  exact LieDerivation.exp (LieDerivation.ad K L z) hd

omit [LieAlgebra.IsKilling K L] in
/-- The automorphism acts by a finite adjoint exponential.  The cutoff is
the nilpotency class of the unscaled adjoint operator, uniform in the parameter. -/
theorem rootAdjointExponential_apply (χ : H → K) (hχ : χ ≠ 0)
    (x : L) (hx : x ∈ rootSpace H χ) (n : K) (y : L) :
    rootAdjointExponential H χ hχ x hx n y =
      ∑ j ∈ Finset.range (nilpotencyClass (ad K L x)),
        (j.factorial : K)⁻¹ • ((ad K L ((-n) • x)) ^ j) y := by
  let : Module ℚ L := Module.compHom L (algebraMap ℚ K)
  let : LieAlgebra ℚ L :=
    { lie_smul := by
        intro t a b
        exact LieAlgebra.lie_smul (R := K) (algebraMap ℚ K t) a b }
  let : Module ℚ (Module.End K L) :=
    Module.compHom (Module.End K L) (algebraMap ℚ K)
  let z : L := (-n) • x
  have hz : z ∈ rootSpace H χ := (rootSpace H χ).smul_mem (-n) hx
  have hn : IsNilpotent (ad K L z) :=
    LieAlgebra.isNilpotent_ad_of_mem_rootSpace H hχ hz
  have hn0 : IsNilpotent (ad K L x) :=
    LieAlgebra.isNilpotent_ad_of_mem_rootSpace H hχ hx
  have hpow : (ad K L z) ^ (nilpotencyClass (ad K L x)) = 0 := by
    have heq : ad K L z = (-n) • ad K L x := by
      simp [z]
    rw [heq, smul_pow, pow_nilpotencyClass hn0, smul_zero]
  have hd : IsNilpotent ((LieDerivation.ad K L z).toLinearMap) := by
    have heq : ((LieDerivation.ad K L z).toLinearMap) = ad K L z := by
      ext w
      simp
    rw [heq]
    exact hn
  change IsNilpotent.exp ((LieDerivation.ad K L z).toLinearMap) y = _
  have heq : ((LieDerivation.ad K L z).toLinearMap) = ad K L z := by
    ext w
    simp
  rw [heq, IsNilpotent.exp_eq_sum hpow]
  simp only [z]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply]
  apply Finset.sum_congr rfl
  intro j hj
  change (algebraMap ℚ K ((j.factorial : ℚ)⁻¹)) •
      ((ad K L ((-n) • x)) ^ j) y = _
  simp

omit [LieAlgebra.IsKilling K L] in
/-- The factorial coefficients of the first-order adjoint expansion. -/
theorem RootAdjointExponential.apply_coefficients (χ : H → K) (hχ : χ ≠ 0)
    (x : L) (hx : x ∈ rootSpace H χ) (n : K) (y : L) :
    rootAdjointExponential H χ hχ x hx n y =
      ∑ j ∈ Finset.range (nilpotencyClass (ad K L x)),
        ((-n) ^ j / (j.factorial : K)) • ((ad K L x) ^ j) y := by
  rw [rootAdjointExponential_apply]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [map_smul, smul_pow, div_eq_mul_inv]
  rw [LinearMap.smul_apply]
  rw [smul_smul]
  congr 1
  exact mul_comm _ _

end ReductiveGroups
