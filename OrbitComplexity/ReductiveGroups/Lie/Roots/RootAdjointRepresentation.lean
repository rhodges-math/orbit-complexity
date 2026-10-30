import OrbitComplexity.ReductiveGroups.Lie.Exponential.RootAdjointExponential
import OrbitComplexity.ReductiveGroups.Lie.Exponential.NilpotentExponentialConjugation
import OrbitComplexity.ReductiveGroups.Lie.Exponential.AssociativeRootNilpotence

/-!
# Root Adjoint Representation

Compatibility of the constructed root-adjoint automorphism with
conjugation after a Lie representation in an associative algebra. -/

noncomputable section
namespace ReductiveGroups
open LieAlgebra LieModule

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K L A : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [Ring A] [Algebra K A]
  (H : LieSubalgebra K L) [H.IsCartanSubalgebra] [IsTriangularizable K H L]

/-- When the represented root vector is nilpotent as an associative element,
the root-adjoint automorphism is represented by exponential conjugation. -/
theorem rootAdjointExponential_representation
    (χ : H → K) (hχ : χ ≠ 0) (x : L) (hx : x ∈ rootSpace H χ)
    (f : L →ₗ⁅K⁆ A) (hf : IsNilpotent (f x)) (n : K) (y : L) :
    f (rootAdjointExponential H χ hχ x hx n y) =
      associativeExponential (K := K) ((-n) • f x) * f y *
        associativeExponential (K := K) (n • f x) := by
  let : Module ℚ L := Module.compHom L (algebraMap ℚ K)
  let : Module ℚ A := Module.compHom A (algebraMap ℚ K)
  let : Module ℚ (Module.End K L) :=
    Module.compHom (Module.End K L) (algebraMap ℚ K)
  let : Module ℚ (Module.End K A) :=
    Module.compHom (Module.End K A) (algebraMap ℚ K)
  have hsource : IsNilpotent (ad K L ((-n) • x)) :=
    LieAlgebra.isNilpotent_ad_of_mem_rootSpace H hχ
      ((rootSpace H χ).smul_mem (-n) hx)
  have himage : IsNilpotent (f ((-n) • x)) := by
    rw [map_smul]
    exact hf.smul (-n)
  have htarget : IsNilpotent (associativeAdjoint (K := K) (f ((-n) • x))) :=
    associativeAdjoint_nilpotent himage
  have hinter : associativeAdjoint (K := K) (f ((-n) • x)) ∘ₗ f.toLinearMap =
      f.toLinearMap ∘ₗ ad K L ((-n) • x) := by
    rw [associativeAdjoint_eq_ad]
    ext z
    exact (f.map_lie ((-n) • x) z).symm
  have hcomm := Module.End.commute_exp_left_of_commute hsource htarget hinter
  have heq : f (rootAdjointExponential H χ hχ x hx n y) =
      associativeAdjointExponential (K := K) (f ((-n) • x)) (f y) := by
    change f (IsNilpotent.exp ((LieDerivation.ad K L ((-n) • x)).toLinearMap) y) =
      IsNilpotent.exp (associativeAdjoint (K := K) (f ((-n) • x))) (f y)
    have hd : (LieDerivation.ad K L ((-n) • x)).toLinearMap = ad K L ((-n) • x) := by
      ext z
      simp
    rw [hd]
    exact (LinearMap.congr_fun hcomm y).symm
  rw [associativeAdjoint_exp_apply himage] at heq
  simpa only [map_smul, map_neg, neg_smul, neg_neg] using heq

/-- Over an algebraically closed field, including the complex field,
nilpotence of the represented root vector is proved from its weight. -/
theorem RootAdjointExponential.finite_representation
    [IsAlgClosed K] [FiniteDimensional K A]
    (χ : H → K) (hχ : χ ≠ 0) (x : L) (hx : x ∈ rootSpace H χ)
    (f : L →ₗ⁅K⁆ A) (n : K) (y : L) :
    f (rootAdjointExponential H χ hχ x hx n y) =
      associativeExponential (K := K) ((-n) • f x) * f y *
        associativeExponential (K := K) (n • f x) :=
  rootAdjointExponential_representation H χ hχ x hx f
    (AssociativeRootNilpotence.image_isNilpotent_of_mem_rootSpace H f hχ hx) n y

end ReductiveGroups
