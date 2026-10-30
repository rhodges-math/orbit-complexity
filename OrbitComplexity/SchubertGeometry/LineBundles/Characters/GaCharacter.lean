import OrbitComplexity.ReductiveGroups.Groups.GaCoordinates.GaTangentCoordinate
import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Scheme.Basic
import Mathlib.Algebra.Polynomial.Degree.Units

/-! # Characters of the additive group -/

noncomputable section
namespace SchubertGeometry.ProjectiveLine
open ReductiveGroups TauCeti
universe u
variable {K : Type u} [Field K]

/-- A regular multiplicative character of the additive group takes its generator to one. -/
theorem additiveCharacter_generator
    (f : MonoidAlgebra K (Multiplicative ℤ) →ₐc[K] SymmetricAlgebra K K) :
    f (MonoidAlgebra.single (Multiplicative.ofAdd 1) 1) = 1 := by
  let z : MonoidAlgebra K (Multiplicative ℤ) :=
    MonoidAlgebra.single (Multiplicative.ofAdd 1) 1
  have hz : IsUnit z := by
    apply isUnit_iff_exists_inv.mpr
    refine ⟨MonoidAlgebra.single (Multiplicative.ofAdd (-1)) 1, ?_⟩
    simp [z, MonoidAlgebra.single_mul_single, ← MonoidAlgebra.one_def]
  have hu : IsUnit (gaPolynomialEquiv K (f z)) :=
    (hz.map f.toMonoidHom).map (gaPolynomialEquiv K).toMonoidHom
  have hp := Polynomial.eq_C_of_natDegree_eq_zero
    (Polynomial.natDegree_eq_zero_of_isUnit hu)
  apply (gaPolynomialEquiv K).injective
  change gaPolynomialEquiv K (f z) = gaPolynomialEquiv K 1
  rw [hp, gaPolynomialEquiv_coeff_zero, CoalgHomClass.counit_comp_apply, map_one]
  simp only [z, MonoidAlgebra.counit_single, CommSemiring.counit_apply, Polynomial.C_1]

end SchubertGeometry.ProjectiveLine
