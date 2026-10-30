import OrbitComplexity.FrobeniusSplitting.Normality.Groebner.FlatPolynomials
import Mathlib.RingTheory.Extension.Presentation.Basic
import Mathlib.Data.Finsupp.MonomialOrder.DegLex
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! Free scalar extensions of finitely presented arithmetic algebras. -/

open MvPolynomial TensorProduct

namespace FrobeniusSplitting

variable {K B : Type*} [Field K]

/-- A finitely presented algebra becomes free after enlarging its arithmetic coefficients. -/
theorem exists_free_baseChange (S : Subalgebra ℤ K) (hS : S.FG)
    [CommRing B] [Algebra S B] [Algebra.FinitePresentation S B] :
    ∃ R : Subalgebra ℤ K, R.FG ∧ ∃ hSR : S ≤ R,
      letI : Algebra S R := (Subalgebra.inclusion hSR).toRingHom.toAlgebra
      Module.Free R (R ⊗[S] B) := by
  obtain ⟨n, k, ⟨P⟩⟩ := Algebra.Presentation.exists_presentation_fin S B
  obtain ⟨R, hR, hSR, hfree⟩ := exists_free_polynomial_models S hS
    MonomialOrder.degLex (fun _ : Unit => P.ker)
  let : Algebra S R := (Subalgebra.inclusion hSR).toRingHom.toAlgebra
  have hker : (P.baseChange R).ker =
      P.ker.map (map (algebraMap S R)) := by
    rw [← P.span_range_relation_eq_ker,
      ← (P.baseChange R).span_range_relation_eq_ker, Ideal.map_span, ← Set.range_comp]
    rfl
  have : Module.Free R (P.baseChange R).Quotient := by
    change Module.Free R (MvPolynomial (Fin n) R ⧸ (P.baseChange R).ker)
    rw [hker]
    exact hfree ()
  exact ⟨R, hR, hSR, Module.Free.of_equiv
    ((P.baseChange R).quotientEquiv.restrictScalars R).toLinearEquiv⟩

end FrobeniusSplitting
