import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Coefficient extension of polynomial quotients

Tensoring a polynomial quotient by a coefficient algebra gives the polynomial
quotient by the extended ideal, with the expected formula on pure tensors.
-/

open MvPolynomial
open scoped TensorProduct

namespace GroupActions

noncomputable section

universe u v w

variable (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Algebra R S]
variable {σ : Type w}

/-- A polynomial quotient commutes with extension of its coefficient ring. -/
def polynomialQuotientBaseChange (I : Ideal (MvPolynomial σ R)) :
    S ⊗[R] (MvPolynomial σ R ⧸ I) ≃ₐ[S]
      MvPolynomial σ S ⧸ I.map (MvPolynomial.map (algebraMap R S)) := by
  let J := I.map
    (Algebra.TensorProduct.includeRight : MvPolynomial σ R →ₐ[R] S ⊗[R] MvPolynomial σ R)
  let e := MvPolynomial.algebraTensorAlgEquiv (σ := σ) R S
  have he : e.toRingHom.comp
      (Algebra.TensorProduct.includeRight :
        MvPolynomial σ R →ₐ[R] S ⊗[R] MvPolynomial σ R).toRingHom =
      MvPolynomial.map (algebraMap R S) := by
    apply RingHom.ext
    intro p
    change e (1 ⊗ₜ[R] p) = MvPolynomial.map (algebraMap R S) p
    simp [e]
  have hJ : I.map (MvPolynomial.map (algebraMap R S)) = J.map e.toRingHom := by
    change I.map (MvPolynomial.map (algebraMap R S)) =
      (I.map (Algebra.TensorProduct.includeRight :
        MvPolynomial σ R →ₐ[R] S ⊗[R] MvPolynomial σ R).toRingHom).map e.toRingHom
    rw [Ideal.map_map, he]
  exact (Algebra.TensorProduct.tensorQuotientEquiv S (MvPolynomial σ R) S I).trans
    (Ideal.quotientEquivAlg J _ e hJ)

/-- The quotient coefficient-extension isomorphism sends a pure tensor to the
scalar multiple of the corresponding polynomial with extended coefficients. -/
theorem polynomialQuotientBaseChange_tmul (I : Ideal (MvPolynomial σ R))
    (s : S) (p : MvPolynomial σ R) :
    polynomialQuotientBaseChange R S I (s ⊗ₜ[R] Ideal.Quotient.mk I p) =
      s • Ideal.Quotient.mk (I.map (MvPolynomial.map (algebraMap R S)))
        (MvPolynomial.map (algebraMap R S) p) := by
  change Ideal.Quotient.mk (I.map (MvPolynomial.map (algebraMap R S)))
      (MvPolynomial.algebraTensorAlgEquiv R S (s ⊗ₜ[R] p)) = _
  rw [MvPolynomial.algebraTensorAlgEquiv_tmul]
  exact (Ideal.Quotient.mkₐ S (I.map (MvPolynomial.map (algebraMap R S)))).toLinearMap.map_smul s _

end

end GroupActions
