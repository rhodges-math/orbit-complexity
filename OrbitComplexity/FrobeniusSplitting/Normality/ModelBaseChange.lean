import Batteries.Tactic.Lint
import Mathlib.RingTheory.Extension.Presentation.Core
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.Smooth.Basic

/-!
# Model Base Change

Presentation models commute with extension of their coefficient ring.
-/

open scoped TensorProduct

namespace FrobeniusSplitting

variable {S R K M ι σ : Type*} [CommRing S] [CommRing R] [CommRing K] [CommRing M]
    [Algebra S R] [Algebra R K] [Algebra S K] [IsScalarTower S R K] [Algebra S M]
    (Q : Algebra.Presentation S M ι σ)

/-- Relations defined over the initial ring have coefficients in every intermediate ring. -/
theorem hasCoeffs_baseChange : (Q.baseChange K).HasCoeffs R := by
  constructor
  intro k hk
  change k ∈ ⋃ j, ((Q.baseChange K).relation j).coeffs at hk
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hk
  have hm : MvPolynomial.map (algebraMap R K) ((Q.baseChange R).relation j) =
      (Q.baseChange K).relation j := by
    change MvPolynomial.map (algebraMap R K)
        (MvPolynomial.map (algebraMap S R) (Q.relation j)) =
      MvPolynomial.map (algebraMap S K) (Q.relation j)
    rw [MvPolynomial.map_map, ← IsScalarTower.algebraMap_eq S R K]
  have hc : (((Q.baseChange K).relation j).coeffs : Set K) ⊆
      Set.range (algebraMap R K) :=
    MvPolynomial.mem_range_map_iff_coeffs_subset.mp ⟨_, hm⟩
  exact hc hj

variable [(Q.baseChange K).HasCoeffs R]

/-- A descended base-change relation is the corresponding relation over the intermediate ring. -/
theorem relationOfHasCoeffs_baseChange (hi : Function.Injective (algebraMap R K)) (j : σ) :
    (Q.baseChange K).relationOfHasCoeffs R j = (Q.baseChange R).relation j := by
  apply MvPolynomial.map_injective _ hi
  rw [Algebra.Presentation.map_relationOfHasCoeffs]
  change MvPolynomial.map (algebraMap S K) (Q.relation j) =
    MvPolynomial.map (algebraMap R K) (MvPolynomial.map (algebraMap S R) (Q.relation j))
  rw [MvPolynomial.map_map, ← IsScalarTower.algebraMap_eq S R K]

/-- A presentation already defined over a smaller ring has its expected base-change model. -/
noncomputable def baseChangeModelEquiv (hi : Function.Injective (algebraMap R K)) :
    (Q.baseChange K).ModelOfHasCoeffs R ≃ₐ[R] R ⊗[S] M := by
  have hker : Ideal.span (Set.range ((Q.baseChange K).relationOfHasCoeffs R)) =
      (Q.baseChange R).ker := by
    rw [← (Q.baseChange R).span_range_relation_eq_ker]
    congr 1
    exact congrArg Set.range (funext (relationOfHasCoeffs_baseChange Q hi))
  exact (Ideal.quotientEquivAlgOfEq R hker).trans
    ((Q.baseChange R).quotientEquiv.restrictScalars R)

/-- The base-change model comparison evaluates polynomial classes at the base-changed generators. -/
theorem baseChangeModelEquiv_mk (hi : Function.Injective (algebraMap R K))
    (v : MvPolynomial ι R) :
    baseChangeModelEquiv Q hi (Ideal.Quotient.mk _ v) =
      MvPolynomial.aeval (Q.baseChange R).val v := by
  change (Q.baseChange R).quotientEquiv (Ideal.Quotient.mk _ v) = _
  rfl

end FrobeniusSplitting

namespace FrobeniusSplitting

variable {S R K M A ι σ : Type*}
    [CommRing S] [CommRing R] [CommRing K] [CommRing M] [CommRing A]
    [Algebra S R] [Algebra R K] [Algebra S K] [IsScalarTower S R K]
    [Algebra S M] [Algebra K A] [Algebra R A] [IsScalarTower R K A]
    (Q : Algebra.Presentation S M ι σ) (e : K ⊗[S] M ≃ₐ[K] A)
    [((Q.baseChange K).ofAlgEquiv e).HasCoeffs R]

/-- Changing the target comparison of a presentation preserves its expected model. -/
noncomputable def baseChangeModelEquivOf (hi : Function.Injective (algebraMap R K)) :
    ((Q.baseChange K).ofAlgEquiv e).ModelOfHasCoeffs R ≃ₐ[R] R ⊗[S] M := by
  have : (Q.baseChange K).HasCoeffs R := hasCoeffs_baseChange Q
  have hker :
      Ideal.span (Set.range (((Q.baseChange K).ofAlgEquiv e).relationOfHasCoeffs R)) =
        Ideal.span (Set.range ((Q.baseChange K).relationOfHasCoeffs R)) := by
    rfl
  exact (Ideal.quotientEquivAlgOfEq R hker).trans (baseChangeModelEquiv Q hi)

/-- The comparison with a changed target still evaluates polynomial classes at model generators. -/
theorem baseChangeModelEquivOf_mk (hi : Function.Injective (algebraMap R K))
    (v : MvPolynomial ι R) :
    baseChangeModelEquivOf Q e hi (Ideal.Quotient.mk _ v) =
      MvPolynomial.aeval (Q.baseChange R).val v := by
  have : (Q.baseChange K).HasCoeffs R := hasCoeffs_baseChange Q
  change baseChangeModelEquiv Q hi (Ideal.Quotient.mk _ v) = _
  exact baseChangeModelEquiv_mk Q hi v

/-- Smoothness is preserved by a presentation model already defined over a smaller ring. -/
theorem smooth_baseChangeModel [Algebra.Smooth S M]
    (hi : Function.Injective (algebraMap R K)) :
    Algebra.Smooth R (((Q.baseChange K).ofAlgEquiv e).ModelOfHasCoeffs R) := by
  have : Algebra.Smooth R (R ⊗[S] M) := inferInstance
  exact Algebra.Smooth.of_equiv (baseChangeModelEquivOf Q e hi).symm

end FrobeniusSplitting
