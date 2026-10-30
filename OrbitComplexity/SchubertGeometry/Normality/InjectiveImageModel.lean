import OrbitComplexity.SchubertGeometry.Normality.Coordinates.GraphPresentation
import OrbitComplexity.FrobeniusSplitting.Normality.Groebner.SplitImageModel
import OrbitComplexity.FrobeniusSplitting.Normality.Groebner.QuotientBaseChange
import OrbitComplexity.FrobeniusSplitting.Normality.Retractions.PrescribedRetraction

/-! Coefficient models preserving an injective map under all scalar extensions. -/

open MvPolynomial
open scoped TensorProduct

universe u

open FrobeniusSplitting

namespace SchubertGeometry

/-- An injective generic map spreads to a split inclusion of the original models. -/
theorem exists_injective_image_model {K : Type u} [Field K]
    (S : Subalgebra ℤ K) (hS : S.FG)
    {M N : Type u} [CommRing M] [CommRing N] [Algebra S M] [Algebra S N]
    [Algebra.FinitePresentation S M] [Algebra.FinitePresentation S N]
    (f : M →ₐ[S] N)
    (hf : Function.Injective (Algebra.TensorProduct.lTensor (S := K) K f)) :
    ∃ R : Subalgebra ℤ K, R.FG ∧ ∃ hSR : S ≤ R,
      letI : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
      ∃ r : R ⊗[S] N →ₗ[R] R ⊗[S] M,
        r.comp (Algebra.TensorProduct.lTensor (S := R) R f).toLinearMap =
          LinearMap.id := by
  classical
  obtain ⟨m, n, I, eA, eB, hgraph⟩ := exists_injective_graph_presentation
    (Algebra.TensorProduct.lTensor (S := K) K f) hf
  obtain ⟨T, hT, hST, hJ, hA, hfree, r, hr⟩ := exists_split_image_model S hS I
  let J : Ideal (MvPolynomial (Fin n ⊕ₗ Fin m) T) :=
    I.comap (map T.val.toRingHom)
  let P := MvPolynomial (Fin m) T ⧸ J.comap (rename Sum.inrₗ).toRingHom
  let Q := MvPolynomial (Fin n ⊕ₗ Fin m) T ⧸ J
  let : Module.Free T Q := hfree
  let : IsNoetherianRing T := isNoetherianRing_of_fg hT
  have : Algebra.FinitePresentation T P :=
    (Algebra.FinitePresentation.of_finiteType (R := T) (A := P)).mp inferInstance
  have : Algebra.FinitePresentation T Q :=
    (Algebra.FinitePresentation.of_finiteType (R := T) (A := Q)).mp inferInstance
  let eP : K ⊗[T] P ≃ₐ[K] K ⊗[S] M :=
    (polynomialQuotientEquiv _ _ hA).trans eA
  let eQ : K ⊗[T] Q ≃ₐ[K] K ⊗[S] N :=
    (polynomialQuotientEquiv J I hJ).trans eB
  have hsq (y : K ⊗[T] P) :
      eQ (Algebra.TensorProduct.lTensor (S := K) K (eliminationQuotientMap J) y) =
        Algebra.TensorProduct.lTensor (S := K) K f (eP y) := by
    change eB (polynomialQuotientEquiv J I hJ
      (Algebra.TensorProduct.lTensor (S := K) K (eliminationQuotientMap J) y)) =
        Algebra.TensorProduct.lTensor (S := K) K f
          (eA (polynomialQuotientEquiv _ _ hA y))
    rw [polynomialQuotientEquiv_rename J I hJ hA]
    exact AlgHom.congr_fun hgraph (polynomialQuotientEquiv _ _ hA y)
  obtain ⟨R, hR, hTR, hrR⟩ := exists_prescribed_retraction S T hT hST f
    (eliminationQuotientMap J) eP eQ r hr hsq
  exact ⟨R, hR, hST.trans hTR, hrR⟩

end SchubertGeometry
