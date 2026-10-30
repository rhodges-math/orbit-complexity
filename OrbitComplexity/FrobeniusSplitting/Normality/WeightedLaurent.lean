import Batteries.Tactic.Lint
import OrbitComplexity.FrobeniusSplitting.Normality.WeightedContraction
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# The Laurent coordinate identity over arbitrary coefficient algebras

-/

open scoped TensorProduct

noncomputable section

namespace FrobeniusSplitting

universe u v

variable {K H C : Type u} [CommRing K] [CommRing H] [CommRing C]
    [Algebra K H] [Algebra K C] {ι : Type v}

/-- The diagonal coaction with a specified coordinate character for each variable. -/
def diagonalCoordinates (χ : ι → H) :
    MvPolynomial ι K →ₐ[K] H ⊗[K] MvPolynomial ι K :=
  MvPolynomial.aeval (fun i => χ i ⊗ₜ[K] MvPolynomial.X i)

/-- Extension of a coordinate map to constant Laurent polynomials. -/
def laurentConstants (q : MvPolynomial ι K →ₐ[K] C) :
    MvPolynomial ι K →ₐ[K] LaurentPolynomial C :=
  (IsScalarTower.toAlgHom K C (LaurentPolynomial C)).comp q

/-- The punctured weighted family is the diagonal coaction evaluated at the
same parameter and the same coordinate point. -/
theorem weightedLaurent_diagonal (weight : ι → ℕ) (χ : ι → H)
    (q : MvPolynomial ι K →ₐ[K] C) (t : H →ₐ[K] LaurentPolynomial C)
    (hχ : ∀ i, t (χ i) = LaurentPolynomial.T (weight i : ℤ)) :
    Polynomial.toLaurent.comp
        ((Polynomial.mapRingHom q.toRingHom).comp
          (weightedCoordinateMap weight).toRingHom) =
      ((Algebra.TensorProduct.lift t (laurentConstants q)
        (fun _ _ => .all _ _)).comp (diagonalCoordinates χ)).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro k
    simp [weightedCoordinateMap, diagonalCoordinates, laurentConstants]
  · intro i
    change Polynomial.toLaurent
        (Polynomial.map q.toRingHom ((weightedCoordinateMap weight) (MvPolynomial.X i))) =
      (Algebra.TensorProduct.lift t (laurentConstants q)
        (fun _ _ => .all _ _)) ((diagonalCoordinates χ) (MvPolynomial.X i))
    simp only [weightedCoordinateMap, diagonalCoordinates, MvPolynomial.aeval_X,
      Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.toLaurent_C_mul_X_pow, Algebra.TensorProduct.lift_tmul,
      hχ, laurentConstants, AlgHom.comp_apply]
    exact mul_comm _ _

end FrobeniusSplitting
