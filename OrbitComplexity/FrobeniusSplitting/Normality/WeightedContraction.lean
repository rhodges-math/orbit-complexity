import Batteries.Tactic.Lint
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# Positive-weight polynomial contractions

The ambient polynomial contraction multiplies each coordinate by a positive
power of the parameter. Its zero and one equations are proved over arbitrary
coefficient rings, before any Schubert chart or concrete scheme is substituted.

The weighted-coordinate construction does not identify the punctured family with a
torus cocharacter. That geometric identification is a separate obligation.
-/

noncomputable section

namespace FrobeniusSplitting

universe u v

variable {K : Type u} [CommRing K] {ι : Type v}

/-- The polynomial family which scales coordinate i by the given weight. -/
def weightedCoordinateMap (weight : ι → ℕ) :
    MvPolynomial ι K →ₐ[K] Polynomial (MvPolynomial ι K) :=
  MvPolynomial.aeval (fun i =>
    Polynomial.C (MvPolynomial.X i) * Polynomial.X ^ weight i)

/-- The weighted family equals the identity at parameter one. -/
theorem weightedCoordinateMap_one (weight : ι → ℕ) :
    ((Polynomial.aeval (1 : MvPolynomial ι K)).restrictScalars K).comp
        (weightedCoordinateMap weight) =
      AlgHom.id K (MvPolynomial ι K) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp [weightedCoordinateMap]

/-- Positive weights make the zero endpoint the original coordinate origin. -/
theorem weightedCoordinateMap_zero (weight : ι → ℕ)
    (hpositive : ∀ i, 0 < weight i) :
    ((Polynomial.aeval (0 : MvPolynomial ι K)).restrictScalars K).comp
        (weightedCoordinateMap weight) =
      (Algebra.ofId K (MvPolynomial ι K)).comp
        (MvPolynomial.aeval (fun _ : ι => (0 : K))) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp [weightedCoordinateMap, Nat.ne_of_gt (hpositive i)]

/-- The positive-weight family evaluates to the original coordinate at one. -/
theorem weightedCoordinateMap_one_apply (weight : ι → ℕ) (a : MvPolynomial ι K) :
    (weightedCoordinateMap weight a).eval 1 = a := by
  have h := DFunLike.congr_fun (weightedCoordinateMap_one weight) a
  simpa only [AlgHom.comp_apply, AlgHom.id_apply, AlgHom.restrictScalars_apply,
    Polynomial.coe_aeval_eq_eval] using h

/-- The positive-weight family evaluates to the scalar coordinate origin at zero. -/
theorem weightedCoordinateMap_zero_apply (weight : ι → ℕ)
    (hpositive : ∀ i, 0 < weight i) (a : MvPolynomial ι K) :
    (weightedCoordinateMap weight a).eval 0 =
      algebraMap K (MvPolynomial ι K) (MvPolynomial.aeval (fun _ : ι => (0 : K)) a) := by
  have h := DFunLike.congr_fun (weightedCoordinateMap_zero weight hpositive) a
  simpa only [AlgHom.comp_apply, AlgHom.restrictScalars_apply,
    Polynomial.coe_aeval_eq_eval, Algebra.ofId_apply] using h

end FrobeniusSplitting
