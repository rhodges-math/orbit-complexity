import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Batteries.Tactic.Lint
import OrbitComplexity.FrobeniusSplitting.Normality.DescentConnected
import OrbitComplexity.SchubertGeometry.Connectedness.CellLaurentKernel

/-!
# Connectedness of the specified nonempty cell intersection

The ambient family is the positive cocharacter in the original inversion-root
coordinates. Its Laurent kernel equation is proved by the given torus action
on this same intersection. The quotient contraction and its scalar origin are
derived, and connectedness is transported through the original affine counit.
No connectedness, Laurent-preservation or origin package is assumed.

-/

open AlgebraicGeometry CategoryTheory

noncomputable section

namespace SchubertGeometry.CellContraction

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory

universe u

attribute [local instance] coefficientAlgebra

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroups.ReductiveGroupData K)

/-- The original ambient cell family evaluates to the identity at one. -/
theorem cellWeightedMap_one (w : G.weylGroup) (f : cellAlgebra G w) :
    (cellWeightedMap G w f).eval 1 = f :=
  FrobeniusSplitting.weightedCoordinateMap_one_apply (cellWeight G w) f

/-- The original ambient cell family evaluates to its scalar coordinate origin at zero. -/
theorem cellWeightedMap_zero (w : G.weylGroup) (f : cellAlgebra G w) :
    (cellWeightedMap G w f).eval 0 =
      algebraMap K (cellAlgebra G w)
        (MvPolynomial.aeval (fun _ => (0 : K)) f) :=
  FrobeniusSplitting.weightedCoordinateMap_zero_apply
    (cellWeight G w) (cellWeight_pos G w) f

/-- The polynomial contraction of the original closed intersection coordinate ring. -/
def cellContractionAlg (a b w : G.weylGroup) :
    cellCoefficients G a b w →ₐ[K] Polynomial (cellCoefficients G a b w) :=
  FrobeniusSplitting.polynomialDescent (cellIntersectionAlgMap G a b w)
    (cellIntersectionAlgMap_surj G a b w) (cellWeightedMap G w)
    (cellIntersectionLaurent_ideal G a b w)

/-- The same quotient contraction is the identity at one. -/
theorem cellContractionAlg_one (a b w : G.weylGroup)
    (c : cellCoefficients G a b w) :
    (cellContractionAlg G a b w c).eval 1 = c :=
  FrobeniusSplitting.polynomialDescent_one (cellIntersectionAlgMap G a b w)
    (cellIntersectionAlgMap_surj G a b w) (cellWeightedMap G w)
    (cellIntersectionLaurent_ideal G a b w) (cellWeightedMap_one G w) c

/-- The scalar origin on the specified nonempty closed intersection, derived from its ideal. -/
def cellOriginAlg (a b w : G.weylGroup)
    (hne : Nonempty (cellIntersection G a b w).left) :
    cellCoefficients G a b w →ₐ[K] K := by
  let := coefficient_nontrivial (cellIntersection G a b w) hne
  exact FrobeniusSplitting.polynomialOrigin (cellIntersectionAlgMap G a b w)
    (cellIntersectionAlgMap_surj G a b w) (algebraMap K _).injective
    (cellWeightedMap G w) (cellIntersectionLaurent_ideal G a b w)
    (MvPolynomial.aeval (fun _ => (0 : K))) (cellWeightedMap_zero G w)

/-- The derived scalar origin retains exactly the original coordinate origin. -/
theorem cellOriginAlg_comp (a b w : G.weylGroup)
    (hne : Nonempty (cellIntersection G a b w).left) :
    (cellOriginAlg G a b w hne).comp (cellIntersectionAlgMap G a b w) =
      MvPolynomial.aeval (fun _ => (0 : K)) := by
  let := coefficient_nontrivial (cellIntersection G a b w) hne
  exact FrobeniusSplitting.polynomialOrigin_comp (cellIntersectionAlgMap G a b w)
    (cellIntersectionAlgMap_surj G a b w) (algebraMap K _).injective
    (cellWeightedMap G w) (cellIntersectionLaurent_ideal G a b w)
    (MvPolynomial.aeval (fun _ => (0 : K))) (cellWeightedMap_zero G w)

/-- At zero the original quotient contraction is constant through its derived origin. -/
theorem cellContractionAlg_zero (a b w : G.weylGroup)
    (hne : Nonempty (cellIntersection G a b w).left)
    (c : cellCoefficients G a b w) :
    (cellContractionAlg G a b w c).eval 0 =
      algebraMap K (cellCoefficients G a b w) (cellOriginAlg G a b w hne c) := by
  let := coefficient_nontrivial (cellIntersection G a b w) hne
  exact FrobeniusSplitting.polynomialDescent_zero (cellIntersectionAlgMap G a b w)
    (cellIntersectionAlgMap_surj G a b w) (algebraMap K _).injective
    (cellWeightedMap G w) (cellIntersectionLaurent_ideal G a b w)
    (MvPolynomial.aeval (fun _ => (0 : K))) (cellWeightedMap_zero G w) c

/-- Every nonempty original cell/Richardson scheme intersection is connected,
including all of its scheme points and its nilpotent structure. -/
theorem cellIntersection_connected (a b w : G.weylGroup)
    (hne : Nonempty (cellIntersection G a b w).left) :
    ConnectedSpace (cellIntersection G a b w).left := by
  let := coefficient_nontrivial (cellIntersection G a b w) hne
  exact connected_of_coefficients (cellIntersection G a b w)
    (FrobeniusSplitting.spec_connected_of_descent (cellIntersectionAlgMap G a b w)
      (cellIntersectionAlgMap_surj G a b w) (cellWeightedMap G w)
      (cellIntersectionLaurent_ideal G a b w)
      (MvPolynomial.aeval (fun _ => (0 : K)))
      (cellWeightedMap_one G w) (cellWeightedMap_zero G w))

end SchubertGeometry.CellContraction
