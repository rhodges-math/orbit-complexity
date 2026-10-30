import OrbitComplexity.GroupActions.Varieties.AffineVariety

/-! # Coordinate basic opens in affine space

A rational point lies in the basic open of a product of coordinate functions exactly when
all selected coordinates are nonzero.

## Main results

* `GroupActions.affineBasicOpen_points`: membership in a coordinate basic open.
-/

open AlgebraicGeometry
open scoped BigOperators

namespace GroupActions

universe u

/-- A product of coordinates is nonzero at a rational point exactly when each factor is nonzero. -/
theorem affineBasicOpen_points {K ι : Type u} [Field K] [Finite ι]
    (S : Finset ι) (x : (affineSpaceVariety K ι).points) :
    (affineSpaceVariety K ι).pointMap x ∈
        PrimeSpectrum.basicOpen (∏ j ∈ S, (MvPolynomial.X j : MvPolynomial ι K)) ↔
      ∀ j ∈ S, affineSpaceVarietyPointsEquiv K ι x j ≠ 0 := by
  classical
  let f : MvPolynomial ι K →ₐ[K] K := affinePointsEquiv.symm x
  have hx : affinePointsEquiv f = x := Equiv.apply_symm_apply _ x
  have hp : (affineSpaceVariety K ι).pointMap x =
      (⟨RingHom.ker f, RingHom.ker_isPrime f⟩ : PrimeSpectrum _) := by
    exact (congrArg (fun q => q.val (IsLocalRing.closedPoint K)) hx).symm.trans
      (affinePointsEquiv_prime f)
  rw [hp]
  change f (∏ j ∈ S, (MvPolynomial.X j : MvPolynomial ι K)) ≠ 0 ↔ _
  simp only [map_prod, Finset.prod_ne_zero_iff]
  rfl

end GroupActions
