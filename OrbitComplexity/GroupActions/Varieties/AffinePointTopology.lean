import OrbitComplexity.ReductiveGroups.Algebra.PointZariski
import OrbitComplexity.GroupActions.Varieties.AffineVariety

/-! # The Zariski topology on affine rational points

The kernel topology on algebra homomorphisms agrees with the topology on rational points
induced from an affine variety. The agreement identifies coordinate charts with their
scheme-theoretic rational points.

## Main definitions

* `GroupActions.affineVarietyPointsHomeomorph`: the topological affine-points identification.

-/

open CategoryTheory AlgebraicGeometry Topology

namespace GroupActions

noncomputable section

attribute [local instance] ReductiveGroups.pointZariskiTopology

universe u

variable (K A : Type u) [Field K] [CommRing A] [Algebra K A]
  [IsReduced A] [Algebra.FiniteType K A]

/-- Algebra homomorphisms with the kernel topology are the rational points of an affine variety. -/
def affineVarietyPointsHomeomorph :
    (A →ₐ[K] K) ≃ₜ (affineVariety K A).points where
  toEquiv := affinePointsEquiv
  continuous_toFun := by
    apply continuous_induced_rng.mpr
    change Continuous[ReductiveGroups.pointZariskiTopology, _]
      (fun f => (affineVariety K A).pointMap (affinePointsEquiv f))
    have hmap : (fun f : A →ₐ[K] K =>
        (affineVariety K A).pointMap (affinePointsEquiv f)) =
        ReductiveGroups.pointZariskiPrime := by
      funext f
      exact affinePointsEquiv_prime f
    rw [hmap]
    exact continuous_induced_dom
  continuous_invFun := by
    apply continuous_induced_rng.mpr
    have hmap : (fun p : (affineVariety K A).points =>
        ReductiveGroups.pointZariskiPrime (affinePointsEquiv.symm p)) =
        (affineVariety K A).pointMap := by
      funext p
      exact (affinePointsEquiv_prime (affinePointsEquiv.symm p)).symm.trans
        (congrArg (fun q => q.val (IsLocalRing.closedPoint K))
          ((affinePointsEquiv (K := K) (R := A)).apply_symm_apply p))
    change Continuous (fun p : (affineVariety K A).points =>
      ReductiveGroups.pointZariskiPrime (affinePointsEquiv.symm p))
    rw [hmap]
    exact (affineVariety K A).continuous_pointMap

end

end GroupActions
