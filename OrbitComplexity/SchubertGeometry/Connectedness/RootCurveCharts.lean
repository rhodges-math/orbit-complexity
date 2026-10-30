import Batteries.Tactic.Lint
import OrbitComplexity.SchubertGeometry.Connectedness.RootCurveParameters
import OrbitComplexity.SchubertGeometry.Cells.Schubert
import OrbitComplexity.GroupActions.Varieties.AdditiveVariety
import OrbitComplexity.GroupActions.Actions.OrbitMap

/-!
# Affine orbit charts for conjugated root curves

The positive and negative root parameters give specified affine-line morphisms into the flag
variety based at any Weyl flag. Their values at zero are the specified anchors. Their gluing
to a projective curve remains separate from these chart constructions.
-/

noncomputable section

namespace SchubertGeometry

open AlgebraicGeometry CategoryTheory GroupActions ReductiveGroups

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K)

/-- The negative root orbit chart based at a specified Weyl flag. -/
def rootCurveZeroChart (w : G.weylGroup) (i : G.rootBase.support) (x : G.weylGroup) :
    (additiveVariety K).toOver ⟶ (flagVariety G).toOver :=
  gaMorphism G (rootLowerMap G w i) ≫
    Variety.orbitMorphism (reductiveVariety G) (flagVariety G) (weylFlagPoint G x)

/-- The positive root orbit chart based at the second specified Weyl flag. -/
def rootCurveInfinityChart (w : G.weylGroup) (i : G.rootBase.support)
    (y : G.weylGroup) : (additiveVariety K).toOver ⟶ (flagVariety G).toOver :=
  gaMorphism G (rootUpperMap G w i) ≫
    Variety.orbitMorphism (reductiveVariety G) (flagVariety G) (weylFlagPoint G y)

omit [IsAlgClosed K] [CharZero K] in
private theorem gaMorphism_zero
    (φ : G.coordinateAlgebra →ₐc[K] SymmetricAlgebra K K) :
    Variety.mapPoints (gaMorphism G φ) (additivePointsEquiv K 0) =
      (1 : (reductiveVariety G).points) := by
  rw [gaMorphism_points, gaParameterPoint_zero]
  exact map_one (reductivePointsMulEquiv G)

private theorem gaOrbit_zero
    (φ : G.coordinateAlgebra →ₐc[K] SymmetricAlgebra K K)
    (x : (flagVariety G).points) :
    Variety.mapPoints (gaMorphism G φ ≫
      Variety.orbitMorphism (reductiveVariety G) (flagVariety G) x)
      (additivePointsEquiv K 0) = x := by
  rw [Variety.mapPoints_comp, gaMorphism_zero, Variety.mapPoints_orbitMorphism, one_smul]

/-- The zero chart takes zero to its original Weyl anchor. -/
theorem rootCurve_zeroChart_zero (w : G.weylGroup) (i : G.rootBase.support)
    (x : G.weylGroup) :
    Variety.mapPoints (rootCurveZeroChart G w i x) (additivePointsEquiv K 0) =
      weylFlagPoint G x :=
  gaOrbit_zero G (rootLowerMap G w i) (weylFlagPoint G x)

/-- The infinity chart takes zero to its original Weyl anchor. -/
theorem rootCurve_infinityChart_zero (w : G.weylGroup) (i : G.rootBase.support)
    (y : G.weylGroup) :
    Variety.mapPoints (rootCurveInfinityChart G w i y) (additivePointsEquiv K 0) =
      weylFlagPoint G y :=
  gaOrbit_zero G (rootUpperMap G w i) (weylFlagPoint G y)

-- RootCurveFlags provides the upper/diagonal stabilizers and Weyl endpoint.
-- RootCurveOverlap provides the scheme-level Laurent overlap, RootCurveGluing its
-- specified global P¹ morphism, and RootCurveContainment the two scheme-image supports
-- and the factor through the original Richardson inclusion. These downstream files
-- do not add a connectedness hypothesis to the construction.

end SchubertGeometry
