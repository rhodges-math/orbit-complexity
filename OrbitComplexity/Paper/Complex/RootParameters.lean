import OrbitComplexity.SchubertGeometry.Roots.Parameters
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! # Torus multiplication of root parameters

The root-character scaling formula holds for every root over the complex numbers.
-/

open ReductiveGroups GroupActions
noncomputable section
namespace SchubertOrbits

export SchubertGeometry (rootParameterMap rootParameter_torus_mul)

/-- Over the complex numbers, torus multiplication scales every specified root
parameter by its root character. -/
theorem root_parameter_torus_complex (G : ReductiveGroupData ℂ) (r : G.rootIndex)
    (t : (torusVariety G).points) (a : ℂ) :
    (torusPointsMulEquiv G t : G.points) * gaParameterPoint (rootParameterMap G r) a =
      gaParameterPoint (rootParameterMap G r)
        (torusWeightCharacter G (G.rootCharacter r).toAdd t * a) *
          (torusPointsMulEquiv G t : G.points) :=
  rootParameter_torus_mul G r t a

end SchubertOrbits
