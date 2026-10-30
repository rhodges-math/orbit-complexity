import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupReflectionSquare
import OrbitComplexity.SchubertGeometry.Roots.Parameters

/-! # Exact root-parameter scaling by a simple-representative square -/

noncomputable section

namespace SchubertGeometry

open ReductiveGroups

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

/-- Squaring the chosen simple representative scales every root parameter by Cartan parity. -/
theorem simpleSquare_root_parameter (i : G.rootBase.support) (r : G.rootIndex) (t : K) :
    G.reflectionPoint i.val ^ 2 * gaParameterPoint (rootParameterMap G r) t *
        (G.reflectionPoint i.val ^ 2)⁻¹ =
      gaParameterPoint (rootParameterMap G r)
        (((-1 : K) ^ G.rootSystem.pairingIn ℤ r i.val) * t) :=
  GaAffineGroupPoints.conjugate_of_tangent_eq _ _ _ _
    (G.simpleReflection_square_weight i r _ (rootParameterMap_tangent_mem G r)) t

end SchubertGeometry
