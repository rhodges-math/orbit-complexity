import OrbitComplexity.GroupActions.Varieties.ReductiveVariety
import Mathlib.GroupTheory.GroupAction.Quotient

/-! # Rational flag points

The rational flag space is the quotient of the group points by its chosen Borel subgroup.
It carries the quotient Zariski topology and the standard left action of the group.

## Main definitions

* `SchubertGeometry.flagPoints`: the coset space of the Borel subgroup.
* `SchubertGeometry.flagProjection`: the quotient map from group points.
* `SchubertGeometry.baseFlag`: the flag represented by the identity.

## Main results

* `SchubertGeometry.flagProjection_quotientMap`: the topology is the quotient topology.
* `SchubertGeometry.isOpenMap_flagProjection`: the quotient projection is open.
* `SchubertGeometry.baseFlagStabilizer`: the stabilizer of the base flag is the Borel subgroup.
-/

namespace SchubertGeometry

noncomputable section

universe u

variable {K : Type u} [Field K] (G : ReductiveGroups.ReductiveGroupData K)

/-- The rational flag space, with its quotient Zariski topology and left group action. -/
abbrev flagPoints := G.points ⧸ G.borelPoints

/-- The projection from a group point to its Borel coset. -/
abbrev flagProjection : G.points → flagPoints G := QuotientGroup.mk

/-- The base flag represented by the identity of the group. -/
def baseFlag : flagPoints G := flagProjection G 1

/-- Every rational flag has a group representative. -/
theorem flagProjection_surjective : Function.Surjective (flagProjection G) :=
  QuotientGroup.mk_surjective

/-- Two group points represent the same flag exactly when their quotient lies in the Borel. -/
theorem flagProjection_eq_iff (g h : G.points) :
    flagProjection G g = flagProjection G h ↔ g⁻¹ * h ∈ G.borelPoints := QuotientGroup.eq

/-- The projection to flags intertwines left multiplication and the left group action. -/
theorem flagProjection_smul (g h : G.points) :
    flagProjection G (g * h) = g • flagProjection G h := rfl

/-- The topology on rational flags is the quotient of the Zariski topology on group points. -/
theorem flagProjection_quotientMap : Topology.IsQuotientMap (flagProjection G) :=
  isQuotientMap_quotient_mk'

/-- The projection from group points to flag points is continuous. -/
theorem continuous_flagProjection : Continuous (flagProjection G) :=
  (flagProjection_quotientMap G).continuous

/-- The projection from group points to flag points is an open map. -/
theorem isOpenMap_flagProjection : IsOpenMap (flagProjection G) :=
  QuotientGroup.isOpenMap_coe (N := G.borelPoints)

/-- The chosen Borel subgroup is the stabilizer of the base flag. -/
theorem baseFlagStabilizer : MulAction.stabilizer G.points (baseFlag G) = G.borelPoints :=
  MulAction.stabilizer_quotient G.borelPoints

/-- The chosen maximal torus fixes the base flag. -/
theorem torus_smul_baseFlag (t : G.torusPoints) : t • baseFlag G = baseFlag G := by
  have ht : (t : G.points) ∈ MulAction.stabilizer G.points (baseFlag G) := by
    rw [baseFlagStabilizer]
    exact G.torus_le_borel t.property
  exact ht

end

end SchubertGeometry
