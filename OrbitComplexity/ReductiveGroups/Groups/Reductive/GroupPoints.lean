import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupData
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Order

/-!
# Rational points of reductive groups

The group of rational points is the convolution group of algebra maps from the
coordinate algebra to the base field. The chosen torus and Borel subgroup cut out
subgroups by vanishing of their Hopf ideals.

## Main definitions

* `ReductiveGroups.ReductiveGroupData.points`: the group of rational points.
* `ReductiveGroups.ReductiveGroupData.torusPoints`: its chosen maximal torus.
* `ReductiveGroups.ReductiveGroupData.borelPoints`: its chosen Borel subgroup.

## Main results

* `ReductiveGroups.ReductiveGroupData.torus_le_borel`: the torus lies in the Borel subgroup.
-/

noncomputable section

namespace ReductiveGroups.ReductiveGroupData

open TauCeti

universe u

variable {K : Type u} [Field K] (G : ReductiveGroupData K)

/-- Rational points of the reductive group, with convolution multiplication. -/
abbrev points := WithConv (G.coordinateAlgebra →ₐ[K] K)

/-- The rational points of the chosen maximal torus. -/
def torusPoints : Subgroup G.points :=
  CommHopfAlgCat.quotientPointsSubgroup (CommHopfAlgCat.of K G.coordinateAlgebra)
    G.torusIdeal (CommAlgCat.of K K)

/-- The rational points of the chosen Borel subgroup. -/
def borelPoints : Subgroup G.points :=
  CommHopfAlgCat.quotientPointsSubgroup (CommHopfAlgCat.of K G.coordinateAlgebra)
    G.borelIdeal (CommAlgCat.of K K)

/-- A point lies in the chosen torus exactly when it kills the torus ideal. -/
theorem mem_torusPoints (g : G.points) :
    g ∈ G.torusPoints ↔ ∀ a ∈ G.torusIdeal, g.ofConv a = 0 :=
  CommHopfAlgCat.mem_quotientPointsSubgroup_iff _ _ _ _

/-- A point lies in the chosen Borel subgroup exactly when it kills the Borel ideal. -/
theorem mem_borelPoints (g : G.points) :
    g ∈ G.borelPoints ↔ ∀ a ∈ G.borelIdeal, g.ofConv a = 0 :=
  CommHopfAlgCat.mem_quotientPointsSubgroup_iff _ _ _ _

/-- The rational points of the maximal torus form a subgroup of the Borel points. -/
theorem torus_le_borel : G.torusPoints ≤ G.borelPoints :=
  CommHopfAlgCat.quotientPointsSubgroup_le_of_le _ G.borel_le_torus _

end ReductiveGroupData
