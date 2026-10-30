import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupPoints
import OrbitComplexity.ReductiveGroups.Groups.Borel.BorelGeometricProperties
import TauCeti.Algebra.AlgebraicGroup.Torus.SmoothConnected

/-!
# Coordinate algebras of the chosen subgroups

The maximal torus and Borel subgroup are affine groups represented by the
quotients of the coordinate algebra by their defining Hopf ideals. The Borel
quotient is geometrically connected and is smooth over an algebraically closed field.

## Main definitions

* `ReductiveGroups.ReductiveGroupData.torusAlgebra`: the maximal torus coordinate algebra.
* `ReductiveGroups.ReductiveGroupData.borelAlgebra`: the Borel coordinate algebra.
-/

noncomputable section

namespace ReductiveGroups.ReductiveGroupData

open TauCeti

universe u

variable {K : Type u} [Field K] (G : ReductiveGroupData K)

/-- The finite type coordinate Hopf algebra of the chosen maximal torus. -/
def torusAlgebra : FiniteTypeCommHopfAlgCat.{u, u} K :=
  FiniteTypeCommHopfAlgCat.quotient G.coordinateAlgebra G.torusIdeal

/-- The finite type coordinate Hopf algebra of the chosen Borel subgroup. -/
def borelAlgebra : FiniteTypeCommHopfAlgCat.{u, u} K :=
  FiniteTypeCommHopfAlgCat.quotient G.coordinateAlgebra G.borelIdeal

/-- The chosen maximal torus coordinate quotient represents a torus. -/
theorem torus_isTorus : torusCommHopfAlgProperty K G.torusAlgebra :=
  G.isMaximalTorus.1

/-- The maximal torus coordinate quotient is smooth. -/
theorem torus_smooth : smoothCommHopfAlgProperty K G.torusAlgebra.obj :=
  torusCommHopfAlgProperty.smooth K G.torusAlgebra G.torus_isTorus

/-- The maximal torus coordinate quotient is geometrically connected. -/
theorem torus_geometricallyConnected :
    geometricallyConnectedCommHopfAlgProperty K G.torusAlgebra.obj :=
  torusCommHopfAlgProperty.geometricallyConnected K G.torusAlgebra G.torus_isTorus

/-- The coordinate ring of the maximal torus is reduced. -/
instance torusAlgebra_isReduced : IsReduced G.torusAlgebra := by
  let : Algebra.Smooth K G.torusAlgebra := G.torus_smooth
  exact isReduced_of_smooth K G.torusAlgebra

/-- The Borel coordinate quotient is geometrically connected. -/
theorem borel_geometricallyConnected :
    geometricallyConnectedCommHopfAlgProperty K G.borelAlgebra.obj :=
  borelQuotient_geometricallyConnected G.borelIdeal G.isBorel

/-- The Borel coordinate quotient is smooth over an algebraically closed field. -/
theorem borel_smooth [IsAlgClosed K] : smoothCommHopfAlgProperty K G.borelAlgebra.obj :=
  borelQuotient_smooth G.borelIdeal G.isBorel

end ReductiveGroupData
