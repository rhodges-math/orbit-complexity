import OrbitComplexity.ReductiveGroups.GLn.Reductive
import OrbitComplexity.ReductiveGroups.GLn.Borel
import OrbitComplexity.ReductiveGroups.GLn.MaximalTorus
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupData

/-!
# General linear groups with a torus and Borel subgroup

The coordinate Hopf algebra of `GL_n`, its diagonal torus, and its upper triangular
Borel subgroup form reductive group data over an algebraically closed field.

## Main definitions

* `ReductiveGroups.GLn.groupData`: reductive group data for the general linear group.

## Main results

* `ReductiveGroups.GLn.groupData_torusIdeal`: its maximal torus is the diagonal torus.
* `ReductiveGroups.GLn.groupData_borelIdeal`: its Borel subgroup is upper triangular.

## References

* A. Borel, *Linear Algebraic Groups*, 2nd ed., Springer (1991), Chapters III and IV.
-/

noncomputable section

namespace ReductiveGroups.GLn

open TauCeti TauCeti.GeneralLinear

universe u

variable (K : Type u) [Field K] [IsAlgClosed K] (n : ℕ)

/-- The general linear group with its diagonal torus and upper triangular Borel subgroup. -/
def groupData : ReductiveGroupData K where
  coordinateAlgebra := finiteTypeCoordinateHopfAlgebra K n
  torusIndex := ULift.{u} (Fin n)
  finiteIndex := inferInstance
  torusIdeal := torusIdeal K n
  borelIdeal := upperTriangularIdeal K n
  borel_le_torus := upperTriangularIdeal_le_torusIdeal K n
  isMaximalTorus := isMaximalTorus_torusIdeal K n
  isBorel := isBorel_upperTriangularIdeal K n
  torusSplit := torusRestriction K n
  split_surjective := torusRestriction_surjective K n
  split_eq_zero := torusRestriction_eq_zero_iff K n
  reductive := reductive K n

/-- The coordinate algebra of this group data is the coordinate algebra of `GL_n`. -/
theorem groupData_coordinateAlgebra :
    (groupData K n).coordinateAlgebra = finiteTypeCoordinateHopfAlgebra K n :=
  rfl

/-- The maximal torus of this group data is the diagonal torus. -/
theorem groupData_torusIdeal : (groupData K n).torusIdeal = torusIdeal K n :=
  rfl

/-- The Borel subgroup of this group data is the upper triangular subgroup. -/
theorem groupData_borelIdeal : (groupData K n).borelIdeal = upperTriangularIdeal K n :=
  rfl

end GLn
