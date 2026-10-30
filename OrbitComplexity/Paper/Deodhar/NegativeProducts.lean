import OrbitComplexity.Paper.Deodhar.Products
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupOppositeTangent
import OrbitComplexity.ReductiveGroups.Groups.Cells.BruhatDoubleCosets
import OrbitComplexity.SchubertGeometry.Deodhar.NegativeProducts

/-! # Negative-root products of distinguished subexpressions

Selected signed root parameters lie in the opposite unipotent subgroup. Their ordered product
places every distinguished prefix in that subgroup times its signed prefix representative.

## References

* R. J. Marsh and K. Rietsch, *Parametrizations of flag varieties*, Proposition 5.2.
-/

namespace SchubertOrbits

export SchubertGeometry (
  subwordRootMap_mem_opposite
  subwordRootProduct_mem_opposite
  deodharPrefix_mem_opposite
)

end SchubertOrbits
