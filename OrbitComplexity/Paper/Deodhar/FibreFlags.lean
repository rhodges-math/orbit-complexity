import OrbitComplexity.Paper.Deodhar.StepFlags
import OrbitComplexity.SchubertGeometry.Deodhar.OppositeRootPoints
import OrbitComplexity.SchubertGeometry.Cells.OppositeDecomposition
import OrbitComplexity.SchubertGeometry.Deodhar.FibreFlags

/-! # Opposite-cell conditions in a rank-one fibre

The additive cell chart has two opposite-cell strata at an ascent: zero and nonzero.
At a descent its entire additive fibre lies in the reflected opposite cell.

## References

* R. J. Marsh and K. Rietsch, *Parametrizations of flag varieties*, Proposition 5.2.
-/

namespace SchubertOrbits

export SchubertGeometry (
  prefixFibre_zero
  prefixFibre_ascent
  prefixFibre_descent
  prefixFibre_ascent_zero_iff
  prefixFibre_ascent_nonzero_iff
)

end SchubertOrbits
