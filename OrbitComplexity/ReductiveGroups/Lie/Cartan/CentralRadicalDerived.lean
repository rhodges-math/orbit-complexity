import OrbitComplexity.ReductiveGroups.Lie.Cartan.CentralRadicalQuotient
import OrbitComplexity.ReductiveGroups.Lie.Cartan.CentralExtensionSplitting
import OrbitComplexity.ReductiveGroups.Lie.Cartan.SplitCentralDerived

/-!
# Central Radical Derived

The derived algebra of a finite-dimensional characteristic-zero Lie
algebra with central solvable radical is Killing. -/

noncomputable section
namespace ReductiveGroups

variable {K L : Type*} [Field K] [CharZero K] [LieRing L]
  [LieAlgebra K L] [Module.Finite K L] [LieAlgebra.HasCentralRadical K L]

/-- The derived algebra is isomorphic to the quotient by the center,
using a proved splitting of the central extension. -/
def derivedLieEquivCenterQuotient :
    LieAlgebra.derivedSeries K L 1 ≃ₗ⁅K⁆ (L ⧸ LieAlgebra.center K L) := by
  let := centralRadical_centerQuotient_isKilling (K := K) (L := L)
  let E := centerLieExtension (K := K) (L := L)
  let h := centralExtension_exists_lieSection E
    (centerLieExtension_incl_central (K := K) (L := L))
  let t := Classical.choose h
  have ht := Classical.choose_spec h
  exact (centralExtensionDerivedLieEquiv E
    (centerLieExtension_incl_central (K := K) (L := L)) t ht).symm

/-- Reductivity of the Lie algebra supplies Killing nondegeneracy on its
derived algebra, not on its possibly nonzero center. -/
theorem centralRadical_derived_isKilling :
    LieAlgebra.IsKilling K (LieAlgebra.derivedSeries K L 1) := by
  let := centralRadical_centerQuotient_isKilling (K := K) (L := L)
  exact (derivedLieEquivCenterQuotient (K := K) (L := L)).symm.isKilling

/-- The derived algebra has trivial solvable radical. -/
theorem centralRadical_derived_hasTrivialRadical :
    LieAlgebra.HasTrivialRadical K (LieAlgebra.derivedSeries K L 1) := by
  let := centralRadical_derived_isKilling (K := K) (L := L)
  infer_instance

end ReductiveGroups
