import OrbitComplexity.ReductiveGroups.Roots.Inversions.InversionLength
import OrbitComplexity.ReductiveGroups.Roots.Coxeter.CoxeterPresentation

/-!
# Faithfulness on roots and finiteness of the Weyl group

An element acting trivially on roots has no inversions, hence is the
identity by the proved minimum-length theorem. Finite root indices then
give a finite Weyl group, even when the ambient module has extra
directions. The associated Coxeter matrix consequently has no zero entries.
This does not prove injectivity of the Coxeter presentation map.
-/

namespace ReductiveGroups

variable {ι R M N : Type*} [CommRing R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [Finite ι] [IsDomain R]
  [P.IsCrystallographic] [P.IsReduced]

/-- The Weyl group acts faithfully on the finite root index set. -/
theorem weylGroupToPerm_injective (b : P.Base) :
    Function.Injective P.weylGroupToPerm := by
  apply (injective_iff_map_eq_one P.weylGroupToPerm).mpr
  intro w hw
  apply (rootInversionCount_eq_zero_iff b w).mp
  have hi : leftRootInversionIndices b w = ∅ := by
    ext i
    simp [map_inv, hw]
  simp [rootInversionCount, leftRootInversions, hi]

/-- The Weyl group is finite when its root index set is finite. -/
theorem weylGroup_finite (b : P.Base) : Finite P.weylGroup :=
  Finite.of_injective P.weylGroupToPerm (weylGroupToPerm_injective b)

/-- Every product of two simple reflections has finite positive order. -/
theorem simpleCoxeterMatrix_pos (b : P.Base) (i j : b.support) :
    0 < simpleCoxeterMatrix b i j := by
  let := weylGroup_finite b
  exact orderOf_pos _

/-- The inclusion is

```lean
2 ≤ simpleCoxeterMatrix b i j
```
-/
theorem simpleCoxeterMatrix_two_le (b : P.Base) {i j : b.support} (hij : i ≠ j) :
    2 ≤ simpleCoxeterMatrix b i j := by
  have hp := simpleCoxeterMatrix_pos b i j
  have hn := (simpleCoxeterMatrix b).off_diagonal i j hij
  omega

end ReductiveGroups
