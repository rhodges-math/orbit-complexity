import OrbitComplexity.SchubertGeometry.FlagVariety.UnipotentChart
import OrbitComplexity.GroupActions.Varieties.AffineDimension
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupRootCount

/-!
# Dimension of a unipotent subgroup

The root-product affine-space chart computes the dimension of the unipotent subgroup.
Its number of coordinates equals the inversion count of the longest Weyl element.

## Main results

* `SchubertGeometry.unipotentVariety_dim`: the unipotent dimension formula.
-/

namespace SchubertGeometry

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroups.ReductiveGroupData K)

/-- The unipotent subgroup has dimension the inversion count of the longest Weyl element. -/
theorem unipotentVariety_dim :
    (GroupActions.unipotentVariety G).dim =
      ReductiveGroups.rootInversionCount G.rootBase G.longestElement := by
  rw [← GroupActions.Variety.dim_eq_of_iso _ (unipotentChart G),
    GroupActions.dim_affineVariety,
    MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite,
    ringKrullDim_eq_zero_of_field, zero_add]
  simp only [Nat.card_fin, G.natCard_borelCharacters]

end SchubertGeometry
