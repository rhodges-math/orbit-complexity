import OrbitComplexity.GroupActions.Varieties.OppositeUnipotentVariety
import OrbitComplexity.SchubertGeometry.FlagVariety.UnipotentDimension

/-!
# Affine coordinates on the opposite unipotent subgroup

Conjugation by the longest Weyl representative transports the root-product affine-space
chart to the opposite unipotent subgroup and preserves its dimension.

## Main definitions

* `SchubertGeometry.oppositeUnipotentChart`: the opposite affine-space chart.

## Main results

* `SchubertGeometry.oppositeUnipotentVariety_dim`: the opposite unipotent dimension formula.
-/

open CategoryTheory AlgebraicGeometry ReductiveGroups TauCeti

namespace SchubertGeometry

noncomputable section

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

private def unipotentOppositeIso :
    (GroupActions.unipotentVariety G).toOver ≅
      (GroupActions.oppositeUnipotentVariety G).toOver := by
  let F := (forget₂ (FiniteTypeCommHopfAlgCat.{u, u} K) (CommHopfAlgCat.{u} K)) ⋙
    (forget₂ (CommHopfAlgCat.{u} K) (CommBialgCat.{u} K)) ⋙
    (forget₂ (CommBialgCat.{u} K) (CommAlgCat.{u} K))
  let e := F.mapIso G.oppositeUnipotentIso
  exact (algSpec (CommRingCat.of K)).mapIso e.op

/-- The opposite unipotent subgroup has dimension the longest Weyl inversion count. -/
theorem oppositeUnipotentVariety_dim :
    (GroupActions.oppositeUnipotentVariety G).dim =
      rootInversionCount G.rootBase G.longestElement := by
  rw [← GroupActions.Variety.dim_eq_of_iso _ (unipotentOppositeIso G), unipotentVariety_dim]

end

end SchubertGeometry
