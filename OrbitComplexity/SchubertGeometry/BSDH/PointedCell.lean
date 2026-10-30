import OrbitComplexity.SchubertGeometry.BSDH.OpenCell
import OrbitComplexity.SchubertGeometry.Cells.CellAffine
import OrbitComplexity.SchubertGeometry.Cells.SchubertPoints
import OrbitComplexity.GroupActions.Varieties.FullDimension
import Batteries.Tactic.Lint

/-! # A pointed affine chart for the longest-word endpoint

The longest Schubert cell is affine and open in the flag variety. The same cell
is open in a reduced-word Bott--Samelson variety, and its Weyl point gives a
rational point in the common chart.
-/

open AlgebraicGeometry CategoryTheory ReductiveGroups
open GroupActions

namespace SchubertGeometry

universe u

private theorem affine_of_over_iso {B : Scheme.{u}} {X Y : Over B}
    (E : X ≅ Y) [IsAffine Y.left] : IsAffine X.left :=
  IsAffine.of_isIso E.hom.left

/-- A reduced expression for the longest Weyl element has a common affine open
chart with the flag variety, an endpoint triangle, and a rational point. -/
theorem exists_pointed_longest_cell {K : Type u}
    [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K) (word : List G.rootBase.support)
    (hred : (weylCoxeterSystem G.rootBase).IsReduced word)
    (hw : simpleWeylWord G.rootBase word = G.longestElement) :
    ∃ c : (schubertCell G (simpleWeylWord G.rootBase word)).scheme ⟶
        bsdhScheme G word,
      IsOpenImmersion c ∧
      IsOpenImmersion (schubertCellInclusion G
        (simpleWeylWord G.rootBase word)).left ∧
      IsAffine (schubertCell G (simpleWeylWord G.rootBase word)).scheme ∧
      c ≫ bsdhMap G word =
        (schubertCellInclusion G (simpleWeylWord G.rootBase word)).left ∧
      ∃ k : Spec (.of K) ⟶
          (schubertCell G (simpleWeylWord G.rootBase word)).scheme,
        k ≫ (schubertCell G (simpleWeylWord G.rootBase word)).toSpec = 𝟙 _ := by
  let w := simpleWeylWord G.rootBase word
  let j := schubertCellInclusion G w
  have hd : IsDominant (schubertCellInclusion G G.longestElement).left :=
    ⟨longestCell_dense G⟩
  let : IsDominant j.left := by
    change IsDominant
      (schubertCellInclusion G (simpleWeylWord G.rootBase word)).left
    rw [hw]
    exact hd
  have hpre : IsPreimmersion j.left :=
    orbitInclusion_isPreimmersion (borelVariety G) (flagVariety G) (weylFlagPoint G w)
  let : IsImmersion j.left :=
    { toIsPreimmersion := hpre
      isLocallyClosed_range := by
        change IsLocallyClosed (Set.range
          ((orbitInclusion (borelVariety G) (flagVariety G) (weylFlagPoint G w)).left))
        rw [orbitInclusion_range]
        exact orbitImage_locallyClosed (borelVariety G) (flagVariety G)
          (weylFlagPoint G w) }
  have hj : IsOpenImmersion j.left :=
    GroupActions.Variety.isOpenImmersion_of_dominant j
  let A := MvPolynomial (Fin ((weylCoxeterSystem G.rootBase).length w)) K
  let : IsAffine (GroupActions.affineVariety K A).scheme := by
    change IsAffine (Spec (.of A))
    infer_instance
  let : IsAffine (GroupActions.affineVariety K
      (MvPolynomial (Fin ((weylCoxeterSystem G.rootBase).length w)) K)).toOver.left :=
    (inferInstance : IsAffine (Spec (.of A)))
  have ha : IsAffine (schubertCell G w).scheme :=
    affine_of_over_iso (schubertCellAffineIso G w)
  have hp : weylFlagPoint G w ∈ Set.range (Variety.mapPoints j) := by
    rw [schubertCell_points_range G w]
    exact MulAction.mem_orbit_self _
  obtain ⟨x, _⟩ := hp
  obtain ⟨c, hc, htriangle⟩ := bsdh_cell_open G word hred
  exact ⟨c, hc, hj, ha, htriangle, x.val, x.property⟩

end SchubertGeometry
