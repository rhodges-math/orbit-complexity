import Batteries.Tactic.Lint
import OrbitComplexity.SchubertGeometry.Connectedness.RichardsonPieces
import OrbitComplexity.SchubertGeometry.Cells.ClosureStability
import OrbitComplexity.SchubertGeometry.Cells.OppositeClosure
import OrbitComplexity.BruhatIntervals.Order.Interval

/-!
# Bruhat interval labels for the original Richardson pieces

The Weyl flag of an interval element lies in both Schubert closures. Rational
preimages in its ordinary cell and in the original Richardson target then give
a point of their specified scheme pullback. This proves that the nonempty piece
indices are exactly the Bruhat interval, without any normality assertion.

-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

namespace SchubertGeometry.CellContraction

universe u

private theorem pullback_nonempty_of_points
    {K : Type u} [Field K] {X Y Z : GroupActions.Variety K} {P : Scheme.{u}}
    (f : X.toOver ⟶ Z.toOver) (g : Y.toOver ⟶ Z.toOver)
    {fst : P ⟶ X.scheme} {snd : P ⟶ Y.scheme}
    (h : IsPullback fst snd f.left g.left)
    (x : X.points) (y : Y.points)
    (hxy : GroupActions.Variety.mapPoints f x = GroupActions.Variety.mapPoints g y) :
    Nonempty P := by
  have heq : f.left (X.pointMap x) = g.left (Y.pointMap y) := by
    calc
      f.left (X.pointMap x) = Z.pointMap (GroupActions.Variety.mapPoints f x) :=
        (GroupActions.Variety.pointMap_mapPoints f x).symm
      _ = Z.pointMap (GroupActions.Variety.mapPoints g y) := congrArg Z.pointMap hxy
      _ = g.left (Y.pointMap y) := GroupActions.Variety.pointMap_mapPoints g y
  obtain ⟨p, _, _⟩ := Scheme.exists_preimage_of_isPullback h
    (X.pointMap x) (Y.pointMap y) heq
  exact ⟨p⟩

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroups.ReductiveGroupData K)

/-- The Weyl flag of an interval label belongs to the original Richardson variety. -/
theorem weylFlag_mem_richardson (a b w : G.weylGroup)
    (haw : ReductiveGroups.WeylBruhatLE G.rootBase a w)
    (hwb : ReductiveGroups.WeylBruhatLE G.rootBase w b) :
    weylFlagPoint G w ∈
      Set.range (GroupActions.Variety.mapPoints (richardsonInclusion G a b)) := by
  rw [richardson_points_range]
  constructor
  · rw [schubertVariety_points_cells]
    refine Set.mem_iUnion₂.mpr ⟨w, hwb, ?_⟩
    rw [schubertCell_points_range]
    exact MulAction.mem_orbit_self _
  · rw [oppositeSchubert_points_cells]
    refine Set.mem_iUnion₂.mpr ⟨w, haw, ?_⟩
    rw [oppositeSchubertCell_points_range]
    exact MulAction.mem_orbit_self _

/-- Every interval label has a point in its original scheme-theoretic cell intersection. -/
theorem cellIntersection_nonempty_of_le (a b w : G.weylGroup)
    (haw : ReductiveGroups.WeylBruhatLE G.rootBase a w)
    (hwb : ReductiveGroups.WeylBruhatLE G.rootBase w b) :
    Nonempty (cellIntersection G a b w).left := by
  have hCell : weylFlagPoint G w ∈
      Set.range (GroupActions.Variety.mapPoints (schubertCellInclusion G w)) := by
    rw [schubertCell_points_range]
    exact MulAction.mem_orbit_self _
  obtain ⟨c, hc⟩ := hCell
  obtain ⟨x, hx⟩ := weylFlag_mem_richardson G a b w haw hwb
  exact pullback_nonempty_of_points (schubertCellInclusion G w)
    (richardsonInclusion G a b) (cellIntersection_pullback G a b w)
    c x (hc.trans hx.symm)

/-- The specified nonempty cell pieces have precisely the labels of the Bruhat interval. -/
def cellPieceIntervalEquiv (a b : G.weylGroup) :
    cellPieceIndices G a b ≃
      BruhatIntervals.bruhatInterval (ReductiveGroups.weylCoxeterSystem G.rootBase) a b where
  toFun i :=
    ⟨i.val, ⟨(SchubertGeometry.weyl_bruhat_iff G.rootBase a i.val).mp
        (cellPieceIndex_bounds G a b i).1,
      (SchubertGeometry.weyl_bruhat_iff G.rootBase i.val b).mp
        (cellPieceIndex_bounds G a b i).2⟩⟩
  invFun i :=
    ⟨i.val, cellIntersection_nonempty_of_le G a b i.val
      ((SchubertGeometry.weyl_bruhat_iff G.rootBase a i.val).mpr i.property.1)
      ((SchubertGeometry.weyl_bruhat_iff G.rootBase i.val b).mpr i.property.2)⟩
  left_inv i := by
    cases i
    rfl
  right_inv i := by
    cases i
    rfl

end SchubertGeometry.CellContraction
