import Batteries.Tactic.Lint
import OrbitComplexity.SchubertGeometry.Connectedness.CellContractionScheme
import OrbitComplexity.SchubertGeometry.Cells.RichardsonStrata
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# The specified connected cell pieces cover the Richardson target

Only nonempty original cell pullbacks are used as vertices. Their specified
Richardson images are preconnected, contain their specified Weyl anchors and
cover every scheme point. The existing two-cell decomposition places their
indices in the prescribed Bruhat interval without any normality argument.

-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

namespace SchubertGeometry.CellContraction

universe u

private theorem pointFlag_value {K : Type u} [Field K]
    (X : GroupActions.Variety K) {Y : Scheme.{u}}
    (a : Spec (.of K) ⟶ Y) (f : Y ⟶ X.scheme) (x : X.points)
    (h : a ≫ f = (X.pointsEquivOverHom x).left) :
    f (a (IsLocalRing.closedPoint K)) = X.pointMap x := by
  have hv := congrArg (fun m : Spec (.of K) ⟶ X.scheme =>
    m (IsLocalRing.closedPoint K)) h
  change f (a (IsLocalRing.closedPoint K)) = x.val (IsLocalRing.closedPoint K) at hv
  exact hv

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroups.ReductiveGroupData K)

/-- The indices of the specified nonempty closed cell intersections. -/
abbrev cellPieceIndices (a b : G.weylGroup) :=
  {w : G.weylGroup // Nonempty (cellIntersection G a b w).left}

/-- The specified Richardson image of a nonempty cell intersection. -/
def cellPieceImage (a b : G.weylGroup) (i : cellPieceIndices G a b) :
    Set (richardsonVariety G a b).scheme :=
  Set.range (pullback.snd (schubertCellInclusion G i.val) (richardsonInclusion G a b)).left

/-- The specified Weyl anchor, as a point of the original Richardson target. -/
def cellPieceAnchor (a b : G.weylGroup) (i : cellPieceIndices G a b) :
    (richardsonVariety G a b).scheme :=
  cellRichardsonAnchor G a b i.val i.property (IsLocalRing.closedPoint K)

/-- Each specified piece image is preconnected. -/
theorem cellPieceImage_preconnected (a b : G.weylGroup) (i : cellPieceIndices G a b) :
    _root_.IsPreconnected (cellPieceImage G a b i) := by
  let := cellIntersection_connected G a b i.val i.property
  exact isPreconnected_range
    (pullback.snd (schubertCellInclusion G i.val) (richardsonInclusion G a b)).left.continuous

/-- Its specified anchor belongs to the same original piece image. -/
theorem cellPieceAnchor_mem (a b : G.weylGroup) (i : cellPieceIndices G a b) :
    cellPieceAnchor G a b i ∈ cellPieceImage G a b i := by
  refine ⟨cellOrigin G a b i.val i.property (IsLocalRing.closedPoint K), ?_⟩
  exact (Scheme.Hom.comp_apply _ _ _).symm

/-- Each specified piece anchor has its specified Weyl flag as ambient scheme point. -/
theorem cellPieceAnchor_flag (a b : G.weylGroup) (i : cellPieceIndices G a b) :
    (richardsonInclusion G a b).left (cellPieceAnchor G a b i) =
      (flagVariety G).pointMap (weylFlagPoint G i.val) := by
  exact pointFlag_value (flagVariety G)
    (cellRichardsonAnchor G a b i.val i.property) (richardsonInclusion G a b).left
    (weylFlagPoint G i.val) (cellRichardsonAnchor_flag G a b i.val i.property)

/-- The specified nonempty pieces cover all scheme points of the original target. -/
theorem cellPieceImages_cover (a b : G.weylGroup)
    (x : (richardsonVariety G a b).scheme) :
    ∃ i : cellPieceIndices G a b, x ∈ cellPieceImage G a b i := by
  obtain ⟨w, y, hy⟩ := schubertCells_cover G ((richardsonInclusion G a b).left x)
  obtain ⟨z, _, hz⟩ := Scheme.exists_preimage_of_isPullback
    (cellIntersection_pullback G a b w) y x hy
  exact ⟨⟨w, ⟨z⟩⟩, z, hz⟩

/-- Nonempty specified cell pieces have their labels in the prescribed Bruhat interval. -/
theorem cellPieceIndex_bounds (a b : G.weylGroup) (i : cellPieceIndices G a b) :
    ReductiveGroups.WeylBruhatLE G.rootBase a i.val ∧
      ReductiveGroups.WeylBruhatLE G.rootBase i.val b := by
  let z := Classical.choice i.property
  let x := (pullback.snd (schubertCellInclusion G i.val)
    (richardsonInclusion G a b)).left z
  obtain ⟨u, v, hau, huv, hvb, hx⟩ := richardsonVariety_cells_cover G a b x
  rw [richardsonCellInclusion_range] at hx
  have hw : (richardsonInclusion G a b).left x ∈
      Set.range (schubertCellInclusion G i.val).left := by
    refine ⟨(pullback.fst (schubertCellInclusion G i.val)
      (richardsonInclusion G a b)).left z, ?_⟩
    have hs := congrArg Over.Hom.left
      (pullback.condition (f := schubertCellInclusion G i.val)
        (g := richardsonInclusion G a b))
    simpa only [Over.comp_left, Scheme.Hom.comp_apply] using
      congrArg (fun f : (cellIntersection G a b i.val).left ⟶
        (flagVariety G).scheme => f z) hs
  have hiv : i.val = v := schubertCells_disjoint G hw hx.1
  exact ⟨hiv.symm ▸ hau.trans huv, hiv.symm ▸ hvb⟩

end SchubertGeometry.CellContraction
