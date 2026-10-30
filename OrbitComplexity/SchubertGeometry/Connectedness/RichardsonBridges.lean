import Batteries.Tactic.Lint
import OrbitComplexity.SchubertGeometry.Connectedness.RichardsonInterval
import OrbitComplexity.SchubertGeometry.Connectedness.RootCurveContainment
import OrbitComplexity.GroupActions.Varieties.ProjectiveConnected

/-!
# Specified root curves join the specified cell-piece anchors

-/

open AlgebraicGeometry CategoryTheory

noncomputable section

namespace SchubertGeometry.CellContraction

universe u

private theorem integral_range {X Y : Scheme} [IsIntegral X] (f : X ⟶ Y) :
    _root_.IsPreconnected (Set.range f) :=
  isPreconnected_range f.continuous

private theorem curvePoint_ambient {K : Type u} [Field K]
    {P X F : GroupActions.Variety K} (c : P.toOver ⟶ X.toOver)
    (j : X.toOver ⟶ F.toOver) (d : P.toOver ⟶ F.toOver) (h : c ≫ j = d)
    (p : P.points) (w : F.points) (hp : GroupActions.Variety.mapPoints d p = w) :
    j.left (c.left (P.pointMap p)) = F.pointMap w := by
  rw [← GroupActions.Variety.pointMap_mapPoints c p,
    ← GroupActions.Variety.pointMap_mapPoints j (GroupActions.Variety.mapPoints c p),
    ← GroupActions.Variety.mapPoints_comp, h, hp]

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroups.ReductiveGroupData K)

/-- a specified positive-root reflection curve supplies a preconnected bridge
between its two specified nonempty cell-piece anchors. -/
theorem rootCurve_piece_bridge (a b : G.weylGroup)
    (p q : cellPieceIndices G a b) (w : G.weylGroup) (i : G.rootBase.support)
    (hroot : G.rootBase.IsPos (G.rootSystem.weylGroupToPerm w i.val))
    (hpos : G.rootBase.IsPos (G.rootSystem.weylGroupToPerm p.val⁻¹
      (G.rootSystem.weylGroupToPerm w i.val)))
    (hxy : ReductiveGroups.WeylBruhatLE G.rootBase p.val q.val)
    (hy : q.val = RootPairing.weylGroup.ofIdx G.rootSystem
      (G.rootSystem.weylGroupToPerm w i.val) * p.val) :
    ∃ s : Set (richardsonVariety G a b).scheme,
      _root_.IsPreconnected s ∧ cellPieceAnchor G a b p ∈ s ∧ cellPieceAnchor G a b q ∈ s := by
  have hxy' : ReductiveGroups.WeylBruhatLE G.rootBase p.val
      (RootPairing.weylGroup.ofIdx G.rootSystem
        (G.rootSystem.weylGroupToPerm w i.val) * p.val) := hy ▸ hxy
  have hyb : ReductiveGroups.WeylBruhatLE G.rootBase
      (RootPairing.weylGroup.ofIdx G.rootSystem
        (G.rootSystem.weylGroupToPerm w i.val) * p.val) b :=
    hy ▸ (cellPieceIndex_bounds G a b q).2
  let c := rootCurveRichardson G w i a p.val b hroot hpos
    (cellPieceIndex_bounds G a b p).1 hxy' hyb
  let P := GroupActions.projectiveVariety K (ULift.{u} (Fin 2))
  let : IsIntegral P.scheme := GroupActions.projectiveScheme_integral K (ULift.{u} (Fin 2))
  let p0 := GroupActions.Variety.mapPoints (projectiveLineChart K ⟨0⟩)
    (GroupActions.additivePointsEquiv K 0)
  let p1 := GroupActions.Variety.mapPoints (projectiveLineChart K ⟨1⟩)
    (GroupActions.additivePointsEquiv K 0)
  have hc : c ≫ richardsonInclusion G a b = rootCurveProjective G w i p.val hpos :=
    rootCurveRichardson_comp G w i a p.val b hroot hpos
      (cellPieceIndex_bounds G a b p).1 hxy' hyb
  refine ⟨Set.range c.left, integral_range (X := P.scheme) c.left, ?_, ?_⟩
  · refine ⟨P.pointMap p0, ?_⟩
    apply (richardsonInclusion G a b).left.isEmbedding.injective
    exact (curvePoint_ambient c (richardsonInclusion G a b)
      (rootCurveProjective G w i p.val hpos) hc p0 (weylFlagPoint G p.val)
      (rootCurveProjective_at_zero G w i p.val hpos)).trans
        (cellPieceAnchor_flag G a b p).symm
  · refine ⟨P.pointMap p1, ?_⟩
    apply (richardsonInclusion G a b).left.isEmbedding.injective
    have he : GroupActions.Variety.mapPoints (rootCurveProjective G w i p.val hpos) p1 =
        weylFlagPoint G q.val := by
      rw [hy]
      exact rootCurveProjective_at_infinity G w i p.val hpos
    exact (curvePoint_ambient c (richardsonInclusion G a b)
      (rootCurveProjective G w i p.val hpos) hc p1 (weylFlagPoint G q.val) he).trans
        (cellPieceAnchor_flag G a b q).symm

end SchubertGeometry.CellContraction
