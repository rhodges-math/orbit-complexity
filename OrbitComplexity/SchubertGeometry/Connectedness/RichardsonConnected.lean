import Batteries.Tactic.Lint
import OrbitComplexity.GroupActions.Varieties.Contractions.GraphGluing
import OrbitComplexity.BruhatIntervals.Graph.IntervalPaths
import OrbitComplexity.SchubertGeometry.Connectedness.RichardsonBridges
import OrbitComplexity.SchubertGeometry.Connectedness.CoverRoots

/-!
# Reflection-curve gluing on the original Richardson variety

-/

open AlgebraicGeometry CategoryTheory

noncomputable section

namespace SchubertGeometry.CellContraction

universe u

private theorem predicate_transport {I : Type*} (P : I → Prop)
    {i j : I} (he : i = j) (hj : P j) : P i := he.symm ▸ hj

private theorem connected_graph_reindex {I J L X : Type*} [TopologicalSpace X]
    (r : L → L → Prop) (label : I → L) (label' : J → L) (e : I ≃ J)
    (he : ∀ j, label (e.symm j) = label' j) (root : J)
    (anchor : I → X) (piece : I → Set X)
    (hpiece : ∀ i, _root_.IsPreconnected (piece i))
    (hanchor : ∀ i, anchor i ∈ piece i) (hcover : ∀ x, ∃ i, x ∈ piece i)
    (hbridge : ∀ i j, r (label i) (label j) → ∃ s : Set X,
      _root_.IsPreconnected s ∧ anchor i ∈ s ∧ anchor j ∈ s)
    (hpath : ∀ j, Relation.ReflTransGen
      (fun p q : J => r (label' p) (label' q)) root j) : ConnectedSpace X := by
  apply GroupActions.connectedSpace_of_graph_cover
    (fun p q : J => r (label' p) (label' q)) root
    (fun j => anchor (e.symm j)) (fun j => piece (e.symm j))
    (fun j => hpiece (e.symm j)) (fun j => hanchor (e.symm j))
  · intro x
    obtain ⟨i, hi⟩ := hcover x
    refine ⟨e i, ?_⟩
    simpa only [Equiv.symm_apply_apply] using hi
  · intro p q hpq
    apply hbridge (e.symm p) (e.symm q)
    rw [he, he]
    exact hpq
  · exact hpath

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroups.ReductiveGroupData K)

private theorem cover_bridge (a b : G.weylGroup) (p q : cellPieceIndices G a b) :
    let : PartialOrder G.weylGroup :=
      (ReductiveGroups.weylCoxeterSystem G.rootBase).bruhatPartialOrder
    p.val ⋖ q.val → ∃ s : Set (richardsonVariety G a b).scheme,
      _root_.IsPreconnected s ∧ cellPieceAnchor G a b p ∈ s ∧ cellPieceAnchor G a b q ∈ s := by
  let : PartialOrder G.weylGroup :=
    (ReductiveGroups.weylCoxeterSystem G.rootBase).bruhatPartialOrder
  dsimp only
  intro hpq
  obtain ⟨β, hβ, hy, hpos⟩ := bruhatCover_root G p.val q.val hpq
  obtain ⟨w, i, hwi⟩ := rootCurve_simple_presentation G β hβ
  exact rootCurve_piece_bridge G a b p q w i
    (predicate_transport G.rootBase.IsPos hwi hβ)
    (predicate_transport (fun r => G.rootBase.IsPos
      (G.rootSystem.weylGroupToPerm p.val⁻¹ r)) hwi hpos)
    ((SchubertGeometry.weyl_bruhat_iff G.rootBase p.val q.val).mpr hpq.le)
    (predicate_transport (fun r => q.val = RootPairing.weylGroup.ofIdx G.rootSystem r * p.val)
      hwi hy)

/-- The original Richardson target is connected by its specified cell contractions
and reflection-root curve graph, without a normality or integrality input. -/
theorem richardson_connected_graph (a b : G.weylGroup)
    (hab : ReductiveGroups.WeylBruhatLE G.rootBase a b) :
    ConnectedSpace (richardsonVariety G a b).scheme := by
  let cs := ReductiveGroups.weylCoxeterSystem G.rootBase
  let : PartialOrder G.weylGroup := cs.bruhatPartialOrder
  let I := BruhatIntervals.bruhatInterval cs a b
  let e := cellPieceIntervalEquiv G a b
  have hab' : cs.BruhatLE a b := (SchubertGeometry.weyl_bruhat_iff G.rootBase a b).mp hab
  let root : I := ⟨a, cs.bruhatLE_refl a, hab'⟩
  have heval (v : I) : (e.symm v).val = v.val := rfl
  exact connected_graph_reindex (X := (richardsonVariety G a b).scheme)
    (fun p q : G.weylGroup => p ⋖ q) (fun p : cellPieceIndices G a b => p.val)
    (fun p : I => p.val) e heval root (cellPieceAnchor G a b) (cellPieceImage G a b)
    (cellPieceImage_preconnected G a b) (cellPieceAnchor_mem G a b)
    (cellPieceImages_cover G a b) (cover_bridge G a b)
    (BruhatIntervals.bruhatInterval_cover_reachable cs a b hab')

end SchubertGeometry.CellContraction
