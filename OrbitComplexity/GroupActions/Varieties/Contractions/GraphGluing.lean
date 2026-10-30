import Batteries.Tactic.Lint
import Mathlib.Topology.Connected.Basic

/-!
# Connected covers linked by a graph

Preconnected sets containing specified anchors are joined by preconnected bridge sets. Reachability
from one anchor forces the connected components of all anchors to agree. If the anchored sets
cover the ambient space, the space is connected. No separation or finiteness assumption is needed.
-/

namespace GroupActions

open Set TopologicalSpace

universe u v

variable {X : Type u} [TopologicalSpace X] {I : Type v}

/-- A chain of preconnected bridges identifies the connected components of its endpoint anchors. -/
theorem connectedComponent_eq_of_path (r : I → I → Prop) (anchor : I → X)
    (hbridge : ∀ i j, r i j → ∃ s : Set X,
      IsPreconnected s ∧ anchor i ∈ s ∧ anchor j ∈ s)
    {i j : I} (hpath : Relation.ReflTransGen r i j) :
    connectedComponent (anchor i) = connectedComponent (anchor j) := by
  induction hpath with
  | refl => rfl
  | @tail j k _ hjk ih =>
      obtain ⟨s, hs, hj, hk⟩ := hbridge j k hjk
      exact ih.trans (connectedComponent_eq ((hs.subset_connectedComponent hj) hk))

/-- A cover by preconnected anchored sets is connected when bridge sets link every anchor to
a specified root. This applies in particular to a finite connected graph of pieces and curves. -/
theorem connectedSpace_of_graph_cover (r : I → I → Prop) (root : I)
    (anchor : I → X) (piece : I → Set X)
    (hpiece : ∀ i, IsPreconnected (piece i))
    (hanchor : ∀ i, anchor i ∈ piece i)
    (hcover : ∀ x : X, ∃ i, x ∈ piece i)
    (hbridge : ∀ i j, r i j → ∃ s : Set X,
      IsPreconnected s ∧ anchor i ∈ s ∧ anchor j ∈ s)
    (hpath : ∀ i, Relation.ReflTransGen r root i) : ConnectedSpace X := by
  have hfull : connectedComponent (anchor root) = (Set.univ : Set X) := by
    ext x
    constructor
    · intro _
      trivial
    · intro _
      obtain ⟨i, hi⟩ := hcover x
      have hx : x ∈ connectedComponent (anchor i) :=
        (hpiece i).subset_connectedComponent (hanchor i) hi
      rw [connectedComponent_eq_of_path r anchor hbridge (hpath i)]
      exact hx
  apply connectedSpace_iff_univ.mpr
  rw [← hfull]
  exact isConnected_connectedComponent

end GroupActions
