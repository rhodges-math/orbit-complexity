import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Data.Finset.Powerset

/-!
# Connected unions of connected blocks in a graph quotient

The quotient graph has an edge only when an original graph edge
crosses two blocks. Connectivity of a collection of quotient vertices
therefore lifts to connectivity of the union of their original blocks.
-/

noncomputable section

namespace ReductiveGroups

variable {V I : Type*}
attribute [local instance] Classical.decEq

/-- Quotient adjacency is witnessed by a graph edge crossing
two blocks. The blocks need not be disjoint for this connectivity lemma. -/
def supportQuotientGraph (G : SimpleGraph V) (B : I → Set V) : SimpleGraph I :=
  SimpleGraph.fromRel (fun i j => ∃ u ∈ B i, ∃ v ∈ B j, G.Adj u v)

/-- There exist elements satisfying

```lean
∃ u ∈ B i, ∃ v ∈ B j, G.Adj u v
```
-/
theorem supportQuotientGraph_adj_crossing
    (G : SimpleGraph V) (B : I → Set V) {i j : I}
    (h : (supportQuotientGraph G B).Adj i j) :
    ∃ u ∈ B i, ∃ v ∈ B j, G.Adj u v := by
  rcases ((SimpleGraph.fromRel_adj _ i j).mp h).2 with h | h
  · exact h
  · obtain ⟨v, hv, u, hu, hvu⟩ := h
    exact ⟨u, hu, v, hv, hvu.symm⟩

/-- The union of blocks indexed by a finite set. -/
def supportBlockUnion (B : I → Set V) (S : Finset I) : Set V :=
  ⋃ i ∈ S, B i

/-- The equality is

```lean
supportBlockUnion B {i} = B i
```
-/
@[simp] theorem supportBlockUnion_singleton (B : I → Set V) (i : I) :
    supportBlockUnion B {i} = B i := by
  ext v
  simp [supportBlockUnion]

/-- The equality is

```lean
supportBlockUnion B (insert i S) = B i ∪ supportBlockUnion B S
```
-/
@[simp] theorem supportBlockUnion_insert (B : I → Set V) (S : Finset I) (i : I) :
    supportBlockUnion B (insert i S) = B i ∪ supportBlockUnion B S := by
  ext v
  simp [supportBlockUnion]

/-- A connected set of quotient vertices has connected union,
provided every block in that set is itself induced-connected and nonempty.
 -/
theorem SupportBlockUnion.connected_of_quotient_connected
    (G : SimpleGraph V) (B : I → Set V) (K : Finset I)
    (hK : K.Nonempty)
    (hblock : ∀ i ∈ K, (G.induce (B i)).Connected)
    (hquot : ((supportQuotientGraph G B).induce (↑K : Set I)).Connected) :
    (G.induce (supportBlockUnion B K)).Connected := by
  classical
  let Q := supportQuotientGraph G B
  let C : Finset (Finset I) :=
    K.powerset.filter (fun S => (G.induce (supportBlockUnion B S)).Connected)
  have hC : C.Nonempty := by
    obtain ⟨i, hi⟩ := hK
    refine ⟨{i}, ?_⟩
    simp only [C, Finset.mem_filter, Finset.mem_powerset]
    refine ⟨Finset.singleton_subset_iff.mpr hi, ?_⟩
    rw [supportBlockUnion_singleton]
    exact hblock i hi
  obtain ⟨S, hSC, hmax⟩ := C.exists_max_image Finset.card hC
  have hSK : S ⊆ K := Finset.mem_powerset.mp (Finset.mem_filter.mp hSC).1
  have hSconn : (G.induce (supportBlockUnion B S)).Connected :=
    (Finset.mem_filter.mp hSC).2
  by_cases hproper : S = K
  · subst S
    exact hSconn
  · have hS : S.Nonempty := by
      by_contra hn
      have hz : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
      obtain ⟨v, hv⟩ := hSconn.nonempty
      have : v ∈ supportBlockUnion B S := hv
      simp [supportBlockUnion, hz] at this
    obtain ⟨j, hjS⟩ := hS
    have hjK : j ∈ K := hSK hjS
    obtain ⟨i, hiK, hiS⟩ : ∃ i ∈ K, i ∉ S := by
      by_contra hn
      push Not at hn
      exact hproper (Finset.Subset.antisymm hSK (fun x hx => hn x hx))
    let j' : (↑K : Set I) := ⟨j, hjK⟩
    let i' : (↑K : Set I) := ⟨i, hiK⟩
    let T : Set (↑K : Set I) := {x | x.val ∈ S}
    obtain ⟨p⟩ := hquot j' i'
    obtain ⟨d, _, hdS, hdi⟩ := p.exists_boundary_dart T hjS hiS
    let j₀ : I := d.fst.val
    let i₀ : I := d.snd.val
    have hj₀S : j₀ ∈ S := hdS
    have hi₀S : i₀ ∉ S := hdi
    have hi₀K : i₀ ∈ K := d.snd.property
    have hadj : Q.Adj j₀ i₀ := d.adj
    obtain ⟨u, hu, v, hv, huv⟩ :=
      supportQuotientGraph_adj_crossing G B hadj
    have huS : u ∈ supportBlockUnion B S := by
      simp only [supportBlockUnion, Set.mem_iUnion]
      exact ⟨j₀, hj₀S, hu⟩
    have hnew : (G.induce (supportBlockUnion B (insert i₀ S))).Connected := by
      rw [supportBlockUnion_insert]
      exact G.connected_induce_union (hblock i₀ hi₀K).preconnected
        hSconn.preconnected hv huS huv.symm
    have hTmem : insert i₀ S ∈ C := by
      simp only [C, Finset.mem_filter, Finset.mem_powerset]
      exact ⟨Finset.insert_subset hi₀K hSK, hnew⟩
    have hle := hmax (insert i₀ S) hTmem
    simp [hi₀S] at hle

end ReductiveGroups
