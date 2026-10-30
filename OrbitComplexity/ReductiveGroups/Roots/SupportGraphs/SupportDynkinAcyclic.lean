import OrbitComplexity.ReductiveGroups.Roots.SupportGraphs.ConnectedSupportLeaf
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# Support Dynkin Acyclic

The underlying Dynkin graph is acyclic. A copy of a cycle
would give a finite connected induced simple-root support in which every
vertex has at least two neighbors, contradicting the proved leaf theorem. -/

noncomputable section
set_option linter.style.haveILetI false

namespace ReductiveGroups

private theorem isAcyclic_of_connected_induce_has_leaf
    {V : Type*} (G : SimpleGraph V)
    (hleaf : ∀ K : Finset V, K.Nonempty →
      (G.induce (↑K : Set V)).Connected →
      ∃ i ∈ K, ∀ j ∈ K, ∀ k ∈ K,
        G.Adj i j → G.Adj i k → j = k) :
    G.IsAcyclic := by
  classical
  apply SimpleGraph.isAcyclic_iff_free_cycleGraph.mpr
  intro n hn hcopy
  obtain ⟨t, rfl⟩ : ∃ t : ℕ, n = t + 3 := ⟨n - 3, by omega⟩
  obtain ⟨f⟩ := hcopy
  let K : Finset V := Finset.univ.image f
  have hK : K.Nonempty := by
    refine ⟨f 0, ?_⟩
    exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
  let g : (SimpleGraph.cycleGraph (t + 3)) →g G.induce (↑K : Set V) := {
    toFun := fun i => ⟨f i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
    map_rel' := by
      intro i j hij
      exact f.toHom.map_rel hij
  }
  have hgSurj : Function.Surjective g := by
    rintro ⟨v, hv⟩
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
    exact ⟨i, rfl⟩
  have hgInj : Function.Injective g := by
    intro i j hij
    exact f.injective (congrArg Subtype.val hij)
  let c : SimpleGraph.Copy (SimpleGraph.cycleGraph (t + 3))
      (G.induce (↑K : Set V)) := ⟨g, hgInj⟩
  have hconn : (G.induce (↑K : Set V)).Connected := by
    have hcyc : (SimpleGraph.cycleGraph (t + 3)).Connected := by
      simpa only [Nat.add_assoc] using
        (SimpleGraph.cycleGraph_connected (n := t + 2))
    exact hcyc.map g hgSurj
  obtain ⟨i, hiK, hi⟩ := hleaf K hK hconn
  obtain ⟨j, hj⟩ := hgSurj (⟨i, hiK⟩ : (↑K : Set V))
  have hdegreeLe : (G.induce (↑K : Set V)).degree (g j) ≤ 1 := by
    rw [SimpleGraph.degree]
    apply Finset.card_le_one.mpr
    intro a ha b hb
    apply Subtype.ext
    have hga : G.Adj i a.val := by
      have ha' : (G.induce (↑K : Set V)).Adj (g j) a := by simpa using ha
      simpa [hj] using ha'
    have hgb : G.Adj i b.val := by
      have hb' : (G.induce (↑K : Set V)).Adj (g j) b := by simpa using hb
      simpa [hj] using hb'
    exact hi a.val a.property b.val b.property hga hgb
  have hdegreeGe : 2 ≤ (G.induce (↑K : Set V)).degree (g j) := by
    rw [← SimpleGraph.cycleGraph_degree_three_le (v := j)]
    exact c.degree_le j
  omega

/-- The graph on all simple-root vertices, with edges given by
nonzero integral Cartan pairings, has no cycle. This includes all finite
crystallographic types and empty or singleton support. -/
theorem supportDynkinGraph_isAcyclic
    {ι R M N : Type*} [CommRing R] [CharZero R] [IsDomain R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing ι R M N} [Finite ι] [P.IsCrystallographic]
    (b : P.Base) : (supportDynkinGraph b).IsAcyclic := by
  classical
  letI : Fintype b.support := Fintype.ofFinite b.support
  apply isAcyclic_of_connected_induce_has_leaf
  intro K hK hconn
  exact connectedSupport_exists_leaf b K hK hconn

end ReductiveGroups
