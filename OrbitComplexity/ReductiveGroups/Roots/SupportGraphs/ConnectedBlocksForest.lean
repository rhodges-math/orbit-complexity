import OrbitComplexity.ReductiveGroups.Roots.SupportGraphs.SupportQuotientConnected
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# Connected Blocks Forest

Crossing edges between disjoint connected vertex blocks in a forest. -/

namespace ReductiveGroups

variable {V : Type*} (G : SimpleGraph V)

/-- A forest has at most one edge between two disjoint induced-connected
vertex sets. The edges are compared as unordered edges. -/
theorem crossing_edge_unique_of_acyclic
    (hforest : G.IsAcyclic) {A B : Set V}
    (hdisj : Disjoint A B)
    (hA : (G.induce A).Connected) (hB : (G.induce B).Connected)
    {u₁ u₂ v₁ v₂ : V}
    (hu₁ : u₁ ∈ A) (hu₂ : u₂ ∈ A)
    (hv₁ : v₁ ∈ B) (hv₂ : v₂ ∈ B)
    (he₁ : G.Adj u₁ v₁) (he₂ : G.Adj u₂ v₂) :
    s(u₁, v₁) = s(u₂, v₂) := by
  classical
  let D := G.deleteEdges {s(u₁, v₁)}
  let hAmap : G.induce A →g D := {
    toFun := Subtype.val
    map_rel' := by
      intro x y hxy
      apply SimpleGraph.deleteEdges_adj.mpr
      refine ⟨hxy, ?_⟩
      simp only [Set.mem_singleton_iff]
      intro he
      rcases Sym2.eq_iff.mp he with h | h
      · exact (Set.disjoint_left.mp hdisj) (by simpa only [h.2] using y.property) hv₁
      · exact (Set.disjoint_left.mp hdisj) (by simpa only [h.1] using x.property) hv₁
  }
  let hBmap : G.induce B →g D := {
    toFun := Subtype.val
    map_rel' := by
      intro x y hxy
      apply SimpleGraph.deleteEdges_adj.mpr
      refine ⟨hxy, ?_⟩
      simp only [Set.mem_singleton_iff]
      intro he
      rcases Sym2.eq_iff.mp he with h | h
      · exact (Set.disjoint_left.mp hdisj) hu₁
          (by simpa only [h.1] using x.property)
      · exact (Set.disjoint_left.mp hdisj) hu₁
          (by simpa only [h.2] using y.property)
  }
  by_contra hne
  have he₂D : D.Adj u₂ v₂ := by
    apply SimpleGraph.deleteEdges_adj.mpr
    exact ⟨he₂, by simpa only [Set.mem_singleton_iff] using Ne.symm hne⟩
  have hreachA : D.Reachable u₁ u₂ :=
    (hA.preconnected ⟨u₁, hu₁⟩ ⟨u₂, hu₂⟩).map hAmap
  have hreachB : D.Reachable v₂ v₁ :=
    (hB.preconnected ⟨v₂, hv₂⟩ ⟨v₁, hv₁⟩).map hBmap
  have hreach : D.Reachable u₁ v₁ :=
    (hreachA.trans he₂D.reachable).trans hreachB
  exact ((SimpleGraph.isBridge_iff.mp
    ((SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp hforest) he₁)) hreach)

/-- Reachability in the quotient lifts between arbitrary vertices of the
corresponding connected blocks. -/
theorem supportQuotientGraph_reachable_lift {I : Type*}
    (B : I → Set V)
    (hconn : ∀ i, (G.induce (B i)).Connected)
    {i j : I} (hij : (supportQuotientGraph G B).Reachable i j)
    {u v : V} (hu : u ∈ B i) (hv : v ∈ B j) :
    G.Reachable u v := by
  let lift (a : I) : G.induce (B a) →g G := {
    toFun := Subtype.val
    map_rel' := by intro x y hxy; exact hxy
  }
  have hin (a : I) {x y : V} (hx : x ∈ B a) (hy : y ∈ B a) :
      G.Reachable x y :=
    ((hconn a).preconnected ⟨x, hx⟩ ⟨y, hy⟩).map (lift a)
  have go : ∀ {a b : I}, (supportQuotientGraph G B).Walk a b →
      ∀ {x y : V}, x ∈ B a → y ∈ B b → G.Reachable x y := by
    intro a b p
    induction p with
    | nil =>
        intro x y hx hy
        exact hin _ hx hy
    | @cons a b c hab p ih =>
        intro x z hx hz
        obtain ⟨x', hx', y', hy', hxy⟩ :=
          supportQuotientGraph_adj_crossing G B hab
        exact ((hin a hx hx').trans hxy.reachable).trans (ih hy' hz)
  obtain ⟨p⟩ := hij
  exact go p hu hv

/-- Contracting pairwise disjoint nonempty connected blocks cannot create a
cycle in a forest.  -/
theorem SupportQuotientGraph.isAcyclic_of_disjoint_connected
    {I : Type*} (B : I → Set V)
    (hforest : G.IsAcyclic)
    (hdisj : ∀ a b : I, a ≠ b → Disjoint (B a) (B b))
    (hconn : ∀ a, (G.induce (B a)).Connected) :
    (supportQuotientGraph G B).IsAcyclic := by
  classical
  let Q := supportQuotientGraph G B
  have huniq (a b : I) {x : V} (ha : x ∈ B a) (hb : x ∈ B b) : a = b := by
    by_contra hne
    exact (Set.disjoint_left.mp (hdisj a b hne)) ha hb
  apply SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mpr
  intro i j hij
  obtain ⟨u, hu, v, hv, huv⟩ := supportQuotientGraph_adj_crossing G B hij
  have hijne : i ≠ j := hij.ne
  let D := G.deleteEdges {s(u, v)}
  have hDconn (a : I) : (D.induce (B a)).Connected := by
    let f : G.induce (B a) →g D.induce (B a) := {
      toFun := id
      map_rel' := by
        intro x y hxy
        change D.Adj (x : V) (y : V)
        apply SimpleGraph.deleteEdges_adj.mpr
        refine ⟨hxy, ?_⟩
        simp only [Set.mem_singleton_iff]
        intro he
        rcases Sym2.eq_iff.mp he with h | h
        · have hai : a = i := huniq a i (by simpa only [← h.1] using x.property) hu
          have haj : a = j := huniq a j (by simpa only [← h.2] using y.property) hv
          exact hijne (hai.symm.trans haj)
        · have haj : a = j := huniq a j (by simpa only [← h.1] using x.property) hv
          have hai : a = i := huniq a i (by simpa only [← h.2] using y.property) hu
          exact hijne (hai.symm.trans haj)
    }
    exact (hconn a).map f (fun x => ⟨x, rfl⟩)
  have hQsub : Q.deleteEdges {s(i, j)} ≤ supportQuotientGraph D B := by
    intro a b hab
    obtain ⟨x, hx, y, hy, hxy⟩ :=
      supportQuotientGraph_adj_crossing G B
        (SimpleGraph.deleteEdges_adj.mp hab).1
    have hxyne : s(x, y) ≠ s(u, v) := by
      intro he
      rcases Sym2.eq_iff.mp he with h | h
      · have hai : a = i := huniq a i (h.1 ▸ hx) hu
        have hbj : b = j := huniq b j (h.2 ▸ hy) hv
        exact (SimpleGraph.deleteEdges_adj.mp hab).2
          (by simp only [Set.mem_singleton_iff]; simp [hai, hbj])
      · have haj : a = j := huniq a j (h.1 ▸ hx) hv
        have hbi : b = i := huniq b i (h.2 ▸ hy) hu
        exact (SimpleGraph.deleteEdges_adj.mp hab).2
          (by simp only [Set.mem_singleton_iff]; simp [haj, hbi, Sym2.eq_swap])
    apply (SimpleGraph.fromRel_adj _ a b).mpr
    exact ⟨hab.ne, Or.inl ⟨x, hx, y, hy,
      SimpleGraph.deleteEdges_adj.mpr ⟨hxy, by simpa only [Set.mem_singleton_iff]⟩⟩⟩
  have hbridge : G.IsBridge s(u, v) :=
    (SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp hforest) huv
  apply SimpleGraph.isBridge_iff.mpr
  intro hreach
  have hreachD : D.Reachable u v :=
    supportQuotientGraph_reachable_lift D B hDconn
      (hreach.mono hQsub) hu hv
  exact (SimpleGraph.isBridge_iff.mp hbridge) hreachD

end ReductiveGroups
