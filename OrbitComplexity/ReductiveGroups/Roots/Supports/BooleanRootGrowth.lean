import OrbitComplexity.ReductiveGroups.Roots.Parabolic.ParabolicSupportStability
import OrbitComplexity.ReductiveGroups.Roots.Inversions.PositiveRootConnectedSupport
import OrbitComplexity.ReductiveGroups.Roots.SupportGraphs.SupportDynkinAcyclic
import OrbitComplexity.ReductiveGroups.Roots.SupportGraphs.ConnectedBlocksForest

/-!
# Boolean Root Growth

A reflected positive root gains one omitted simple-root leaf. The
coefficient on that leaf retains the integral Cartan weight. -/

noncomputable section
namespace ReductiveGroups

attribute [local instance] Classical.decEq
open scoped BigOperators

variable {ι R M N : Type*} [CommRing R] [CharZero R] [IsDomain R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [Finite ι] [P.IsCrystallographic]

private theorem unique_omitted_support_neighbor
    (b : P.Base) (β : ι) (j : b.support)
    (hj : simpleRootCoeffInt b β j = 0)
    (hconn : ((supportDynkinGraph b).induce
      (simpleRootSupportInt b β)).Connected)
    {i k : b.support}
    (hi : i ∈ simpleRootSupportInt b β)
    (hk : k ∈ simpleRootSupportInt b β)
    (hij : P.pairingIn ℤ (i : ι) (j : ι) ≠ 0)
    (hkj : P.pairingIn ℤ (k : ι) (j : ι) ≠ 0) : i = k := by
  let G := supportDynkinGraph b
  let S := simpleRootSupportInt b β
  have hjS : j ∉ S := by simp [S, simpleRootSupportInt, hj]
  have hdisj : Disjoint ({j} : Set b.support) S := by
    apply Set.disjoint_left.mpr
    intro x hx hxS
    exact hjS (by simpa only [Set.mem_singleton_iff.mp hx] using hxS)
  have hsing : (G.induce ({j} : Set b.support)).Connected := by
    have : Nonempty (↑({j} : Set b.support)) := ⟨⟨j, by simp⟩⟩
    have : Subsingleton (↑({j} : Set b.support)) := by
      constructor
      intro x y
      apply Subtype.ext
      exact (Set.mem_singleton_iff.mp x.property).trans
        (Set.mem_singleton_iff.mp y.property).symm
    exact SimpleGraph.Connected.of_subsingleton
  have hji : G.Adj j i :=
    ((supportDynkinGraph_adj_iff b i j).mpr
      ⟨by intro h; subst i; exact hjS hi, hij⟩).symm
  have hjk : G.Adj j k :=
    ((supportDynkinGraph_adj_iff b k j).mpr
      ⟨by intro h; subst k; exact hjS hk, hkj⟩).symm
  have heq : s(j, i) = s(j, k) :=
    crossing_edge_unique_of_acyclic G (supportDynkinGraph_isAcyclic b)
      hdisj hsing hconn (by simp) (by simp) hi hk hji hjk
  rcases Sym2.eq_iff.mp heq with h | h
  · exact h.2
  · exact False.elim (hjS (h.1 ▸ hk))

variable [P.IsReduced]

/-- If a simple reflection moves a positive root whose coefficient at that
simple root is zero, the old connected support has exactly one neighboring
simple root. The new coefficient is its old coefficient times the
negative Cartan entry; no simply-laced restriction is imposed. -/
theorem booleanRootGrowth_reflection
    (b : P.Base) (β : ι) (hβ : b.IsPos β) (j : b.support)
    (hj : simpleRootCoeffInt b β j = 0)
    (hmove : P.reflectionPerm (j : ι) β ≠ β) :
    ∃ i : b.support,
      i ∈ simpleRootSupportInt b β ∧
      P.pairingIn ℤ (i : ι) (j : ι) ≠ 0 ∧
      (∀ k : b.support, k ∈ simpleRootSupportInt b β →
        P.pairingIn ℤ (k : ι) (j : ι) ≠ 0 → k = i) ∧
      b.IsPos (P.reflectionPerm (j : ι) β) ∧
      simpleRootSupportInt b (P.reflectionPerm (j : ι) β) =
        simpleRootSupportInt b β ∪ {j} ∧
      (∀ k : b.support, k ≠ j →
        simpleRootCoeffInt b (P.reflectionPerm (j : ι) β) k =
          simpleRootCoeffInt b β k) ∧
      simpleRootCoeffInt b (P.reflectionPerm (j : ι) β) j =
        -simpleRootCoeffInt b β i *
          P.pairingIn ℤ (i : ι) (j : ι) := by
  have hpair : P.pairingIn ℤ β (j : ι) ≠ 0 := by
    intro hz
    have hp : P.pairing β (j : ι) = 0 := by
      simpa only [← P.algebraMap_pairingIn ℤ, map_zero] using
        congrArg (algebraMap ℤ R) hz
    exact hmove (P.reflectionPerm_eq_of_pairing_eq_zero hp)
  have hsum :
      (∑ k : b.support, simpleRootCoeffInt b β k *
        P.pairingIn ℤ (k : ι) (j : ι)) ≠ 0 := by
    rw [← pairingIn_eq_sum_simpleRootCoeffInt b β j]
    exact hpair
  obtain ⟨i, _, hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
  have hi : i ∈ simpleRootSupportInt b β := by
    change simpleRootCoeffInt b β i ≠ 0
    exact fun hz => hterm (by simp [hz])
  have hij : P.pairingIn ℤ (i : ι) (j : ι) ≠ 0 :=
    fun hz => hterm (by simp [hz])
  have hconn := positiveRoot_simpleSupport_connected b β hβ
  have huniq (k : b.support) (hk : k ∈ simpleRootSupportInt b β)
      (hkj : P.pairingIn ℤ (k : ι) (j : ι) ≠ 0) : k = i :=
    unique_omitted_support_neighbor b β j hj hconn hk hi hkj hij
  have hpairEq : P.pairingIn ℤ β (j : ι) =
      simpleRootCoeffInt b β i * P.pairingIn ℤ (i : ι) (j : ι) := by
    rw [pairingIn_eq_sum_simpleRootCoeffInt b β j]
    apply Finset.sum_eq_single i
    · intro k _ hki
      by_cases hk : simpleRootCoeffInt b β k = 0
      · simp [hk]
      · by_cases hkj : P.pairingIn ℤ (k : ι) (j : ι) = 0
        · simp [hkj]
        · exact False.elim (hki (huniq k hk hkj))
    · intro hiNot
      exact False.elim (hiNot (Finset.mem_univ i))
  have hβj : β ≠ (j : ι) := by
    intro heq
    rw [heq, simpleRootCoeffInt_simple b j j] at hj
    simp at hj
  have hpos : b.IsPos (P.reflectionPerm (j : ι) β) :=
    hβ.reflectionPerm j.property hβj
  have hother (k : b.support) (hk : k ≠ j) :
      simpleRootCoeffInt b (P.reflectionPerm (j : ι) β) k =
        simpleRootCoeffInt b β k := by
    rw [simpleRootCoeffInt_reflection]
    rw [ite_eq_right (Ne.symm hk)]
    ring
  have hnew : simpleRootCoeffInt b (P.reflectionPerm (j : ι) β) j =
      -simpleRootCoeffInt b β i *
        P.pairingIn ℤ (i : ι) (j : ι) := by
    rw [simpleRootCoeffInt_reflection, ite_eq_left rfl, hj, hpairEq]
    ring
  have hnewNe : simpleRootCoeffInt b (P.reflectionPerm (j : ι) β) j ≠ 0 := by
    rw [hnew]
    exact mul_ne_zero (neg_ne_zero.mpr hi) hij
  have hsupp : simpleRootSupportInt b (P.reflectionPerm (j : ι) β) =
      simpleRootSupportInt b β ∪ {j} := by
    ext k
    by_cases hk : k = j
    · subst k
      simp [simpleRootSupportInt, hnewNe]
    · simp only [simpleRootSupportInt, Set.mem_ofPred_eq,
        Set.mem_union, Set.mem_singleton_iff, hk, or_false]
      rw [hother k hk]
  exact ⟨i, hi, hij, huniq, hpos, hsupp, hother, hnew⟩

/-- Under simply-laced off-diagonal integral Cartan values, the new leaf
also has coefficient one. The main reflection theorem above retains the
correct weighted value without this extra hypothesis. -/
theorem booleanRootGrowth_zero_one
    (b : P.Base) (β : ι) (hβ : b.IsPos β) (j : b.support)
    (hj : simpleRootCoeffInt b β j = 0)
    (hmove : P.reflectionPerm (j : ι) β ≠ β)
    (hcoeff : ∀ k : b.support,
      simpleRootCoeffInt b β k = 0 ∨ simpleRootCoeffInt b β k = 1)
    (hCartan : ∀ i k : b.support, i ≠ k →
      P.pairingIn ℤ (i : ι) (k : ι) = 0 ∨
        P.pairingIn ℤ (i : ι) (k : ι) = -1) :
    b.IsPos (P.reflectionPerm (j : ι) β) ∧
      simpleRootSupportInt b (P.reflectionPerm (j : ι) β) =
        simpleRootSupportInt b β ∪ {j} ∧
      simpleRootCoeffInt b (P.reflectionPerm (j : ι) β) j = 1 ∧
      ∀ k : b.support,
        simpleRootCoeffInt b (P.reflectionPerm (j : ι) β) k = 0 ∨
          simpleRootCoeffInt b (P.reflectionPerm (j : ι) β) k = 1 := by
  obtain ⟨i, hi, hij, _, hpos, hsupp, hother, hnew⟩ :=
    booleanRootGrowth_reflection b β hβ j hj hmove
  have hiNe : i ≠ j := by
    intro heq
    subst i
    exact hi hj
  have hci : simpleRootCoeffInt b β i = 1 :=
    (hcoeff i).resolve_left hi
  have hpij : P.pairingIn ℤ (i : ι) (j : ι) = -1 :=
    (hCartan i j hiNe).resolve_left hij
  have hnewOne :
      simpleRootCoeffInt b (P.reflectionPerm (j : ι) β) j = 1 := by
    rw [hnew, hci, hpij]
    norm_num
  refine ⟨hpos, hsupp, hnewOne, ?_⟩
  intro k
  by_cases hk : k = j
  · subst k
    exact Or.inr hnewOne
  · rw [hother k hk]
    exact hcoeff k

end ReductiveGroups
