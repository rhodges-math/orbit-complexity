import OrbitComplexity.ReductiveGroups.Roots.Supports.MultiplicityFreeSupportPartition
import OrbitComplexity.ReductiveGroups.Roots.SupportGraphs.ConnectedSupportRoot
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

/-!
# Simple support of a positive root

The support is measured in the integral root-span basis. The
coefficient lemmas below are prerequisites for proving that this support
is connected in the underlying Dynkin graph.
-/

noncomputable section

namespace ReductiveGroups

open scoped BigOperators

attribute [local instance] Classical.decEq

variable {ι R M N : Type*} [CommRing R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N}

/-- The equality is

```lean
simpleRootCoeffInt b (i : ι) j = if i = j then 1 else 0
```
-/
theorem simpleRootCoeffInt_simple (b : P.Base) (i j : b.support) :
    simpleRootCoeffInt b (i : ι) j = if i = j then 1 else 0 := by
  have he : P.rootSpanMem ℤ (i : ι) = b.toWeightBasisInt i := by
    apply Subtype.ext
    simp
  simp [simpleRootCoeffInt, he, Finsupp.single_apply]

/-- The equality is

```lean
simpleRootCoeffInt b γ i =
      simpleRootCoeffInt b α i + simpleRootCoeffInt b β i
```
-/
theorem simpleRootCoeffInt_add (b : P.Base) {α β γ : ι}
    (h : P.root γ = P.root α + P.root β) (i : b.support) :
    simpleRootCoeffInt b γ i =
      simpleRootCoeffInt b α i + simpleRootCoeffInt b β i := by
  have hspan : P.rootSpanMem ℤ γ =
      P.rootSpanMem ℤ α + P.rootSpanMem ℤ β := by
    apply Subtype.ext
    exact h
  simp only [simpleRootCoeffInt, hspan, map_add, Finsupp.add_apply]

/-- The equality is

```lean
simpleRootCoeffInt b γ i =
      simpleRootCoeffInt b α i - simpleRootCoeffInt b β i
```
-/
theorem simpleRootCoeffInt_sub (b : P.Base) {α β γ : ι}
    (h : P.root γ = P.root α - P.root β) (i : b.support) :
    simpleRootCoeffInt b γ i =
      simpleRootCoeffInt b α i - simpleRootCoeffInt b β i := by
  have hspan : P.rootSpanMem ℤ γ =
      P.rootSpanMem ℤ α - P.rootSpanMem ℤ β := by
    apply Subtype.ext
    exact h
  simp only [simpleRootCoeffInt, hspan, map_sub, Finsupp.sub_apply]

/-- For these parameters,

```lean
(simpleRootSupportInt b β).Nonempty
```
-/
theorem simpleRootSupportInt_nonempty (b : P.Base) (β : ι) :
    (simpleRootSupportInt b β).Nonempty := by
  by_contra h
  have hzero : b.toWeightBasisInt.repr (P.rootSpanMem ℤ β) = 0 := by
    apply Finsupp.ext
    intro i
    by_contra hi
    exact h ⟨i, hi⟩
  have hz : P.rootSpanMem ℤ β = 0 := by
    apply b.toWeightBasisInt.repr.injective
    simpa using hzero
  exact P.ne_zero β (congrArg Subtype.val hz)

/-- There exist elements satisfying

```lean
∃ i : b.support, 0 < simpleRootCoeffInt b β i
```
-/
theorem simpleRootCoeffInt_exists_pos_of_isPos (b : P.Base) (β : ι)
    (hβ : b.IsPos β) :
    ∃ i : b.support, 0 < simpleRootCoeffInt b β i := by
  obtain ⟨i, hi⟩ := simpleRootSupportInt_nonempty b β
  refine ⟨i, ?_⟩
  have hn := simpleRootCoeffInt_nonneg_of_isPos b β hβ i
  exact lt_of_le_of_ne hn (Ne.symm hi)

/-- The equality is

```lean
simpleRootCoeffInt b (P.reflectionPerm β β) i =
      -simpleRootCoeffInt b β i
```
-/
theorem simpleRootCoeffInt_neg_index (b : P.Base) (β : ι) (i : b.support) :
    simpleRootCoeffInt b (P.reflectionPerm β β) i =
      -simpleRootCoeffInt b β i := by
  have hspan : P.rootSpanMem ℤ (P.reflectionPerm β β) =
      -P.rootSpanMem ℤ β := by
    apply Subtype.ext
    simp
  rw [simpleRootCoeffInt, hspan, map_neg]
  rfl

set_option linter.style.haveILetI false in
/-- Every root's simple coordinates have one weak sign. -/
theorem simpleRootCoeffInt_sign (b : P.Base) (β : ι) :
    (∀ i : b.support, 0 ≤ simpleRootCoeffInt b β i) ∨
      (∀ i : b.support, simpleRootCoeffInt b β i ≤ 0) := by
  letI := P.indexNeg
  rcases RootPairing.Base.IsPos.or_neg (b := b) β with hp | hn
  · exact Or.inl (simpleRootCoeffInt_nonneg_of_isPos b β hp)
  · refine Or.inr (fun i => ?_)
    have h := simpleRootCoeffInt_nonneg_of_isPos b (-β) hn i
    change 0 ≤ simpleRootCoeffInt b (P.reflectionPerm β β) i at h
    rw [simpleRootCoeffInt_neg_index b β i] at h
    omega

/-- A positive root minus an omitted simple root cannot be a root: its
simple coefficients would have both signs. -/
theorem positiveRoot_sub_omitted_simple_not_root (b : P.Base)
    (β : ι) (hβ : b.IsPos β) (j : b.support)
    (hj : simpleRootCoeffInt b β j = 0) :
    P.root β - P.root (j : ι) ∉ Set.range P.root := by
  rintro ⟨δ, hδ⟩
  obtain ⟨i, hi⟩ := simpleRootCoeffInt_exists_pos_of_isPos b β hβ
  have hij : i ≠ j := by
    intro he
    subst i
    omega
  have hδj := simpleRootCoeffInt_sub b hδ j
  have hδi := simpleRootCoeffInt_sub b hδ i
  rw [simpleRootCoeffInt_simple b j j, ite_eq_left rfl, hj] at hδj
  rw [simpleRootCoeffInt_simple b j i, ite_eq_right hij.symm] at hδi
  rcases simpleRootCoeffInt_sign b δ with hpos | hneg
  · have := hpos j; omega
  · have := hneg i; omega

/-- Pairing against a simple coroot is the corresponding integral linear
combination of the simple-root coefficients. -/
theorem pairingIn_eq_sum_simpleRootCoeffInt (b : P.Base) (β : ι)
    [P.IsCrystallographic] (j : b.support) :
    P.pairingIn ℤ β (j : ι) =
      ∑ i : b.support, simpleRootCoeffInt b β i *
        P.pairingIn ℤ (i : ι) (j : ι) := by
  have h := (b.toWeightBasisInt.sum_repr (P.rootSpanMem ℤ β)).symm
  have hpair := congrArg (P.coroot'In ℤ (j : ι)) h
  simp only [map_sum, map_zsmul, smul_eq_mul] at hpair
  have hb (i : b.support) :
      P.coroot'In ℤ (j : ι) (b.toWeightBasisInt i) =
        P.pairingIn ℤ (i : ι) (j : ι) := by
    have hi : b.toWeightBasisInt i = P.rootSpanMem ℤ (i : ι) := by
      apply Subtype.ext
      simp
    rw [hi, RootPairing.coroot'In_rootSpanMem_eq_pairingIn]
  simpa only [RootPairing.coroot'In_rootSpanMem_eq_pairingIn,
    simpleRootCoeffInt, hb] using hpair

/-- There exist elements satisfying

```lean
∃ i : b.support, simpleRootCoeffInt b β i ≠ 0 ∧
      P.pairingIn ℤ (i : ι) (j : ι) ≠ 0
```
-/
theorem PositiveRoot.add_omitted_simple_has_support_neighbor
    [P.IsCrystallographic] (b : P.Base) (β γ : ι)
    (hβ : b.IsPos β) (j : b.support)
    (hj : simpleRootCoeffInt b β j = 0)
    (hadd : P.root γ = P.root β + P.root (j : ι)) :
    ∃ i : b.support, simpleRootCoeffInt b β i ≠ 0 ∧
      P.pairingIn ℤ (i : ι) (j : ι) ≠ 0 := by
  have hpair : P.pairingIn ℤ β (j : ι) ≠ 0 := by
    intro hz
    have hspan : P.rootSpanMem ℤ γ =
        P.rootSpanMem ℤ β + P.rootSpanMem ℤ (j : ι) := by
      apply Subtype.ext
      exact hadd
    have hp := congrArg (P.coroot'In ℤ (j : ι)) hspan
    simp only [map_add, RootPairing.coroot'In_rootSpanMem_eq_pairingIn,
      RootPairing.pairingIn_same] at hp
    have hpg : P.pairingIn ℤ γ (j : ι) = 2 := by omega
    have hr : P.root (P.reflectionPerm (j : ι) γ) =
        P.root β - P.root (j : ι) := by
      rw [P.root_reflectionPerm, P.reflection_apply_root' ℤ, hpg, hadd]
      module
    exact positiveRoot_sub_omitted_simple_not_root b β hβ j hj ⟨_, hr⟩
  rw [pairingIn_eq_sum_simpleRootCoeffInt b β j] at hpair
  by_contra h
  push Not at h
  apply hpair
  apply Finset.sum_eq_zero
  intro i _
  by_cases hi : simpleRootCoeffInt b β i = 0
  · simp [hi]
  · simp [h i hi]

/-- The equality is

```lean
simpleRootSupportInt b γ = simpleRootSupportInt b β ∪ {j}
```
-/
theorem simpleRootSupportInt_add_simple (b : P.Base) {β γ : ι}
    (hβ : b.IsPos β) (j : b.support)
    (hadd : P.root γ = P.root β + P.root (j : ι)) :
    simpleRootSupportInt b γ = simpleRootSupportInt b β ∪ {j} := by
  ext i
  have hcoeff := simpleRootCoeffInt_add b hadd i
  rw [simpleRootCoeffInt_simple b j i] at hcoeff
  by_cases hij : j = i
  · subst i
    simp only [simpleRootSupportInt, Set.mem_ofPred_eq, Set.mem_union,
      Set.mem_singleton_iff, or_true, iff_true]
    rw [hcoeff, ite_eq_left rfl]
    have hn := simpleRootCoeffInt_nonneg_of_isPos b β hβ j
    omega
  · simp only [simpleRootSupportInt, Set.mem_ofPred_eq, Set.mem_union,
      Set.mem_singleton_iff]
    rw [hcoeff, ite_eq_right hij]
    have hji : i ≠ j := fun h => hij h.symm
    simp [hji]

set_option linter.style.haveILetI false in
omit [CharZero R] in
private theorem supportDynkinGraph_singleton_connected
    [P.IsCrystallographic]
    (b : P.Base) (j : b.support) :
    ((supportDynkinGraph b).induce ({j} : Set b.support)).Connected := by
  haveI : Nonempty (↑({j} : Set b.support)) := ⟨⟨j, by simp⟩⟩
  haveI : Subsingleton (↑({j} : Set b.support)) := by
    constructor
    intro x y
    apply Subtype.ext
    exact (Set.mem_singleton_iff.mp x.property).trans
      (Set.mem_singleton_iff.mp y.property).symm
  exact SimpleGraph.Connected.of_subsingleton

/-- The positive root has connected support in the underlying
simple Dynkin graph. The proof uses the root-system simple-addition
induction and the mixed-sign obstruction; it does not assert that
orthogonal roots can never sum to a root. -/
theorem positiveRoot_simpleSupport_connected
    [IsDomain R] [Finite ι] [P.IsCrystallographic]
    (b : P.Base) (β : ι) (hβ : b.IsPos β) :
    ((supportDynkinGraph b).induce (simpleRootSupportInt b β)).Connected := by
  let G := supportDynkinGraph b
  have hstrong (γ : ι) (hγ : b.IsPos γ) :
      ((G.induce (simpleRootSupportInt b γ)).Connected) := by
    let p : ι → Prop := fun γ => b.IsPos γ ∧
      ((G.induce (simpleRootSupportInt b γ)).Connected)
    have hp : p γ := by
      apply RootPairing.Base.IsPos.induction_on_add hγ
      · intro i hi
        refine ⟨b.isPos_of_mem_support hi, ?_⟩
        have hs : simpleRootSupportInt b i = ({⟨i, hi⟩} : Set b.support) := by
          ext j
          simp [simpleRootSupportInt, simpleRootCoeffInt_simple b ⟨i, hi⟩ j, eq_comm]
        rw [hs]
        exact supportDynkinGraph_singleton_connected b ⟨i, hi⟩
      · intro i j k hk hi hj
        let js : b.support := ⟨j, hj⟩
        have hkpos : b.IsPos k := hi.1.add (b.isPos_of_mem_support hj) hk
        refine ⟨hkpos, ?_⟩
        have hs := simpleRootSupportInt_add_simple b hi.1 js hk
        by_cases hz : simpleRootCoeffInt b i js = 0
        · obtain ⟨v, hv, hpair⟩ :=
            PositiveRoot.add_omitted_simple_has_support_neighbor b i k hi.1 js hz hk
          have hvne : v ≠ js := by
            intro he
            subst v
            exact hv hz
          have hadj : G.Adj v js :=
            (supportDynkinGraph_adj_iff b v js).mpr ⟨hvne, hpair⟩
          rw [hs]
          exact G.connected_induce_union hi.2.preconnected
            (supportDynkinGraph_singleton_connected b js).preconnected
            hv (by simp) hadj
        · have hjs : js ∈ simpleRootSupportInt b i := hz
          have heq : simpleRootSupportInt b k = simpleRootSupportInt b i := by
            rw [hs]
            exact Set.union_eq_self_of_subset_right
              (Set.singleton_subset_iff.mpr hjs)
          rw [heq]
          exact hi.2
    exact hp.2
  exact hstrong β hβ

end ReductiveGroups
