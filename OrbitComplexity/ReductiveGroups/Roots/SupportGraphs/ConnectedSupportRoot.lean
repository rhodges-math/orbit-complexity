import OrbitComplexity.ReductiveGroups.Roots.SupportGraphs.ConnectedSupportExtension
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Finset.Powerset

/-!
# Connected support with coefficients all one

The graph below is the underlying simple Dynkin graph on the base
support: adjacency means a nonzero integral Cartan pairing. Multiple bond
decorations are forgotten, but not any vertices or edges.
-/

noncomputable section

namespace ReductiveGroups

open scoped BigOperators

attribute [local instance] Classical.decEq
set_option linter.unusedSectionVars false

variable {ι R M N : Type*} [CommRing R] [CharZero R] [IsDomain R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [Finite ι] [P.IsCrystallographic]

/-- The simple graph underlying the base's Dynkin diagram. -/
def supportDynkinGraph (b : P.Base) : SimpleGraph b.support :=
  SimpleGraph.fromRel (fun i j : b.support =>
    P.pairingIn ℤ (i : ι) (j : ι) ≠ 0)

omit [Finite ι] in
/-- Its edges are exactly the nonzero integral Cartan pairings; the reverse
direction in `fromRel` gives no additional edges. -/
theorem supportDynkinGraph_adj_iff (b : P.Base) (i j : b.support) :
    (supportDynkinGraph b).Adj i j ↔
      i ≠ j ∧ P.pairingIn ℤ (i : ι) (j : ι) ≠ 0 := by
  rw [supportDynkinGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨hij, h | h⟩
    · exact ⟨hij, h⟩
    · refine ⟨hij, ?_⟩
      intro hz
      have hR : P.pairing (i : ι) (j : ι) = 0 := by
        simpa only [← P.algebraMap_pairingIn ℤ, map_zero] using
          congrArg (algebraMap ℤ R) hz
      have hR' : P.pairing (j : ι) (i : ι) = 0 :=
        (P.pairing_eq_zero_iff').mp hR
      exact h (by
        apply (FaithfulSMul.algebraMap_injective ℤ R)
        simpa only [P.algebraMap_pairingIn, map_zero] using hR')
  · intro h
    exact ⟨h.1, Or.inl h.2⟩

omit [Finite ι] in
private theorem exists_pairing_boundary_of_connected (b : P.Base)
    (K S : Finset b.support) (hSK : S ⊆ K) (hS : S.Nonempty) (hproper : S ≠ K)
    (hconn : ((supportDynkinGraph b).induce (↑K : Set b.support)).Connected) :
    ∃ i ∈ K, i ∉ S ∧ ∃ j ∈ S, P.pairingIn ℤ (j : ι) (i : ι) ≠ 0 := by
  classical
  obtain ⟨u, huS⟩ := hS
  have huK : u ∈ K := hSK huS
  obtain ⟨v, hvK, hvS⟩ : ∃ v ∈ K, v ∉ S := by
    by_contra h
    push Not at h
    exact hproper (Finset.Subset.antisymm hSK (fun x hx => h x hx))
  let u' : (↑K : Set b.support) := ⟨u, huK⟩
  let v' : (↑K : Set b.support) := ⟨v, hvK⟩
  let T : Set (↑K : Set b.support) := {x | x.val ∈ S}
  obtain ⟨p⟩ := hconn u' v'
  obtain ⟨d, _, hdS, hdi⟩ := p.exists_boundary_dart T huS hvS
  let j : b.support := d.fst.val
  let i : b.support := d.snd.val
  have hjS : j ∈ S := hdS
  have hiS : i ∉ S := hdi
  have hiK : i ∈ K := d.snd.property
  have hadj : (supportDynkinGraph b).Adj j i := d.adj
  have hp : P.pairingIn ℤ (j : ι) (i : ι) ≠ 0 :=
    ((supportDynkinGraph_adj_iff b j i).mp hadj).2
  exact ⟨i, hiK, hiS, j, hjS, hp⟩

/-- A nonempty connected induced support with all simple coefficients one
is the sum of simple roots of one positive root. Connectedness is
that of the underlying Dynkin graph, not an assumed vertex order. -/
theorem connectedSupport_sum_isPositiveRoot (b : P.Base)
    (K : Finset b.support) (hK : K.Nonempty)
    (hconn : ((supportDynkinGraph b).induce (↑K : Set b.support)).Connected) :
    ∃ k : ι, b.IsPos k ∧ P.root k = ∑ j ∈ K, P.root (j : ι) := by
  classical
  let C : Finset (Finset b.support) :=
    K.powerset.filter (fun S => ∃ k : ι, P.root k = ∑ j ∈ S, P.root (j : ι))
  have hC : C.Nonempty := by
    obtain ⟨u, huK⟩ := hK
    refine ⟨{u}, ?_⟩
    simp only [C, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨Finset.singleton_subset_iff.mpr huK, u, by simp⟩
  obtain ⟨S, hSC, hmax⟩ := C.exists_max_image Finset.card hC
  have hSK : S ⊆ K := Finset.mem_powerset.mp (Finset.mem_filter.mp hSC).1
  obtain ⟨k, hk⟩ := (Finset.mem_filter.mp hSC).2
  by_cases hproper : S = K
  · subst S
    refine ⟨k, ?_, hk⟩
    have hspan : (∑ x ∈ K, P.rootSpanMem ℤ (x : ι)) = P.rootSpanMem ℤ k := by
      apply Subtype.ext
      simpa using hk.symm
    have hheight : (K.card : ℤ) = b.height k := by
      have h : (∑ x ∈ K, b.height (x : ι)) = b.height k := by
        simpa only [map_sum, rootLatticeHeight_root] using
          congrArg (rootLatticeHeight b) hspan
      calc
        (K.card : ℤ) = ∑ _x ∈ K, (1 : ℤ) := by simp
        _ = ∑ x ∈ K, b.height (x : ι) := by
          apply Finset.sum_congr rfl
          intro x _
          exact (b.height_one_of_mem_support x.property).symm
        _ = b.height k := h
    change 0 < b.height k
    rw [← hheight]
    exact_mod_cast Finset.card_pos.mpr hK
  · have hS : S.Nonempty := by
      by_contra h
      have hEmpty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
      have hz : P.root k = 0 := by simpa [hEmpty] using hk
      exact P.ne_zero k hz
    obtain ⟨i, hiK, hiS, j, hjS, hpair⟩ :=
      exists_pairing_boundary_of_connected b K S hSK hS hproper hconn
    obtain ⟨k', _, hk'⟩ :=
      positiveRoot_sum_insert_of_adjacent b S i hiS ⟨k, hk⟩ ⟨j, hjS, hpair⟩
    have hTmem : insert i S ∈ C := by
      simp only [C, Finset.mem_filter, Finset.mem_powerset]
      exact ⟨Finset.insert_subset hiK hSK, k', hk'⟩
    have hle := hmax (insert i S) hTmem
    simp [hiS] at hle

end ReductiveGroups
