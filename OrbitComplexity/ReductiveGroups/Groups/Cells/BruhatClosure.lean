import OrbitComplexity.ReductiveGroups.Groups.Representatives.WeylRepresentativeAbstract
import OrbitComplexity.ReductiveGroups.Roots.Coxeter.BruhatSubword
import Mathlib.Topology.Algebra.Monoid.Defs
import OrbitComplexity.ReductiveGroups.Groups.Cells.BruhatSystems

/-! # Topological closures of Bruhat sweeps -/

noncomputable section
namespace ReductiveGroups

open CoxeterSystem

section Bruhat

variable {ι R M₀ N₀ : Type*} [CommRing R] [CharZero R]
  [AddCommGroup M₀] [Module R M₀] [AddCommGroup N₀] [Module R N₀]
  {P : RootPairing ι R M₀ N₀} [Finite ι] [IsDomain R]
  [P.IsCrystallographic] [P.IsReduced]

variable {G 𝕜 : Type*} [Group G] [Field 𝕜]

namespace IsBruhatSystem

variable {b : P.Base} {Bo T : Subgroup G} {f : ι → G} {Tr : G → Equiv.Perm ι → Prop}
  {x y : b.support → 𝕜 → G}

section Topology

variable [TopologicalSpace G] [SeparatelyContinuousMul G]

/-- **Closure relation along reduced words.** If `1 ∈ closure (Bo n_i Bo)` for
every simple `i`, then for a reduced word `l` and a subword `k`,
`Bo (π k)˙ Bo ⊆ closure (Bo (π l)˙ Bo)`. -/
theorem doubleCoset_subset_closure_of_sublist (h : IsBruhatSystem b Bo T f Tr x y)
    (hcl : ∀ i : b.support, (1 : G) ∈ closure (subgroupDoubleCoset Bo (f (i : ι)))) :
    ∀ l : List b.support, rootInversionCount b (simpleWeylWord b l) = l.length →
      ∀ k : List b.support, k.Sublist l →
        subgroupDoubleCoset Bo (weylElementPoint f b (simpleWeylWord b k)) ⊆
          closure (subgroupDoubleCoset Bo (weylElementPoint f b (simpleWeylWord b l))) := by
  intro l
  induction l using List.reverseRecOn with
  | nil =>
    intro _ k hk
    rw [List.sublist_nil.mp hk]
    exact subset_closure
  | append_singleton l s ih =>
    intro hred k hk
    have hlred := RootInversionCount.prefix_of_reduced_append b l [s] hred
    have hpos := isPos_of_reduced_append b l s hred
    have hstep : subgroupDoubleCoset Bo (weylElementPoint f b (simpleWeylWord b l)) ⊆
        closure (subgroupDoubleCoset Bo (weylElementPoint f b (simpleWeylWord b (l ++ [s])))) := by
      intro g hg
      rw [simpleWeylWord_append_singleton]
      have hc : Continuous (fun z : G => g * z) := SeparatelyContinuousMul.continuous_const_mul
      have := map_mem_closure hc (hcl s)
        (fun z hz => h.doubleCoset_mul_of_isPos _ s hpos hg hz)
      simpa only [mul_one] using this
    obtain ⟨k₁, k₂, rfl, hk₁, hk₂⟩ := List.sublist_append_iff.mp hk
    rcases List.sublist_singleton.mp hk₂ with rfl | rfl
    · rw [List.append_nil]
      exact (ih hlred k₁ hk₁).trans (closure_minimal hstep isClosed_closure)
    · intro g hg
      rw [simpleWeylWord_append_singleton] at hg
      obtain ⟨g₁, hg₁, g₂, hg₂, rfl⟩ := h.exists_mul_of_mem_doubleCoset _ s hg
      rw [simpleWeylWord_append_singleton]
      have hc : Continuous (fun z : G => z * g₂) := SeparatelyContinuousMul.continuous_mul_const
      exact map_mem_closure (f := fun z : G => z * g₂) hc (ih hlred k₁ hk₁ hg₁)
        (fun z hz => h.doubleCoset_mul_of_isPos _ s hpos hz hg₂)

/-- **Bruhat order gives closure relations.** If `v ≤ w` in the Bruhat order then
`Bo v̇ Bo ⊆ closure (Bo ẇ Bo)`. -/
theorem doubleCoset_subset_closure_of_le (h : IsBruhatSystem b Bo T f Tr x y)
    (hcl : ∀ i : b.support, (1 : G) ∈ closure (subgroupDoubleCoset Bo (f (i : ι))))
    {v w : P.weylGroup} (hvw : WeylBruhatLE b v w) :
    subgroupDoubleCoset Bo (weylElementPoint f b v) ⊆
      closure (subgroupDoubleCoset Bo (weylElementPoint f b w)) := by
  have hred := (weylCoxeterSystem_isReduced_iff b _).mp (chosenReducedWord_isReduced b w)
  have hvw' : WeylBruhatLE b v (simpleWeylWord b (chosenReducedWord b w)) := by
    rw [simpleWeylWord_chosenReducedWord]
    exact hvw
  obtain ⟨k, hk, hkv, -⟩ := (weylBruhatLE_iff_subword b v _ hred).mp hvw'
  have := h.doubleCoset_subset_closure_of_sublist hcl _ hred k hk
  rwa [hkv, simpleWeylWord_chosenReducedWord] at this

end Topology

/-- The sweep chain is right-`Bo`-stable. -/
theorem sweepChain_stable (h : IsBruhatSystem b Bo T f Tr x y) (l : List b.support) :
    ∀ g ∈ sweepChain Bo f y l, ∀ c ∈ Bo, g * c ∈ sweepChain Bo f y l := by
  induction l using List.reverseRecOn with
  | nil => exact fun g hg c hc => mul_mem hg hc
  | append_singleton l s ih =>
    rw [sweepChain_append_singleton]
    exact (h.rankOne s).sweepSet_stable ih

/-- The sweep chain is closed when `Bo` is closed and rank-one sweeps of closed
sets are closed. -/
theorem sweepChain_isClosed [TopologicalSpace G] (h : IsBruhatSystem b Bo T f Tr x y)
    (hBo : IsClosed (Bo : Set G))
    (hsweep : ∀ (i : b.support) (Y : Set G), IsClosed Y →
      (∀ (g : G) (c : 𝕜), c ≠ 0 → (g * y i c ∈ Y ↔ g * x i c⁻¹ * f (i : ι) ∈ Y)) →
        IsClosed (sweepSet (y i) (f (i : ι)) Y))
    (l : List b.support) : IsClosed (sweepChain Bo f y l) := by
  induction l using List.reverseRecOn with
  | nil => exact hBo
  | append_singleton l s ih =>
    rw [sweepChain_append_singleton]
    exact hsweep s _ ih ((h.rankOne s).sweep_rel (h.sweepChain_stable l))

/-- `Bo n_l Bo ⊆ Z_l` for every word `l`. -/
theorem doubleCoset_subset_sweepChain (h : IsBruhatSystem b Bo T f Tr x y)
    (l : List b.support) :
    subgroupDoubleCoset Bo (simpleWordPoint f b l) ⊆ sweepChain Bo f y l := by
  induction l using List.reverseRecOn with
  | nil =>
    rintro g ⟨h₁, hh₁, h₂, hh₂, rfl⟩
    rw [simpleWordPoint_nil, mul_one]
    exact mul_mem hh₁ hh₂
  | append_singleton l s ih =>
    rintro g ⟨h₁, hh₁, h₂, hh₂, rfl⟩
    rw [sweepChain_append_singleton]
    refine ((h.rankOne s).mem_sweepSet_iff (h.sweepChain_stable l) _).mpr
      ⟨h₂⁻¹ * (f (s : ι))⁻¹, ?_, ?_⟩
    · exact IsRankOneBruhatData.mul_mem_parabolic (inv_mem hh₂)
        (Or.inr (h.rankOne s).inv_mem_doubleCoset)
    · apply ih
      refine ⟨h₁, hh₁, 1, one_mem _, ?_⟩
      rw [simpleWordPoint_append, simpleWordPoint_singleton]
      group

/-- `Z_l ⊆ ⋃_{k ⊆ l} Bo (π k)˙ Bo`. -/
theorem sweepChain_subset (h : IsBruhatSystem b Bo T f Tr x y) (l : List b.support) :
    sweepChain Bo f y l ⊆ ⋃ k : List b.support, ⋃ (_ : k.Sublist l),
      subgroupDoubleCoset Bo (weylElementPoint f b (simpleWeylWord b k)) := by
  induction l using List.reverseRecOn with
  | nil =>
    intro g hg
    refine Set.mem_iUnion₂.mpr ⟨[], List.Sublist.refl _, ?_⟩
    rw [show simpleWeylWord b [] = 1 from rfl, weylElementPoint_one]
    exact ⟨g, hg, 1, one_mem _, by group⟩
  | append_singleton l s ih =>
    intro g hg
    rw [sweepChain_append_singleton] at hg
    obtain ⟨p, hp, hgp⟩ := ((h.rankOne s).mem_sweepSet_iff (h.sweepChain_stable l) g).mp hg
    obtain ⟨k, hk, hmem⟩ := Set.mem_iUnion₂.mp (ih hgp)
    have hginv : g = g * p * p⁻¹ := by group
    rcases (h.rankOne s).parabolic_inv hp with hb | hd
    · refine Set.mem_iUnion₂.mpr ⟨k, hk.trans (List.sublist_append_left l [s]), ?_⟩
      rw [hginv]
      exact subgroupDoubleCoset_mul_mem hmem hb
    · rcases h.doubleCoset_mul _ s hmem hd with h1 | h2
      · refine Set.mem_iUnion₂.mpr ⟨k ++ [s], hk.append (List.Sublist.refl _), ?_⟩
        rw [hginv, simpleWeylWord_append_singleton]
        exact h1
      · refine Set.mem_iUnion₂.mpr ⟨k, hk.trans (List.sublist_append_left l [s]), ?_⟩
        rw [hginv]
        exact h2

section ClosedTopology

variable [TopologicalSpace G]

/-- **Closure of a Bruhat cell.** If `Bo` is closed and rank-one sweeps of closed
sets are closed, then `closure (Bo ẇ Bo) ⊆ ⋃_{v ≤ w} Bo v̇ Bo`. -/
theorem closure_doubleCoset_subset (h : IsBruhatSystem b Bo T f Tr x y)
    (hBo : IsClosed (Bo : Set G))
    (hsweep : ∀ (i : b.support) (Y : Set G), IsClosed Y →
      (∀ (g : G) (c : 𝕜), c ≠ 0 → (g * y i c ∈ Y ↔ g * x i c⁻¹ * f (i : ι) ∈ Y)) →
        IsClosed (sweepSet (y i) (f (i : ι)) Y))
    (w : P.weylGroup) :
    closure (subgroupDoubleCoset Bo (weylElementPoint f b w)) ⊆
      ⋃ v : P.weylGroup, ⋃ (_ : WeylBruhatLE b v w),
        subgroupDoubleCoset Bo (weylElementPoint f b v) := by
  have hred := (weylCoxeterSystem_isReduced_iff b _).mp (chosenReducedWord_isReduced b w)
  have hZ := closure_minimal (h.doubleCoset_subset_sweepChain (chosenReducedWord b w))
    (h.sweepChain_isClosed hBo hsweep (chosenReducedWord b w))
  intro g hg
  obtain ⟨k, hk, hmem⟩ := Set.mem_iUnion₂.mp (h.sweepChain_subset _ (hZ hg))
  have hle := weylBruhatLE_of_sublist b hred hk
  rw [simpleWeylWord_chosenReducedWord] at hle
  exact Set.mem_iUnion₂.mpr ⟨_, hle, hmem⟩

end ClosedTopology

end IsBruhatSystem

end Bruhat

end ReductiveGroups
