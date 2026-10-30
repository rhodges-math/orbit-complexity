import OrbitComplexity.ReductiveGroups.Groups.Representatives.WeylRepresentativeAbstract
import OrbitComplexity.ReductiveGroups.Roots.Coxeter.BruhatSubword
import Mathlib.Topology.Algebra.Monoid.Defs
import OrbitComplexity.ReductiveGroups.Groups.Cells.RankOneBruhat

/-! # Bruhat systems and iterated sweeps -/

noncomputable section
namespace ReductiveGroups

open CoxeterSystem

section Bruhat

variable {ι R M₀ N₀ : Type*} [CommRing R] [CharZero R]
  [AddCommGroup M₀] [Module R M₀] [AddCommGroup N₀] [Module R N₀]
  {P : RootPairing ι R M₀ N₀} [Finite ι] [IsDomain R]
  [P.IsCrystallographic] [P.IsReduced]

omit [CharZero R] [Finite ι] [IsDomain R] [P.IsCrystallographic] [P.IsReduced] in
/-- The equality is

```lean
simpleWeylWord b (l ++ [s]) = simpleWeylWord b l * RootPairing.weylGroup.ofIdx P (s : ι)
```
-/
theorem simpleWeylWord_append_singleton (b : P.Base) (l : List b.support) (s : b.support) :
    simpleWeylWord b (l ++ [s]) = simpleWeylWord b l * RootPairing.weylGroup.ofIdx P (s : ι) := by
  rw [simpleWeylWord_append]
  change simpleWeylWord b l * (RootPairing.weylGroup.ofIdx P (s : ι) * 1) = _
  rw [mul_one]

/-- The last letter of a reduced word sends its simple root to a positive root
under the preceding prefix. -/
theorem isPos_of_reduced_append (b : P.Base) (l : List b.support) (s : b.support)
    (hred : rootInversionCount b (simpleWeylWord b (l ++ [s])) = (l ++ [s]).length) :
    b.IsPos (P.weylGroupToPerm (simpleWeylWord b l) (s : ι)) := by
  by_contra hneg
  have hcount := rootInversionCount_mul_simple_of_neg b (simpleWeylWord b l) s
    ((root_height_neg_iff_not_isPos b _).mpr hneg)
  have hle := RootInversionCount.simpleWeylWord_le_length b l
  rw [simpleWeylWord_append_singleton, List.length_append, List.length_singleton] at hred
  omega

variable {G 𝕜 : Type*} [Group G] [Field 𝕜]

/-- The data for Bruhat-cell combinatorics: a Weyl representative system, rank-one
data at every simple root, and positivity of conjugated root subgroups. -/
structure IsBruhatSystem (b : P.Base) (Bo T : Subgroup G)
    (f : ι → G) (Tr : G → Equiv.Perm ι → Prop) (x y : b.support → 𝕜 → G) : Prop where
  torus_le : T ≤ Bo
  weyl : IsWeylRepresentativeSystem P T f Tr
  rankOne : ∀ i : b.support, IsRankOneBruhatData Bo T (x i) (y i) (f i)
  conj_isPos : ∀ (w : P.weylGroup) (i : b.support), b.IsPos (P.weylGroupToPerm w i) →
    ∀ c : 𝕜, weylElementPoint f b w * x i c * (weylElementPoint f b w)⁻¹ ∈ Bo

/-- The sets `Z_l = P_{i₁} ⋯ P_{i_k}`, built by iterated sweeps starting at `Bo`. -/
def sweepChain (Bo : Subgroup G) (f : ι → G) {b : P.Base} (y : b.support → 𝕜 → G)
    (l : List b.support) : Set G :=
  l.foldl (fun Y i => sweepSet (y i) (f (i : ι)) Y) (Bo : Set G)

omit [CharZero R] [Finite ι] [IsDomain R] [P.IsCrystallographic] [P.IsReduced] [Field 𝕜] in
/-- The equality is

```lean
sweepChain Bo f y [] = (Bo : Set G)
```
-/
theorem sweepChain_nil (Bo : Subgroup G) (f : ι → G) {b : P.Base} (y : b.support → 𝕜 → G) :
    sweepChain Bo f y [] = (Bo : Set G) := rfl

omit [CharZero R] [Finite ι] [IsDomain R] [P.IsCrystallographic] [P.IsReduced] [Field 𝕜] in
/-- The equality is

```lean
sweepChain Bo f y (l ++ [s]) = sweepSet (y s) (f (s : ι)) (sweepChain Bo f y l)
```
-/
theorem sweepChain_append_singleton (Bo : Subgroup G) (f : ι → G) {b : P.Base}
    (y : b.support → 𝕜 → G) (l : List b.support) (s : b.support) :
    sweepChain Bo f y (l ++ [s]) = sweepSet (y s) (f (s : ι)) (sweepChain Bo f y l) := by
  simp only [sweepChain, List.foldl_append, List.foldl_cons, List.foldl_nil]

namespace IsBruhatSystem

variable {b : P.Base} {Bo T : Subgroup G} {f : ι → G} {Tr : G → Equiv.Perm ι → Prop}
  {x y : b.support → 𝕜 → G}

/-- `ẇ n_i ∈ T (w s_i)˙`. -/
theorem rep_mul_simple (h : IsBruhatSystem b Bo T f Tr x y) (w : P.weylGroup)
    (i : b.support) :
    ∃ t ∈ T, weylElementPoint f b w * f (i : ι) =
      t * weylElementPoint f b (w * RootPairing.weylGroup.ofIdx P (i : ι)) := by
  obtain ⟨t₁, ht₁, h₁⟩ := h.weyl.simple_eq_mul_weylElementPoint b i
  obtain ⟨t₂, ht₂, h₂⟩ := h.weyl.weylElementPoint_mul b w (RootPairing.weylGroup.ofIdx P (i : ι))
  have hN := h.weyl.weylElementPoint_mem_normalizer b w
  have ht := (Subgroup.mem_normalizer_iff.mp hN t₁).mp ht₁
  refine ⟨weylElementPoint f b w * t₁ * (weylElementPoint f b w)⁻¹ * t₂, mul_mem ht ht₂, ?_⟩
  rw [h₁]
  calc weylElementPoint f b w * (t₁ * weylElementPoint f b (RootPairing.weylGroup.ofIdx P (i : ι)))
      = weylElementPoint f b w * t₁ * (weylElementPoint f b w)⁻¹ *
          (weylElementPoint f b w *
            weylElementPoint f b (RootPairing.weylGroup.ofIdx P (i : ι))) := by group
    _ = _ := by rw [h₂]; group

/-- **Multiplication, positive case.** If `w(α_i) > 0` then
`Bo ẇ Bo · Bo n_i Bo ⊆ Bo (w s_i)˙ Bo`. -/
theorem doubleCoset_mul_of_isPos (h : IsBruhatSystem b Bo T f Tr x y) (w : P.weylGroup)
    (i : b.support) (hpos : b.IsPos (P.weylGroupToPerm w i)) {g g' : G}
    (hg : g ∈ subgroupDoubleCoset Bo (weylElementPoint f b w))
    (hg' : g' ∈ subgroupDoubleCoset Bo (f (i : ι))) :
    g * g' ∈ subgroupDoubleCoset Bo
      (weylElementPoint f b (w * RootPairing.weylGroup.ofIdx P (i : ι))) := by
  obtain ⟨h₁, hh₁, h₂, hh₂, rfl⟩ := hg
  obtain ⟨h₁', hh₁', h₂', hh₂', rfl⟩ := hg'
  obtain ⟨c, b', hb', he⟩ := (h.rankOne i).borel_mul (h₂ * h₁') (mul_mem hh₂ hh₁')
  obtain ⟨t, ht, hrep⟩ := h.rep_mul_simple w i
  have hconj := h.conj_isPos w i hpos c
  set W := weylElementPoint f b w with hW
  refine ⟨h₁ * (W * x i c * W⁻¹) * t, mul_mem (mul_mem hh₁ hconj) (h.torus_le ht),
    b' * h₂', mul_mem hb' hh₂', ?_⟩
  calc h₁ * W * h₂ * (h₁' * f (i : ι) * h₂') = h₁ * W * ((h₂ * h₁') * f (i : ι)) * h₂' := by
        group
    _ = h₁ * W * (x i c * f (i : ι) * b') * h₂' := by rw [he]
    _ = h₁ * (W * x i c * W⁻¹) * (W * f (i : ι)) * (b' * h₂') := by group
    _ = h₁ * (W * x i c * W⁻¹) *
          (t * weylElementPoint f b (w * RootPairing.weylGroup.ofIdx P (i : ι))) *
            (b' * h₂') := by rw [hrep]
    _ = _ := by group

/-- Every element of `Bo (w s_i)˙ Bo` is a product of elements of `Bo ẇ Bo` and
`Bo n_i Bo`. -/
theorem exists_mul_of_mem_doubleCoset (h : IsBruhatSystem b Bo T f Tr x y)
    (w : P.weylGroup) (i : b.support) {g : G}
    (hg : g ∈ subgroupDoubleCoset Bo
      (weylElementPoint f b (w * RootPairing.weylGroup.ofIdx P (i : ι)))) :
    ∃ g₁ ∈ subgroupDoubleCoset Bo (weylElementPoint f b w),
      ∃ g₂ ∈ subgroupDoubleCoset Bo (f (i : ι)), g = g₁ * g₂ := by
  obtain ⟨h₁, hh₁, h₂, hh₂, rfl⟩ := hg
  obtain ⟨t, ht, hrep⟩ := h.rep_mul_simple w i
  refine ⟨h₁ * t⁻¹ * weylElementPoint f b w,
    ⟨h₁ * t⁻¹, mul_mem hh₁ (inv_mem (h.torus_le ht)), 1, one_mem _, by group⟩,
    f (i : ι) * h₂, ⟨1, one_mem _, h₂, hh₂, by group⟩, ?_⟩
  have hrep' : weylElementPoint f b (w * RootPairing.weylGroup.ofIdx P (i : ι)) =
      t⁻¹ * (weylElementPoint f b w * f (i : ι)) := by
    rw [hrep]
    group
  rw [hrep']
  group

/-- **Multiplication rule.** `Bo ẇ Bo · Bo n_i Bo ⊆ Bo (w s_i)˙ Bo ∪ Bo ẇ Bo`. -/
theorem doubleCoset_mul (h : IsBruhatSystem b Bo T f Tr x y) (w : P.weylGroup)
    (i : b.support) {g g' : G}
    (hg : g ∈ subgroupDoubleCoset Bo (weylElementPoint f b w))
    (hg' : g' ∈ subgroupDoubleCoset Bo (f (i : ι))) :
    g * g' ∈ subgroupDoubleCoset Bo
        (weylElementPoint f b (w * RootPairing.weylGroup.ofIdx P (i : ι))) ∨
      g * g' ∈ subgroupDoubleCoset Bo (weylElementPoint f b w) := by
  by_cases hpos : b.IsPos (P.weylGroupToPerm w i)
  · exact Or.inl (h.doubleCoset_mul_of_isPos w i hpos hg hg')
  · have hw' : w * RootPairing.weylGroup.ofIdx P (i : ι) * RootPairing.weylGroup.ofIdx P (i : ι) =
        w := by
      rw [mul_assoc, weylGroup_ofIdx_mul_self, mul_one]
    have hpos' : b.IsPos (P.weylGroupToPerm (w * RootPairing.weylGroup.ofIdx P (i : ι)) i) := by
      rw [map_mul, Equiv.Perm.mul_apply, weylGroupToPerm_simple, weylGroupToPerm_neg_index,
        isPos_neg_index_iff]
      exact hpos
    have hg2 : g ∈ subgroupDoubleCoset Bo (weylElementPoint f b
        (w * RootPairing.weylGroup.ofIdx P (i : ι) * RootPairing.weylGroup.ofIdx P (i : ι))) := by
      rw [hw']
      exact hg
    obtain ⟨g₁, hg₁, g₂, hg₂, rfl⟩ := h.exists_mul_of_mem_doubleCoset _ i hg2
    rcases (h.rankOne i).doubleCoset_mul hg₂ hg' with hb | hd
    · left
      rw [mul_assoc]
      exact subgroupDoubleCoset_mul_mem hg₁ hb
    · right
      rw [mul_assoc]
      have := h.doubleCoset_mul_of_isPos _ i hpos' hg₁ hd
      rwa [hw'] at this

end IsBruhatSystem

end Bruhat

end ReductiveGroups
