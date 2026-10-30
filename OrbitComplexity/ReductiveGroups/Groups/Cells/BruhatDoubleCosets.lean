import OrbitComplexity.ReductiveGroups.Groups.Representatives.WeylRepresentativeAbstract
import OrbitComplexity.ReductiveGroups.Roots.Coxeter.BruhatSubword
import Mathlib.Topology.Algebra.Monoid.Defs
import OrbitComplexity.ReductiveGroups.Groups.Cells.BruhatClosure

/-! # Bruhat double cosets, factorization and disjointness -/

noncomputable section
namespace ReductiveGroups

open CoxeterSystem

section SetForms

open Pointwise

variable {ι R M₀ N₀ : Type*} [CommRing R] [CharZero R]
  [AddCommGroup M₀] [Module R M₀] [AddCommGroup N₀] [Module R N₀]
  {P : RootPairing ι R M₀ N₀} [Finite ι] [IsDomain R]
  [P.IsCrystallographic] [P.IsReduced]

/-- A length-increasing simple reflection sends its simple root to a positive
root under `w`. -/
theorem isPos_of_length_mul_simple (b : P.Base) (w : P.weylGroup) (i : b.support)
    (hlen : (weylCoxeterSystem b).length (w * RootPairing.weylGroup.ofIdx P (i : ι)) =
      (weylCoxeterSystem b).length w + 1) :
    b.IsPos (P.weylGroupToPerm w i) := by
  by_contra hneg
  have hcount := rootInversionCount_mul_simple_of_neg b w i
    ((root_height_neg_iff_not_isPos b _).mpr hneg)
  rw [weylCoxeterSystem_length, weylCoxeterSystem_length] at hlen
  omega

variable {G 𝕜 : Type*} [Group G] [Field 𝕜]

/-- The equality is

```lean
subgroupDoubleCoset H a = subgroupDoubleCoset H c
```
-/
theorem subgroupDoubleCoset_eq_of_mul {H : Subgroup G} {a c t : G} (ht : t ∈ H)
    (h : a = t * c) : subgroupDoubleCoset H a = subgroupDoubleCoset H c := by
  ext g
  constructor
  · rintro ⟨h₁, hh₁, h₂, hh₂, rfl⟩
    exact ⟨h₁ * t, mul_mem hh₁ ht, h₂, hh₂, by rw [h]; group⟩
  · rintro ⟨h₁, hh₁, h₂, hh₂, rfl⟩
    exact ⟨h₁ * t⁻¹, mul_mem hh₁ (inv_mem ht), h₂, hh₂, by rw [h]; group⟩

/-- The equality is

```lean
subgroupDoubleCoset H n * (H : Set G) = subgroupDoubleCoset H n
```
-/
theorem subgroupDoubleCoset_mul_subgroup (H : Subgroup G) (n : G) :
    subgroupDoubleCoset H n * (H : Set G) = subgroupDoubleCoset H n := by
  ext g
  constructor
  · rintro ⟨a, ha, c, hc, rfl⟩
    exact subgroupDoubleCoset_mul_mem ha hc
  · intro hg
    exact ⟨g, hg, 1, one_mem H, mul_one g⟩

namespace IsBruhatSystem

variable {b : P.Base} {Bo T : Subgroup G} {f : ι → G} {Tr : G → Equiv.Perm ι → Prop}
  {x y : b.support → 𝕜 → G}

/-- `Bo n_i Bo = Bo ṡ_i Bo`. -/
theorem doubleCoset_simple_eq (h : IsBruhatSystem b Bo T f Tr x y) (i : b.support) :
    subgroupDoubleCoset Bo (f (i : ι)) =
      subgroupDoubleCoset Bo (weylElementPoint f b (RootPairing.weylGroup.ofIdx P (i : ι))) := by
  obtain ⟨t, ht, he⟩ := h.weyl.simple_eq_mul_weylElementPoint b i
  exact subgroupDoubleCoset_eq_of_mul (h.torus_le ht) he

/-- **Multiplication rule (set form).**
`Bo ẇ Bo · Bo ṡ_i Bo ⊆ Bo (w s_i)˙ Bo ∪ Bo ẇ Bo`. -/
theorem doubleCoset_mul_subset (h : IsBruhatSystem b Bo T f Tr x y) (w : P.weylGroup)
    (i : b.support) :
    subgroupDoubleCoset Bo (weylElementPoint f b w) *
        subgroupDoubleCoset Bo (weylElementPoint f b (RootPairing.weylGroup.ofIdx P (i : ι))) ⊆
      subgroupDoubleCoset Bo
          (weylElementPoint f b (w * RootPairing.weylGroup.ofIdx P (i : ι))) ∪
        subgroupDoubleCoset Bo (weylElementPoint f b w) := by
  rw [← h.doubleCoset_simple_eq i]
  rintro _ ⟨g, hg, g', hg', rfl⟩
  exact h.doubleCoset_mul w i hg hg'

/-- **Multiplication rule, length-additive case (set form).** If `w(α_i) > 0`
then `Bo ẇ Bo · Bo ṡ_i Bo = Bo (w s_i)˙ Bo`. -/
theorem doubleCoset_mul_eq_of_isPos (h : IsBruhatSystem b Bo T f Tr x y) (w : P.weylGroup)
    (i : b.support) (hpos : b.IsPos (P.weylGroupToPerm w i)) :
    subgroupDoubleCoset Bo (weylElementPoint f b w) *
        subgroupDoubleCoset Bo (weylElementPoint f b (RootPairing.weylGroup.ofIdx P (i : ι))) =
      subgroupDoubleCoset Bo
        (weylElementPoint f b (w * RootPairing.weylGroup.ofIdx P (i : ι))) := by
  rw [← h.doubleCoset_simple_eq i]
  ext g
  constructor
  · rintro ⟨g₁, hg₁, g₂, hg₂, rfl⟩
    exact h.doubleCoset_mul_of_isPos w i hpos hg₁ hg₂
  · intro hg
    obtain ⟨g₁, hg₁, g₂, hg₂, rfl⟩ := h.exists_mul_of_mem_doubleCoset w i hg
    exact ⟨g₁, hg₁, g₂, hg₂, rfl⟩

end IsBruhatSystem

end SetForms

section Disjoint

variable {ι R M₀ N₀ : Type*} [CommRing R] [CharZero R]
  [AddCommGroup M₀] [Module R M₀] [AddCommGroup N₀] [Module R N₀]
  {P : RootPairing ι R M₀ N₀} [Finite ι] [IsDomain R]
  [P.IsCrystallographic] [P.IsReduced]

variable {G 𝕜 : Type*} [Group G] [Field 𝕜]

omit [Field 𝕜] in
/-- Double cosets of a subgroup that meet coincide as memberships. -/
theorem mem_subgroupDoubleCoset_symm {H : Subgroup G} {a c : G}
    (h : a ∈ subgroupDoubleCoset H c) : c ∈ subgroupDoubleCoset H a := by
  obtain ⟨h₁, hh₁, h₂, hh₂, rfl⟩ := h
  exact ⟨h₁⁻¹, inv_mem hh₁, h₂⁻¹, inv_mem hh₂, by group⟩

omit [Field 𝕜] in
/-- For these parameters,

```lean
a ∈ subgroupDoubleCoset H c
```
-/
theorem mem_subgroupDoubleCoset_of_inter {H : Subgroup G} {a c g : G}
    (ha : g ∈ subgroupDoubleCoset H a) (hc : g ∈ subgroupDoubleCoset H c) :
    a ∈ subgroupDoubleCoset H c := by
  obtain ⟨h₁, hh₁, h₂, hh₂, rfl⟩ := ha
  obtain ⟨h₁', hh₁', h₂', hh₂', he⟩ := hc
  refine ⟨h₁⁻¹ * h₁', mul_mem (inv_mem hh₁) hh₁', h₂' * h₂⁻¹, mul_mem hh₂' (inv_mem hh₂), ?_⟩
  calc a = h₁⁻¹ * (h₁ * a * h₂) * h₂⁻¹ := by group
    _ = h₁⁻¹ * (h₁' * c * h₂') * h₂⁻¹ := by rw [he]
    _ = _ := by group

namespace IsBruhatSystem

variable {b : P.Base} {Bo T : Subgroup G} {f : ι → G} {Tr : G → Equiv.Perm ι → Prop}
  {x y : b.support → 𝕜 → G}

/-- **Distinct Bruhat cells are disjoint (length induction).** If the only
Weyl element with representative in `Bo` is `1`, then `v̇ ∈ Bo ẇ Bo` forces
`v = w`. -/
theorem eq_of_rep_mem_doubleCoset (h : IsBruhatSystem b Bo T f Tr x y)
    (hone : ∀ w : P.weylGroup, weylElementPoint f b w ∈ Bo → w = 1) :
    ∀ v w : P.weylGroup,
      weylElementPoint f b v ∈ subgroupDoubleCoset Bo (weylElementPoint f b w) → v = w := by
  let cs := weylCoxeterSystem b
  have key : ∀ n : ℕ, ∀ v w : P.weylGroup, cs.length v = n → cs.length v ≤ cs.length w →
      weylElementPoint f b v ∈ subgroupDoubleCoset Bo (weylElementPoint f b w) → v = w := by
    intro n
    induction n with
    | zero =>
      intro v w hv _ hmem
      have hv1 : v = 1 := cs.length_eq_zero_iff.mp hv
      subst hv1
      rw [weylElementPoint_one] at hmem
      obtain ⟨h₁, hh₁, h₂, hh₂, he⟩ := hmem
      have hwB : weylElementPoint f b w ∈ Bo := by
        have : weylElementPoint f b w = h₁⁻¹ * h₂⁻¹ := by
          calc weylElementPoint f b w = h₁⁻¹ * (h₁ * weylElementPoint f b w * h₂) * h₂⁻¹ := by
                group
            _ = h₁⁻¹ * h₂⁻¹ := by rw [← he]; group
        rw [this]
        exact mul_mem (inv_mem hh₁) (inv_mem hh₂)
      exact (hone w hwB).symm
    | succ n ih =>
      intro v w hv hvw hmem
      have hv1 : v ≠ 1 := by
        rintro rfl
        rw [CoxeterSystem.length_one] at hv
        omega
      obtain ⟨i, hi⟩ := cs.exists_rightDescent_of_ne_one hv1
      have hsimple : cs.simple i = RootPairing.weylGroup.ofIdx P (i : ι) :=
        weylCoxeterSystem_simple b i
      have hi' : cs.length (v * RootPairing.weylGroup.ofIdx P (i : ι)) < cs.length v := by
        have h0 : cs.length (v * cs.simple i) < cs.length v := hi
        rwa [hsimple] at h0
      have hv'len : cs.length (v * RootPairing.weylGroup.ofIdx P (i : ι)) + 1 = cs.length v := by
        rcases cs.length_mul_simple v i with h1 | h1 <;> rw [hsimple] at h1 <;> omega
      have hvv : v * RootPairing.weylGroup.ofIdx P (i : ι) * RootPairing.weylGroup.ofIdx P (i : ι) =
          v := by
        rw [mul_assoc, weylGroup_ofIdx_mul_self, mul_one]
      obtain ⟨t, ht, hrep⟩ := h.rep_mul_simple v i
      have hv'mem : weylElementPoint f b (v * RootPairing.weylGroup.ofIdx P (i : ι)) =
          t⁻¹ * weylElementPoint f b v * f (i : ι) := by
        rw [mul_assoc, hrep]
        group
      have hprod := h.doubleCoset_mul w i
        (mul_mem_subgroupDoubleCoset hmem (inv_mem (h.torus_le ht)))
        (mem_subgroupDoubleCoset_self Bo (f (i : ι)))
      rw [← hv'mem] at hprod
      have hwlen := cs.length_mul_simple w i
      rw [hsimple] at hwlen
      rcases hprod with hws | hw
      · have hle : cs.length (v * RootPairing.weylGroup.ofIdx P (i : ι)) ≤
            cs.length (w * RootPairing.weylGroup.ofIdx P (i : ι)) := by
          omega
        have heq := ih _ _ (by omega) hle hws
        rw [← hvv, heq, mul_assoc, weylGroup_ofIdx_mul_self, mul_one]
      · have hle : cs.length (v * RootPairing.weylGroup.ofIdx P (i : ι)) ≤ cs.length w := by
          omega
        have heq := ih _ w (by omega) hle hw
        rw [← heq] at hvw
        omega
  intro v w hmem
  rcases le_total (cs.length v) (cs.length w) with hle | hle
  · exact key _ v w rfl hle hmem
  · exact (key _ w v rfl hle (mem_subgroupDoubleCoset_symm hmem)).symm

/-- **Disjointness of distinct Bruhat cells.** Under the same hypothesis,
`Bo v̇ Bo` and `Bo ẇ Bo` meet only if `v = w`. -/
theorem eq_of_doubleCoset_inter (h : IsBruhatSystem b Bo T f Tr x y)
    (hone : ∀ w : P.weylGroup, weylElementPoint f b w ∈ Bo → w = 1)
    {v w : P.weylGroup} {g : G}
    (hv : g ∈ subgroupDoubleCoset Bo (weylElementPoint f b v))
    (hw : g ∈ subgroupDoubleCoset Bo (weylElementPoint f b w)) : v = w :=
  h.eq_of_rep_mem_doubleCoset hone v w (mem_subgroupDoubleCoset_of_inter hv hw)

end IsBruhatSystem

end Disjoint

end ReductiveGroups
