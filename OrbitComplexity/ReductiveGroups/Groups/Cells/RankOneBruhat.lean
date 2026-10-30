import OrbitComplexity.ReductiveGroups.Groups.Representatives.WeylRepresentativeAbstract
import OrbitComplexity.ReductiveGroups.Roots.Coxeter.BruhatSubword
import Mathlib.Topology.Algebra.Monoid.Defs

/-! # Rank-one Bruhat decompositions and sweeps -/

noncomputable section
namespace ReductiveGroups

open CoxeterSystem

section RankOne

variable {G 𝕜 : Type*} [Group G] [Field 𝕜]

/-- The double coset `H n H` in a group. -/
def subgroupDoubleCoset (H : Subgroup G) (n : G) : Set G :=
  {g | ∃ h₁ ∈ H, ∃ h₂ ∈ H, g = h₁ * n * h₂}

/-- For these parameters,

```lean
n ∈ subgroupDoubleCoset H n
```
-/
theorem mem_subgroupDoubleCoset_self (H : Subgroup G) (n : G) :
    n ∈ subgroupDoubleCoset H n :=
  ⟨1, one_mem H, 1, one_mem H, by group⟩

/-- For these parameters,

```lean
g * h ∈ subgroupDoubleCoset H n
```
-/
theorem subgroupDoubleCoset_mul_mem {H : Subgroup G} {n g h : G}
    (hg : g ∈ subgroupDoubleCoset H n) (hh : h ∈ H) : g * h ∈ subgroupDoubleCoset H n := by
  obtain ⟨h₁, hh₁, h₂, hh₂, rfl⟩ := hg
  exact ⟨h₁, hh₁, h₂ * h, mul_mem hh₂ hh, by group⟩

/-- For these parameters,

```lean
h * g ∈ subgroupDoubleCoset H n
```
-/
theorem mul_mem_subgroupDoubleCoset {H : Subgroup G} {n g h : G}
    (hg : g ∈ subgroupDoubleCoset H n) (hh : h ∈ H) : h * g ∈ subgroupDoubleCoset H n := by
  obtain ⟨h₁, hh₁, h₂, hh₂, rfl⟩ := hg
  exact ⟨h * h₁, mul_mem hh hh₁, h₂, hh₂, by group⟩

/-- The rank-one parabolic `Bo ∪ Bo n Bo`. -/
def rankOneParabolic (Bo : Subgroup G) (n : G) : Set G :=
  {g | g ∈ Bo ∨ g ∈ subgroupDoubleCoset Bo n}

/-- Rank-one relations for a simple root: `x` and `y` are the root subgroups
of `α` and `-α`, `n` the reflection point. -/
structure IsRankOneBruhatData (Bo T : Subgroup G) (x y : 𝕜 → G) (n : G) : Prop where
  torus_le : T ≤ Bo
  x_mem : ∀ c, x c ∈ Bo
  x_zero : x 0 = 1
  y_zero : y 0 = 1
  partner : ∀ d : 𝕜, d ≠ 0 → ∃ t ∈ T, y d = x d⁻¹ * t * n * x d⁻¹
  mem_normalizer : n ∈ Subgroup.normalizer (T : Set G)
  inv_eq : ∃ t ∈ T, n⁻¹ = t * n
  borel_mul : ∀ b ∈ Bo, ∃ c : 𝕜, ∃ b' ∈ Bo, b * n = x c * n * b'
  conj_x : ∀ c : 𝕜, ∃ c' : 𝕜, n * x c * n⁻¹ = y c'

namespace IsRankOneBruhatData

variable {Bo T : Subgroup G} {x y : 𝕜 → G} {n : G}

/-- For these parameters,

```lean
n⁻¹ * t * n ∈ T
```
-/
theorem conj_inv_mem (h : IsRankOneBruhatData Bo T x y n) {t : G} (ht : t ∈ T) :
    n⁻¹ * t * n ∈ T := by
  have hN := inv_mem h.mem_normalizer
  have := (Subgroup.mem_normalizer_iff.mp hN t).mp ht
  simpa only [inv_inv] using this

/-- For these parameters,

```lean
n * n ∈ T
```
-/
theorem sq_mem (h : IsRankOneBruhatData Bo T x y n) : n * n ∈ T := by
  obtain ⟨t, ht, he⟩ := h.inv_eq
  have ht' : t = n⁻¹ * n⁻¹ := eq_mul_inv_of_mul_eq he.symm
  have : n * n = t⁻¹ := by
    rw [ht', mul_inv_rev, inv_inv]
  rw [this]
  exact inv_mem ht

/-- For these parameters,

```lean
n⁻¹ ∈ subgroupDoubleCoset Bo n
```
-/
theorem inv_mem_doubleCoset (h : IsRankOneBruhatData Bo T x y n) :
    n⁻¹ ∈ subgroupDoubleCoset Bo n := by
  obtain ⟨t, ht, he⟩ := h.inv_eq
  exact ⟨t, h.torus_le ht, 1, one_mem _, by rw [he, mul_one]⟩

/-- For these parameters,

```lean
g⁻¹ ∈ subgroupDoubleCoset Bo n
```
-/
theorem doubleCoset_inv (h : IsRankOneBruhatData Bo T x y n) {g : G}
    (hg : g ∈ subgroupDoubleCoset Bo n) : g⁻¹ ∈ subgroupDoubleCoset Bo n := by
  obtain ⟨h₁, hh₁, h₂, hh₂, rfl⟩ := hg
  obtain ⟨t, ht, he⟩ := h.inv_eq
  refine ⟨h₂⁻¹ * t, mul_mem (inv_mem hh₂) (h.torus_le ht), h₁⁻¹, inv_mem hh₁, ?_⟩
  calc (h₁ * n * h₂)⁻¹ = h₂⁻¹ * n⁻¹ * h₁⁻¹ := by group
    _ = h₂⁻¹ * t * n * h₁⁻¹ := by rw [he]; group

/-- For `c ≠ 0`: `x(c) n ∈ y(c⁻¹) Bo`. -/
theorem x_mul_self_mem (h : IsRankOneBruhatData Bo T x y n) {c : 𝕜} (hc : c ≠ 0) :
    ∃ b ∈ Bo, x c * n = y c⁻¹ * b := by
  obtain ⟨t, ht, hy⟩ := h.partner c⁻¹ (inv_ne_zero hc)
  rw [inv_inv] at hy
  refine ⟨(x c)⁻¹ * (n⁻¹ * t⁻¹ * n),
    mul_mem (inv_mem (h.x_mem c)) (h.torus_le (h.conj_inv_mem (inv_mem ht))), ?_⟩
  rw [hy]
  group

/-- For these parameters,

```lean
y c ∈ rankOneParabolic Bo n
```
-/
theorem y_mem_parabolic (h : IsRankOneBruhatData Bo T x y n) (c : 𝕜) :
    y c ∈ rankOneParabolic Bo n := by
  by_cases hc : c = 0
  · left
    rw [hc, h.y_zero]
    exact one_mem _
  · right
    obtain ⟨t, ht, hy⟩ := h.partner c hc
    exact ⟨x c⁻¹ * t, mul_mem (h.x_mem _) (h.torus_le ht), x c⁻¹, h.x_mem _, hy⟩

/-- For `d ≠ 0`, `y(d) ∈ Bo n Bo`. -/
theorem y_mem_doubleCoset (h : IsRankOneBruhatData Bo T x y n) {d : 𝕜} (hd : d ≠ 0) :
    y d ∈ subgroupDoubleCoset Bo n := by
  obtain ⟨t, ht, hy⟩ := h.partner d hd
  exact ⟨x d⁻¹ * t, mul_mem (h.x_mem _) (h.torus_le ht), x d⁻¹, h.x_mem _, hy⟩

/-- For these parameters,

```lean
n ∈ rankOneParabolic Bo n
```
-/
theorem self_mem_parabolic : n ∈ rankOneParabolic Bo n :=
  Or.inr (mem_subgroupDoubleCoset_self _ _)

/-- For these parameters,

```lean
b * p ∈ rankOneParabolic Bo n
```
-/
theorem mul_mem_parabolic {b p : G} (hb : b ∈ Bo) (hp : p ∈ rankOneParabolic Bo n) :
    b * p ∈ rankOneParabolic Bo n := by
  rcases hp with hp | hp
  · exact Or.inl (mul_mem hb hp)
  · exact Or.inr (mul_mem_subgroupDoubleCoset hp hb)

/-- For these parameters,

```lean
p * b ∈ rankOneParabolic Bo n
```
-/
theorem parabolic_mul_mem {b p : G} (hp : p ∈ rankOneParabolic Bo n) (hb : b ∈ Bo) :
    p * b ∈ rankOneParabolic Bo n := by
  rcases hp with hp | hp
  · exact Or.inl (mul_mem hp hb)
  · exact Or.inr (subgroupDoubleCoset_mul_mem hp hb)

/-- For these parameters,

```lean
p⁻¹ ∈ rankOneParabolic Bo n
```
-/
theorem parabolic_inv (h : IsRankOneBruhatData Bo T x y n) {p : G}
    (hp : p ∈ rankOneParabolic Bo n) : p⁻¹ ∈ rankOneParabolic Bo n := by
  rcases hp with hp | hp
  · exact Or.inl (inv_mem hp)
  · exact Or.inr (h.doubleCoset_inv hp)

/-- **The rank-one parabolic as a projective line**: every element is
`y(c) b` or `n b` with `b ∈ Bo`. -/
theorem parabolic_cases (h : IsRankOneBruhatData Bo T x y n) {p : G}
    (hp : p ∈ rankOneParabolic Bo n) :
    (∃ c : 𝕜, ∃ b ∈ Bo, p = y c * b) ∨ ∃ b ∈ Bo, p = n * b := by
  rcases hp with hp | ⟨h₁, hh₁, h₂, hh₂, rfl⟩
  · exact Or.inl ⟨0, p, hp, by rw [h.y_zero, one_mul]⟩
  · obtain ⟨c, b', hb', he⟩ := h.borel_mul h₁ hh₁
    by_cases hc : c = 0
    · right
      refine ⟨b' * h₂, mul_mem hb' hh₂, ?_⟩
      rw [he, hc, h.x_zero]
      group
    · left
      obtain ⟨b, hb, hxb⟩ := h.x_mul_self_mem hc
      refine ⟨c⁻¹, b * b' * h₂, mul_mem (mul_mem hb hb') hh₂, ?_⟩
      rw [he, hxb]
      group

/-- **Rank-one multiplication**: `Bo n Bo · Bo n Bo ⊆ Bo ∪ Bo n Bo`. -/
theorem doubleCoset_mul (h : IsRankOneBruhatData Bo T x y n) {g g' : G}
    (hg : g ∈ subgroupDoubleCoset Bo n) (hg' : g' ∈ subgroupDoubleCoset Bo n) :
    g * g' ∈ rankOneParabolic Bo n := by
  obtain ⟨h₁, hh₁, h₂, hh₂, rfl⟩ := hg
  obtain ⟨h₁', hh₁', h₂', hh₂', rfl⟩ := hg'
  obtain ⟨c, b', hb', he⟩ := h.borel_mul (h₂ * h₁') (mul_mem hh₂ hh₁')
  obtain ⟨c', hc'⟩ := h.conj_x c
  have heq : h₁ * n * h₂ * (h₁' * n * h₂') = h₁ * y c' * (n * n * b' * h₂') := by
    calc h₁ * n * h₂ * (h₁' * n * h₂') = h₁ * n * ((h₂ * h₁') * n) * h₂' := by group
      _ = h₁ * n * (x c * n * b') * h₂' := by rw [he]
      _ = h₁ * (n * x c * n⁻¹) * (n * n * b' * h₂') := by group
      _ = h₁ * y c' * (n * n * b' * h₂') := by rw [hc']
  rw [heq]
  exact parabolic_mul_mem (mul_mem_parabolic hh₁ (h.y_mem_parabolic c'))
    (mul_mem (mul_mem (h.torus_le h.sq_mem) hb') hh₂')

end IsRankOneBruhatData

/-- The rank-one sweep of a set `Y`: all `g` with `g y(c) ∈ Y` for some `c`, or
`g n ∈ Y`. -/
def sweepSet (y : 𝕜 → G) (n : G) (Y : Set G) : Set G :=
  {g | ∃ c : 𝕜, g * y c ∈ Y} ∪ {g | g * n ∈ Y}

namespace IsRankOneBruhatData

variable {Bo T : Subgroup G} {x y : 𝕜 → G} {n : G}

/-- For a right-`Bo`-stable `Y`, the sweep is `Y P⁻¹ = {g | ∃ p ∈ P, g p ∈ Y}`. -/
theorem mem_sweepSet_iff (h : IsRankOneBruhatData Bo T x y n) {Y : Set G}
    (hY : ∀ g ∈ Y, ∀ b ∈ Bo, g * b ∈ Y) (g : G) :
    g ∈ sweepSet y n Y ↔ ∃ p ∈ rankOneParabolic Bo n, g * p ∈ Y := by
  constructor
  · rintro (⟨c, hc⟩ | hn)
    · exact ⟨y c, h.y_mem_parabolic c, hc⟩
    · exact ⟨n, self_mem_parabolic, hn⟩
  · rintro ⟨p, hp, hgp⟩
    rcases h.parabolic_cases hp with ⟨c, b, hb, rfl⟩ | ⟨b, hb, rfl⟩
    · left
      refine ⟨c, ?_⟩
      have := hY _ hgp b⁻¹ (inv_mem hb)
      simpa only [mul_assoc, mul_inv_cancel, mul_one] using this
    · right
      show g * n ∈ Y
      have := hY _ hgp b⁻¹ (inv_mem hb)
      simpa only [mul_assoc, mul_inv_cancel, mul_one] using this

/-- For these parameters,

```lean
∀ g ∈ sweepSet y n Y, ∀ b ∈ Bo, g * b ∈ sweepSet y n Y
```
-/
theorem sweepSet_stable (h : IsRankOneBruhatData Bo T x y n) {Y : Set G}
    (hY : ∀ g ∈ Y, ∀ b ∈ Bo, g * b ∈ Y) :
    ∀ g ∈ sweepSet y n Y, ∀ b ∈ Bo, g * b ∈ sweepSet y n Y := by
  intro g hg b hb
  obtain ⟨p, hp, hgp⟩ := (h.mem_sweepSet_iff hY g).mp hg
  refine (h.mem_sweepSet_iff hY (g * b)).mpr ⟨b⁻¹ * p, mul_mem_parabolic (inv_mem hb) hp, ?_⟩
  simpa only [mul_assoc, mul_inv_cancel_left] using hgp

/-- The rank-one relation needed for projective-line elimination. -/
theorem sweep_rel (h : IsRankOneBruhatData Bo T x y n) {Y : Set G}
    (hY : ∀ g ∈ Y, ∀ b ∈ Bo, g * b ∈ Y) (g : G) (c : 𝕜) (hc : c ≠ 0) :
    g * y c ∈ Y ↔ g * x c⁻¹ * n ∈ Y := by
  obtain ⟨t, ht, hy⟩ := h.partner c hc
  have hb : n⁻¹ * t * n * x c⁻¹ ∈ Bo :=
    mul_mem (h.torus_le (h.conj_inv_mem ht)) (h.x_mem _)
  have heq : g * y c = g * x c⁻¹ * n * (n⁻¹ * t * n * x c⁻¹) := by
    rw [hy]
    group
  rw [heq]
  constructor
  · intro hm
    have := hY _ hm _ (inv_mem hb)
    simpa only [mul_inv_cancel_right] using this
  · intro hm
    exact hY _ hm _ hb

end IsRankOneBruhatData

end RankOne

end ReductiveGroups
