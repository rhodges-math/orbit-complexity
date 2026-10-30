import OrbitComplexity.ReductiveGroups.Roots.Coxeter.WordProperty
import OrbitComplexity.ReductiveGroups.Roots.Coxeter.DihedralLength
import OrbitComplexity.ReductiveGroups.Roots.Coxeter.Exchange
import OrbitComplexity.ReductiveGroups.Roots.Inversions.InversionsWords

/-! # Root reflection data and abstract Weyl representative systems -/

noncomputable section
namespace ReductiveGroups

open CoxeterSystem

section Basic

variable {ι R M₀ N₀ : Type*} [CommRing R]
  [AddCommGroup M₀] [Module R M₀] [AddCommGroup N₀] [Module R N₀]
  {P : RootPairing ι R M₀ N₀} {G : Type*} [Group G]

/-- Hypotheses on chosen root reflection points `f r` in a group `G`, relative
to a subgroup `T` and a relation `Tr g σ` ("`g` transports the roots by `σ`"). -/
structure IsWeylRepresentativeSystem (P : RootPairing ι R M₀ N₀) (T : Subgroup G)
    (f : ι → G) (Tr : G → Equiv.Perm ι → Prop) : Prop where
  mem_normalizer : ∀ r, f r ∈ Subgroup.normalizer (T : Set G)
  sq_mem : ∀ r, f r ^ 2 ∈ T
  transport_one : Tr 1 1
  transport_mul : ∀ g h σ τ, Tr g σ → Tr h τ → Tr (g * h) (σ * τ)
  transport_reflection : ∀ r, Tr (f r) (P.reflectionPerm r)
  conj_mem : ∀ g σ, g ∈ Subgroup.normalizer (T : Set G) → Tr g σ →
    ∀ r, ∃ t ∈ T, g * f r * g⁻¹ = t * f (σ r)

/-- The ordered product `f(i₁) ⋯ f(iₖ)` along a word in the simple roots. -/
def simpleWordPoint (f : ι → G) (b : P.Base) (l : List b.support) : G :=
  (l.map fun i : b.support => f (i : ι)).prod

/-- The equality is

```lean
simpleWordPoint f b [] = 1
```
-/
@[simp] theorem simpleWordPoint_nil (f : ι → G) (b : P.Base) :
    simpleWordPoint f b [] = 1 := List.prod_nil

/-- The equality is

```lean
simpleWordPoint f b (i :: l) = f (i : ι) * simpleWordPoint f b l
```
-/
@[simp] theorem simpleWordPoint_cons (f : ι → G) (b : P.Base) (i : b.support)
    (l : List b.support) :
    simpleWordPoint f b (i :: l) = f (i : ι) * simpleWordPoint f b l := List.prod_cons

/-- The equality is

```lean
simpleWordPoint f b (l ++ k) = simpleWordPoint f b l * simpleWordPoint f b k
```
-/
theorem simpleWordPoint_append (f : ι → G) (b : P.Base) (l k : List b.support) :
    simpleWordPoint f b (l ++ k) = simpleWordPoint f b l * simpleWordPoint f b k := by
  rw [simpleWordPoint, List.map_append, List.prod_append]
  rfl

/-- The equality is

```lean
simpleWordPoint f b [i] = f (i : ι)
```
-/
theorem simpleWordPoint_singleton (f : ι → G) (b : P.Base) (i : b.support) :
    simpleWordPoint f b [i] = f (i : ι) := by
  rw [simpleWordPoint_cons, simpleWordPoint_nil, mul_one]

/-- Conjugating a `T`-coset relation by an element of the normalizer. -/
theorem exists_mem_mul_conj {T : Subgroup G} {g a c : G}
    (hg : g ∈ Subgroup.normalizer (T : Set G))
    (ha : ∃ t ∈ T, a = t * c) : ∃ t ∈ T, g * a = t * (g * c) := by
  obtain ⟨t, ht, rfl⟩ := ha
  refine ⟨g * t * g⁻¹, (Subgroup.mem_normalizer_iff.mp hg t).mp ht, ?_⟩
  group

/-- Transitivity of the `T`-coset relation. -/
theorem exists_mem_mul_trans {T : Subgroup G} {a c d : G}
    (ha : ∃ t ∈ T, a = t * c) (hc : ∃ t ∈ T, c = t * d) :
    ∃ t ∈ T, a = t * d := by
  obtain ⟨t, ht, rfl⟩ := ha
  obtain ⟨t', ht', rfl⟩ := hc
  exact ⟨t * t', mul_mem ht ht', by group⟩

variable {T : Subgroup G} {f : ι → G} {Tr : G → Equiv.Perm ι → Prop}

namespace IsWeylRepresentativeSystem

/-- Every word product normalizes `T`. -/
theorem simpleWordPoint_mem_normalizer (h : IsWeylRepresentativeSystem P T f Tr)
    (b : P.Base) (l : List b.support) :
    simpleWordPoint f b l ∈ Subgroup.normalizer (T : Set G) := by
  apply Subgroup.list_prod_mem
  intro g hg
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp hg
  exact h.mem_normalizer _

/-- A word product transports the roots by the root permutation of the
corresponding Weyl element. -/
theorem simpleWordPoint_transport (h : IsWeylRepresentativeSystem P T f Tr)
    (b : P.Base) (l : List b.support) :
    Tr (simpleWordPoint f b l) (P.weylGroupToPerm (simpleWeylWord b l)) := by
  induction l with
  | nil =>
    rw [simpleWordPoint_nil, show simpleWeylWord b [] = 1 from rfl, map_one]
    exact h.transport_one
  | cons i l ih =>
    rw [simpleWordPoint_cons, show simpleWeylWord b (i :: l) =
      RootPairing.weylGroup.ofIdx P (i : ι) * simpleWeylWord b l from rfl, map_mul,
      weylGroupToPerm_simple]
    exact h.transport_mul _ _ _ _ (h.transport_reflection _) ih

end IsWeylRepresentativeSystem

end Basic

end ReductiveGroups
