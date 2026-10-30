import OrbitComplexity.ReductiveGroups.Roots.Coxeter.WordProperty
import OrbitComplexity.ReductiveGroups.Roots.Coxeter.DihedralLength
import OrbitComplexity.ReductiveGroups.Roots.Coxeter.Exchange
import OrbitComplexity.ReductiveGroups.Roots.Inversions.InversionsWords
import OrbitComplexity.ReductiveGroups.Groups.Representatives.RepresentativeSystem

/-! # Words in abstract Weyl representative systems -/

noncomputable section
namespace ReductiveGroups

open CoxeterSystem

section Weyl

variable {ι R M₀ N₀ : Type*} [CommRing R] [CharZero R]
  [AddCommGroup M₀] [Module R M₀] [AddCommGroup N₀] [Module R N₀]
  {P : RootPairing ι R M₀ N₀} [Finite ι] [IsDomain R]
  [P.IsCrystallographic] [P.IsReduced]

/-- **Rank-two prefix.** If `m = m_{ij} = k + 1`, the alternating word of length
`k` ending in `i` sends the simple root `j` to the simple root that begins the
opposite braid word (`i` if `k` is even, `j` if `k` is odd). -/
theorem weylGroupToPerm_braidPrefix (b : P.Base) (i j : b.support)
    (k : ℕ) (hk : simpleCoxeterMatrix b i j = k + 1) :
    P.weylGroupToPerm (simpleWeylWord b (alternatingWord j i k)) (j : ι) =
      ((if Even k then i else j : b.support) : ι) := by
  set W' := simpleWeylWord b (alternatingWord j i k) with hW'
  set x : b.support := if Even k then i else j with hx
  have hA : braidWord (simpleCoxeterMatrix b) i j = alternatingWord j i k ++ [j] := by
    rw [braidWord, hk, alternatingWord_succ, List.concat_eq_append]
  have hB : braidWord (simpleCoxeterMatrix b) j i = x :: alternatingWord j i k := by
    rw [braidWord, (simpleCoxeterMatrix b).symmetric j i, hk, alternatingWord_succ']
  have hbraid := simpleWeylWord_braidWord_eq b i j
  rw [hA, hB, simpleWeylWord_append] at hbraid
  have h1 : W' * RootPairing.weylGroup.ofIdx P (j : ι) =
      RootPairing.weylGroup.ofIdx P (x : ι) * W' := by
    simpa only [simpleWeylWord, mul_one] using hbraid
  have h2 := simpleWeylWord_mul_reflection b (alternatingWord j i k) (j : ι)
  have hofIdx : RootPairing.weylGroup.ofIdx P (P.weylGroupToPerm W' (j : ι)) =
      RootPairing.weylGroup.ofIdx P (x : ι) :=
    mul_right_cancel (h2.symm.trans h1)
  have hpos : b.IsPos (P.weylGroupToPerm W' (j : ι)) := by
    by_contra hneg
    have hcount := rootInversionCount_mul_simple_of_neg b W' j
      ((root_height_neg_iff_not_isPos b _).mpr hneg)
    have hAcount := rootInversionCount_braidWord b i j
    rw [hA, simpleWeylWord_append] at hAcount
    simp only [simpleWeylWord, mul_one] at hAcount
    have hle := RootInversionCount.simpleWeylWord_le_length b (alternatingWord j i k)
    rw [length_alternatingWord] at hle
    rw [← hW'] at hAcount hle
    omega
  have hmem : P.weylGroupToPerm W' (j : ι) ∈
      leftRootInversionIndices b
        (RootPairing.weylGroup.ofIdx P (P.weylGroupToPerm W' (j : ι))) := by
    rw [mem_leftRootInversionIndices, weylGroup_simple_inv, weylGroupToPerm_simple,
      isPos_neg_index_iff]
    exact ⟨hpos, not_not.mpr hpos⟩
  rw [hofIdx, leftRootInversionIndices_simple] at hmem
  exact hmem

/-- A chosen reduced word for each element of the Weyl group. -/
def chosenReducedWord (b : P.Base) (w : P.weylGroup) : List b.support :=
  Classical.choose ((weylCoxeterSystem b).exists_isReduced w)

/-- For these parameters,

```lean
(weylCoxeterSystem b).IsReduced (chosenReducedWord b w)
```
-/
theorem chosenReducedWord_isReduced (b : P.Base) (w : P.weylGroup) :
    (weylCoxeterSystem b).IsReduced (chosenReducedWord b w) :=
  (Classical.choose_spec ((weylCoxeterSystem b).exists_isReduced w)).1

/-- The equality is

```lean
simpleWeylWord b (chosenReducedWord b w) = w
```
-/
@[simp] theorem simpleWeylWord_chosenReducedWord (b : P.Base) (w : P.weylGroup) :
    simpleWeylWord b (chosenReducedWord b w) = w := by
  rw [← weylCoxeterSystem_wordProd]
  exact (Classical.choose_spec ((weylCoxeterSystem b).exists_isReduced w)).2.symm

/-- The equality is

```lean
chosenReducedWord b (1 : P.weylGroup) = []
```
-/
theorem chosenReducedWord_one (b : P.Base) : chosenReducedWord b (1 : P.weylGroup) = [] := by
  have hred := chosenReducedWord_isReduced b 1
  have hlen : (chosenReducedWord b 1).length = 0 := by
    rw [← hred.eq, weylCoxeterSystem_wordProd, simpleWeylWord_chosenReducedWord,
      CoxeterSystem.length_one]
  exact List.length_eq_zero_iff.mp hlen

variable {G : Type*} [Group G]

/-- The representative of a Weyl element: the word product along its chosen
reduced word. -/
def weylElementPoint (f : ι → G) (b : P.Base) (w : P.weylGroup) : G :=
  simpleWordPoint f b (chosenReducedWord b w)

/-- The equality is

```lean
weylElementPoint f b 1 = 1
```
-/
@[simp] theorem weylElementPoint_one (f : ι → G) (b : P.Base) :
    weylElementPoint f b 1 = 1 := by
  rw [weylElementPoint, chosenReducedWord_one, simpleWordPoint_nil]

variable {T : Subgroup G} {f : ι → G} {Tr : G → Equiv.Perm ι → Prop}

namespace IsWeylRepresentativeSystem

/-- **Braid relations modulo `T`.** For distinct simple roots `i, j`, the two
braid words have products in the same `T`-coset. -/
theorem simpleWordPoint_braid (h : IsWeylRepresentativeSystem P T f Tr)
    (b : P.Base) {i j : b.support} (hij : i ≠ j) :
    ∃ t ∈ T, simpleWordPoint f b (braidWord (simpleCoxeterMatrix b) i j) =
      t * simpleWordPoint f b (braidWord (simpleCoxeterMatrix b) j i) := by
  have htwo := simpleCoxeterMatrix_two_le b hij
  obtain ⟨k, hk⟩ : ∃ k, simpleCoxeterMatrix b i j = k + 1 :=
    ⟨simpleCoxeterMatrix b i j - 1, by omega⟩
  set x : b.support := if Even k then i else j with hx
  have hA : braidWord (simpleCoxeterMatrix b) i j = alternatingWord j i k ++ [j] := by
    rw [braidWord, hk, alternatingWord_succ, List.concat_eq_append]
  have hB : braidWord (simpleCoxeterMatrix b) j i = x :: alternatingWord j i k := by
    rw [braidWord, (simpleCoxeterMatrix b).symmetric j i, hk, alternatingWord_succ']
  set g := simpleWordPoint f b (alternatingWord j i k) with hg
  obtain ⟨t, ht, hconj⟩ := h.conj_mem g _ (h.simpleWordPoint_mem_normalizer b _)
    (h.simpleWordPoint_transport b (alternatingWord j i k)) (j : ι)
  rw [weylGroupToPerm_braidPrefix b i j k hk, ← hx] at hconj
  refine ⟨t, ht, ?_⟩
  rw [hA, hB, simpleWordPoint_append, simpleWordPoint_singleton, simpleWordPoint_cons, ← hg]
  calc g * f (j : ι) = (g * f (j : ι) * g⁻¹) * g := by group
    _ = t * (f (x : ι) * g) := by rw [hconj, mul_assoc]

/-- A braid move changes the word product by a factor in `T`. -/
theorem simpleWordPoint_of_braidMove (h : IsWeylRepresentativeSystem P T f Tr)
    (b : P.Base) {l k : List b.support} (hm : WeylBraidMove b l k) :
    ∃ t ∈ T, simpleWordPoint f b l = t * simpleWordPoint f b k := by
  obtain ⟨pre, post, i, j, hij, rfl, rfl⟩ := hm
  obtain ⟨t, ht, hbr⟩ := h.simpleWordPoint_braid b hij
  obtain ⟨t', ht', heq⟩ :=
    exists_mem_mul_conj (h.simpleWordPoint_mem_normalizer b pre) ⟨t, ht, hbr⟩
  refine ⟨t', ht', ?_⟩
  rw [simpleWordPoint_append, simpleWordPoint_append, heq, simpleWordPoint_append,
    simpleWordPoint_append, mul_assoc]

/-- A finite chain of braid moves changes the word product by a factor in `T`. -/
theorem simpleWordPoint_of_braidChain (h : IsWeylRepresentativeSystem P T f Tr)
    (b : P.Base) {l k : List b.support} (hc : WeylBraidChain b l k) :
    ∃ t ∈ T, simpleWordPoint f b l = t * simpleWordPoint f b k := by
  induction hc with
  | refl => exact ⟨1, one_mem T, (one_mul _).symm⟩
  | tail _ hm ih => exact exists_mem_mul_trans ih (h.simpleWordPoint_of_braidMove b hm)

/-- **Well-definedness modulo `T`.** Two reduced words with the same Weyl
element have word products in the same `T`-coset. -/
theorem simpleWordPoint_of_reduced (h : IsWeylRepresentativeSystem P T f Tr)
    (b : P.Base) {l k : List b.support}
    (hl : (weylCoxeterSystem b).IsReduced l)
    (hk : (weylCoxeterSystem b).IsReduced k)
    (heq : simpleWeylWord b l = simpleWeylWord b k) :
    ∃ t ∈ T, simpleWordPoint f b l = t * simpleWordPoint f b k := by
  apply h.simpleWordPoint_of_braidChain b
  apply weylCoxeterSystem_word_property b l k hl hk
  simpa only [weylCoxeterSystem_wordProd] using heq

/-- The product along any reduced word of `w` lies in `T ẇ`. -/
theorem simpleWordPoint_of_isReduced (h : IsWeylRepresentativeSystem P T f Tr)
    (b : P.Base) {l : List b.support} (hl : (weylCoxeterSystem b).IsReduced l) :
    ∃ t ∈ T, simpleWordPoint f b l = t * weylElementPoint f b (simpleWeylWord b l) :=
  h.simpleWordPoint_of_reduced b hl (chosenReducedWord_isReduced b _)
    (simpleWeylWord_chosenReducedWord b _).symm

/-- `ẇ` transports the roots by the root permutation of `w`. -/
theorem weylElementPoint_transport (h : IsWeylRepresentativeSystem P T f Tr)
    (b : P.Base) (w : P.weylGroup) :
    Tr (weylElementPoint f b w) (P.weylGroupToPerm w) := by
  have ht := h.simpleWordPoint_transport b (chosenReducedWord b w)
  rwa [simpleWeylWord_chosenReducedWord] at ht

/-- `ẇ` normalizes `T`. -/
theorem weylElementPoint_mem_normalizer (h : IsWeylRepresentativeSystem P T f Tr)
    (b : P.Base) (w : P.weylGroup) :
    weylElementPoint f b w ∈ Subgroup.normalizer (T : Set G) :=
  h.simpleWordPoint_mem_normalizer b _

/-- **Length-additive products.** If `ℓ(uv) = ℓ(u) + ℓ(v)` then `u̇ v̇ ∈ T (uv)˙`. -/
theorem weylElementPoint_mul_of_length_add (h : IsWeylRepresentativeSystem P T f Tr)
    (b : P.Base) (u v : P.weylGroup)
    (huv : (weylCoxeterSystem b).length (u * v) =
      (weylCoxeterSystem b).length u + (weylCoxeterSystem b).length v) :
    ∃ t ∈ T, weylElementPoint f b u * weylElementPoint f b v =
      t * weylElementPoint f b (u * v) := by
  have hprod : simpleWeylWord b (chosenReducedWord b u ++ chosenReducedWord b v) = u * v := by
    rw [simpleWeylWord_append, simpleWeylWord_chosenReducedWord,
      simpleWeylWord_chosenReducedWord]
  have hred : (weylCoxeterSystem b).IsReduced
      (chosenReducedWord b u ++ chosenReducedWord b v) := by
    change (weylCoxeterSystem b).length
      ((weylCoxeterSystem b).wordProd (chosenReducedWord b u ++ chosenReducedWord b v)) =
        (chosenReducedWord b u ++ chosenReducedWord b v).length
    rw [weylCoxeterSystem_wordProd, hprod, huv, List.length_append,
      ← (chosenReducedWord_isReduced b u).eq, ← (chosenReducedWord_isReduced b v).eq,
      weylCoxeterSystem_wordProd, weylCoxeterSystem_wordProd,
      simpleWeylWord_chosenReducedWord, simpleWeylWord_chosenReducedWord]
  have h' := h.simpleWordPoint_of_isReduced b hred
  rw [hprod, simpleWordPoint_append] at h'
  exact h'

/-- A simple reflection that lengthens `w`: `f(i) ẇ ∈ T (s_i w)˙`. -/
theorem simple_mul_weylElementPoint_of_length (h : IsWeylRepresentativeSystem P T f Tr)
    (b : P.Base) (i : b.support) (w : P.weylGroup)
    (hl : (weylCoxeterSystem b).length (RootPairing.weylGroup.ofIdx P (i : ι) * w) =
      (weylCoxeterSystem b).length w + 1) :
    ∃ t ∈ T, f (i : ι) * weylElementPoint f b w =
      t * weylElementPoint f b (RootPairing.weylGroup.ofIdx P (i : ι) * w) := by
  have hprod : simpleWeylWord b (i :: chosenReducedWord b w) =
      RootPairing.weylGroup.ofIdx P (i : ι) * w := by
    change RootPairing.weylGroup.ofIdx P (i : ι) * simpleWeylWord b (chosenReducedWord b w) = _
    rw [simpleWeylWord_chosenReducedWord]
  have hred : (weylCoxeterSystem b).IsReduced (i :: chosenReducedWord b w) := by
    change (weylCoxeterSystem b).length
      ((weylCoxeterSystem b).wordProd (i :: chosenReducedWord b w)) =
        (i :: chosenReducedWord b w).length
    rw [weylCoxeterSystem_wordProd, hprod, hl, List.length_cons,
      ← (chosenReducedWord_isReduced b w).eq, weylCoxeterSystem_wordProd,
      simpleWeylWord_chosenReducedWord]
  have h' := h.simpleWordPoint_of_isReduced b hred
  rw [hprod, simpleWordPoint_cons] at h'
  exact h'

/-- For every simple reflection and every `w`: `f(i) ẇ ∈ T (s_i w)˙`. -/
theorem simple_mul_weylElementPoint (h : IsWeylRepresentativeSystem P T f Tr)
    (b : P.Base) (i : b.support) (w : P.weylGroup) :
    ∃ t ∈ T, f (i : ι) * weylElementPoint f b w =
      t * weylElementPoint f b (RootPairing.weylGroup.ofIdx P (i : ι) * w) := by
  have hsimple : (weylCoxeterSystem b).simple i = RootPairing.weylGroup.ofIdx P (i : ι) :=
    weylCoxeterSystem_simple b i
  rcases (weylCoxeterSystem b).length_simple_mul w i with hl | hl
  · rw [hsimple] at hl
    exact h.simple_mul_weylElementPoint_of_length b i w hl
  · rw [hsimple] at hl
    set v := RootPairing.weylGroup.ofIdx P (i : ι) * w with hv
    have hvw : RootPairing.weylGroup.ofIdx P (i : ι) * v = w := by
      rw [hv, weylGroup_ofIdx_mul_cancel_left]
    have hlv : (weylCoxeterSystem b).length (RootPairing.weylGroup.ofIdx P (i : ι) * v) =
        (weylCoxeterSystem b).length v + 1 := by
      rw [hvw]
      exact hl.symm
    obtain ⟨t, ht, heq⟩ := h.simple_mul_weylElementPoint_of_length b i v hlv
    rw [hvw] at heq
    have hsq := h.sq_mem (i : ι)
    have hconj := (Subgroup.mem_normalizer_iff.mp (h.mem_normalizer (i : ι)) t⁻¹).mp
      (inv_mem ht)
    refine ⟨f (i : ι) * t⁻¹ * (f (i : ι))⁻¹ * f (i : ι) ^ 2, mul_mem hconj hsq, ?_⟩
    have hw : weylElementPoint f b w = t⁻¹ * (f (i : ι) * weylElementPoint f b v) := by
      rw [heq]
      group
    rw [hw]
    group

/-- A word product times a representative: `n_l v̇ ∈ T (π(l) v)˙`. -/
theorem simpleWordPoint_mul_weylElementPoint (h : IsWeylRepresentativeSystem P T f Tr)
    (b : P.Base) (l : List b.support) (v : P.weylGroup) :
    ∃ t ∈ T, simpleWordPoint f b l * weylElementPoint f b v =
      t * weylElementPoint f b (simpleWeylWord b l * v) := by
  induction l with
  | nil =>
    refine ⟨1, one_mem T, ?_⟩
    rw [simpleWordPoint_nil, show simpleWeylWord b [] = 1 from rfl, one_mul, one_mul, one_mul]
  | cons i l ih =>
    have h1 : ∃ t ∈ T, f (i : ι) * (simpleWordPoint f b l * weylElementPoint f b v) =
        t * (f (i : ι) * weylElementPoint f b (simpleWeylWord b l * v)) :=
      exists_mem_mul_conj (h.mem_normalizer _) ih
    have h2 := h.simple_mul_weylElementPoint b i (simpleWeylWord b l * v)
    obtain ⟨t, ht, heq⟩ := exists_mem_mul_trans h1
      (exists_mem_mul_conj (T := T) (g := 1) (one_mem _) h2 |>.imp fun t ⟨ht, he⟩ =>
        ⟨ht, by simpa only [one_mul] using he⟩)
    refine ⟨t, ht, ?_⟩
    rw [simpleWordPoint_cons, mul_assoc, heq, show simpleWeylWord b (i :: l) =
      RootPairing.weylGroup.ofIdx P (i : ι) * simpleWeylWord b l from rfl, mul_assoc]

/-- **Products of representatives.** For all `u, v`: `u̇ v̇ ∈ T (uv)˙`. -/
theorem weylElementPoint_mul (h : IsWeylRepresentativeSystem P T f Tr)
    (b : P.Base) (u v : P.weylGroup) :
    ∃ t ∈ T, weylElementPoint f b u * weylElementPoint f b v =
      t * weylElementPoint f b (u * v) := by
  have h' := h.simpleWordPoint_mul_weylElementPoint b (chosenReducedWord b u) v
  rwa [simpleWeylWord_chosenReducedWord] at h'

/-- The product along any word `l` lies in `T (π l)˙`. -/
theorem simpleWordPoint_eq_mul_weylElementPoint (h : IsWeylRepresentativeSystem P T f Tr)
    (b : P.Base) (l : List b.support) :
    ∃ t ∈ T, simpleWordPoint f b l = t * weylElementPoint f b (simpleWeylWord b l) := by
  have h' := h.simpleWordPoint_mul_weylElementPoint b l 1
  rwa [weylElementPoint_one, mul_one, mul_one] at h'

/-- The chosen point of a simple root lies in `T (s_i)˙`. -/
theorem simple_eq_mul_weylElementPoint (h : IsWeylRepresentativeSystem P T f Tr)
    (b : P.Base) (i : b.support) :
    ∃ t ∈ T, f (i : ι) = t * weylElementPoint f b (RootPairing.weylGroup.ofIdx P (i : ι)) := by
  have h' := h.simpleWordPoint_eq_mul_weylElementPoint b [i]
  rwa [simpleWordPoint_singleton, show simpleWeylWord b [i] =
    RootPairing.weylGroup.ofIdx P (i : ι) * 1 from rfl, mul_one] at h'

/-- `ẇ⁻¹ ∈ T (w⁻¹)˙`. -/
theorem weylElementPoint_inv (h : IsWeylRepresentativeSystem P T f Tr)
    (b : P.Base) (w : P.weylGroup) :
    ∃ t ∈ T, (weylElementPoint f b w)⁻¹ = t * weylElementPoint f b w⁻¹ := by
  obtain ⟨t, ht, hmul⟩ := h.weylElementPoint_mul b w⁻¹ w
  rw [inv_mul_cancel, weylElementPoint_one, mul_one] at hmul
  refine ⟨t⁻¹, inv_mem ht, ?_⟩
  rw [← hmul]
  group

end IsWeylRepresentativeSystem

end Weyl

end ReductiveGroups
