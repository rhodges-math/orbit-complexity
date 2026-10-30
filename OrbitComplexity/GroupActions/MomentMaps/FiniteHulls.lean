import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Batteries.Tactic.Lint

/-! # Finite convex hulls and exposing functionals

Barycentric coefficients and separating functionals describe exposed subsets of finite convex
hulls. A nonempty exposed subset is the hull of the generating points it contains.
-/

open Set Filter
open scoped BigOperators Topology
noncomputable section
namespace GroupActions
universe u v

section Shared
variable {I : Type u} [Fintype I]


variable {E : Type v} [AddCommGroup E] [Module ℝ E]

private theorem span_image_coefficients (w : I → E) (S : Set I) (y : E)
    (hy : y ∈ Submodule.span ℝ (w '' S)) :
    ∃ a : I → ℝ, (∀ i, i ∉ S → a i = 0) ∧ ∑ i, a i • w i = y := by
  classical
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, hi, rfl⟩ := hx
    refine ⟨Pi.single i 1, ?_, ?_⟩
    · intro j hj
      have hji : j ≠ i := by rintro rfl; exact hj hi
      simp [hji]
    · simp [Pi.single_apply, ite_smul]
  | zero => exact ⟨0, by simp, by simp⟩
  | add x y hx hy hxc hyc =>
    obtain ⟨a, ha, hax⟩ := hxc
    obtain ⟨b, hb, hby⟩ := hyc
    refine ⟨a + b, fun i hi ↦ by simp [ha i hi, hb i hi], ?_⟩
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib, hax, hby]
  | smul r x hx hxc =>
    obtain ⟨a, ha, hax⟩ := hxc
    refine ⟨r • a, fun i hi ↦ by simp [ha i hi], ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul, mul_smul, ← Finset.smul_sum, hax]

/-- Membership in a finite weight hull is equivalent to nonnegative barycentric coefficients. -/
theorem hull_image_coefficients (w : I → E) (S : Set I) (y : E) :
    y ∈ convexHull ℝ (w '' S) ↔
      ∃ a : I → ℝ, (∀ i, 0 ≤ a i) ∧ (∀ i, i ∉ S → a i = 0) ∧
        ∑ i, a i = 1 ∧ ∑ i, a i • w i = y := by
  classical
  constructor
  · apply convexHull_min
    · rintro x ⟨i, hi, rfl⟩
      refine ⟨Pi.single i 1, ?_, ?_, ?_, ?_⟩
      · intro j; simp [Pi.single_apply]; split <;> norm_num
      · intro j hj
        have hji : j ≠ i := by rintro rfl; exact hj hi
        simp [hji]
      · simp
      · simp [Pi.single_apply, ite_smul]
    · rintro x ⟨a, ha, haS, has, haw⟩ y ⟨b, hb, hbS, hbs, hbw⟩ r t hr ht hrt
      refine ⟨fun i ↦ r * a i + t * b i, ?_, ?_, ?_, ?_⟩
      · intro i; exact add_nonneg (mul_nonneg hr (ha i)) (mul_nonneg ht (hb i))
      · intro i hi; simp [haS i hi, hbS i hi]
      · rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, has, hbs]
        simpa using hrt
      · simp only [add_smul, mul_smul, Finset.sum_add_distrib, ← Finset.smul_sum, haw, hbw]
  · rintro ⟨a, ha, haS, has, haw⟩
    let t := Finset.univ.filter (fun i ↦ i ∈ S)
    have hts : ∑ i ∈ t, a i = 1 := by
      calc
        ∑ i ∈ t, a i = ∑ i, a i := by
          apply Finset.sum_subset (Finset.subset_univ t)
          intro i _ hi
          exact haS i (by simpa [t] using hi)
        _ = 1 := has
    have htw : ∑ i ∈ t, a i • w i = y := by
      calc
        ∑ i ∈ t, a i • w i = ∑ i, a i • w i := by
          apply Finset.sum_subset (Finset.subset_univ t)
          intro i _ hi
          rw [haS i (by simpa [t] using hi), zero_smul]
        _ = y := haw
    have hm := t.centerMass_mem_convexHull (fun i _ ↦ ha i) (by rw [hts]; norm_num)
      (fun i hi ↦ Set.mem_image_of_mem w (Finset.mem_filter.mp hi).2)
    rw [t.centerMass_eq_of_sum_1 w hts, htw] at hm
    exact hm

private theorem span_hull_disjoint (w : I → E) (S : Set I)
    (hrel : ∀ a : I → ℝ, ∑ i, a i • w i = 0 →
      (∀ i, i ∉ S → 0 ≤ a i) → ∀ i, i ∉ S → a i = 0) :
    Disjoint (Submodule.span ℝ (w '' S) : Set E) (convexHull ℝ (w '' Sᶜ)) := by
  classical
  apply Set.disjoint_left.mpr
  intro y hyS hyH
  obtain ⟨b, hbS, hby⟩ := span_image_coefficients w S y hyS
  obtain ⟨a, ha, haS, has, hay⟩ := (hull_image_coefficients w Sᶜ y).mp hyH
  have hzero : ∑ i, (a i - b i) • w i = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib, hay, hby, sub_self]
  have hz := hrel (fun i ↦ a i - b i) hzero (fun i hi ↦ by rw [hbS i hi, sub_zero]; exact ha i)
  have ha0 : a = 0 := by
    funext i
    by_cases hi : i ∈ S
    · exact haS i (by simpa using hi)
    · have ht := hz i hi
      change a i = 0
      simpa only [hbS i hi, sub_zero] using ht
  simp only [ha0, Pi.zero_apply, Finset.sum_const_zero] at has
  exact zero_ne_one has


variable [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [LocallyConvexSpace ℝ E] [T2Space E] [FiniteDimensional ℝ E]

/-- One-sided relation coefficients give a functional vanishing on the chosen weights. -/
theorem exists_exposing_form (w : I → E) (S : Set I)
    (hrel : ∀ a : I → ℝ, ∑ i, a i • w i = 0 →
      (∀ i, i ∉ S → 0 ≤ a i) → ∀ i, i ∉ S → a i = 0) :
    ∃ f : StrongDual ℝ E, (∀ i ∈ S, f (w i) = 0) ∧ (∀ i ∉ S, f (w i) < 0) := by
  classical
  let L := Submodule.span ℝ (w '' S)
  obtain ⟨f, u, v, hQ, huv, hL⟩ := geometric_hahn_banach_compact_closed
    (convex_convexHull ℝ (w '' Sᶜ)) ((Sᶜ.toFinite.image w).isCompact_convexHull ℝ)
    L.convex L.closed_of_finiteDimensional (span_hull_disjoint w S hrel).symm
  have hLzero (y : E) (hy : y ∈ L) : f y = 0 := by
    by_contra hf
    have ht := hL (((v - 1) / f y) • y) (L.smul_mem _ hy)
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hf] at ht
    linarith
  have hv : v < 0 := by simpa using hL 0 L.zero_mem
  refine ⟨f, ?_, ?_⟩
  · intro i hi
    exact hLzero (w i) (Submodule.subset_span (Set.mem_image_of_mem w hi))
  · intro i hi
    have ht := hQ (w i) (subset_convexHull ℝ _ (Set.mem_image_of_mem w hi))
    exact ht.trans (huv.trans hv)

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
  [T2Space E] [FiniteDimensional ℝ E] in
/-- A strict functional gap identifies the selected convex hull with the exposed set. -/
theorem convexHull_eq_toExposed (w : I → E) (S : Set I) (hS : S.Nonempty)
    (f : StrongDual ℝ E) (c : ℝ) (hbound : ∀ i, f (w i) ≤ c)
    (hvalue : ∀ i ∈ S, f (w i) = c) (hstrict : ∀ i ∉ S, f (w i) < c) :
    convexHull ℝ (w '' S) = f.toExposed (convexHull ℝ (Set.range w)) := by
  classical
  have hHullBound : ∀ x ∈ convexHull ℝ (Set.range w), f x ≤ c :=
    convexHull_min (by rintro _ ⟨i, rfl⟩; exact hbound i)
      (convex_halfSpace_le f.toLinearMap.isLinear c)
  have hLevel : ∀ x ∈ convexHull ℝ (w '' S), f x = c := by
    intro x hx
    obtain ⟨a, _, haS, has, haw⟩ := (hull_image_coefficients w S x).mp hx
    rw [← haw, map_sum]
    simp only [map_smul, smul_eq_mul]
    calc
      ∑ i, a i * f (w i) = ∑ i, a i * c := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : i ∈ S
        · rw [hvalue i hi]
        · rw [haS i hi, zero_mul, zero_mul]
      _ = c := by rw [← Finset.sum_mul, has, one_mul]
  refine Set.Subset.antisymm ?_ ?_
  · intro x hx
    refine ⟨convexHull_mono (Set.image_subset_range w S) hx, ?_⟩
    intro y hy
    rw [hLevel x hx]
    exact hHullBound y hy
  · intro x hx
    obtain ⟨i, hi⟩ := hS
    have hxc : f x = c := le_antisymm (hHullBound x hx.1) (by
      have ht := hx.2 (w i) (subset_convexHull ℝ _ (Set.mem_range_self i))
      simpa only [hvalue i hi] using ht)
    have hx' : x ∈ convexHull ℝ (w '' (Set.univ : Set I)) := by
      simpa only [Set.image_univ] using hx.1
    obtain ⟨a, ha, _, has, haw⟩ := (hull_image_coefficients w Set.univ x).mp hx'
    have hdeficit : ∑ i, a i * (c - f (w i)) = 0 := by
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul, has, one_mul]
      have ht : f x = ∑ i, a i * f (w i) := by
        rw [← haw, map_sum]
        simp only [map_smul, smul_eq_mul]
      rw [← ht, hxc, sub_self]
    have hazero (i : I) (hi : i ∉ S) : a i = 0 := by
      have ht := (Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ ↦ mul_nonneg (ha j) (sub_nonneg.mpr (hbound j)))).mp hdeficit i
          (Finset.mem_univ i)
      exact (mul_eq_zero.mp ht).resolve_right (ne_of_gt (sub_pos.mpr (hstrict i hi)))
    exact (hull_image_coefficients w S x).mpr ⟨a, ha, hazero, has, haw⟩


end Shared

/-- A nonempty exposed hull contains a generating point, with its exposing functional. -/
theorem exists_exposing_vertex {I E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] (weight : I → E) {F : Set E}
    (hF : IsExposed ℝ (convexHull ℝ (Set.range weight)) F) (hne : F.Nonempty) :
    ∃ ℓ : StrongDual ℝ E, ∃ i₀ : I,
      F = ℓ.toExposed (convexHull ℝ (Set.range weight)) ∧ weight i₀ ∈ F ∧
        (∀ i, ℓ (weight i) ≤ ℓ (weight i₀)) ∧
        (∀ i, weight i ∈ F ↔ ℓ (weight i) = ℓ (weight i₀)) := by
  obtain ⟨ℓ, hℓ⟩ := hF hne
  obtain ⟨y, hy⟩ := hne
  have hy' := hy
  rw [hℓ] at hy'
  obtain ⟨_, ⟨i₀, rfl⟩, hmax⟩ :=
    (ℓ.toLinearMap.convexOn convex_univ).exists_ge_of_mem_convexHull
      (Set.subset_univ _) hy'.1
  have hi₀ : weight i₀ ∈ F := by
    rw [hℓ]
    exact ⟨subset_convexHull ℝ _ (Set.mem_range_self _),
      fun z hz => (hy'.2 z hz).trans hmax⟩
  have hi₀' := hi₀
  rw [hℓ] at hi₀'
  refine ⟨ℓ, i₀, hℓ, hi₀, ?_, ?_⟩
  · intro i
    exact hi₀'.2 _ (subset_convexHull ℝ _ (Set.mem_range_self _))
  · intro i
    constructor
    · intro hi
      rw [hℓ] at hi
      exact le_antisymm
        (hi₀'.2 _ (subset_convexHull ℝ _ (Set.mem_range_self _)))
        (hi.2 _ hi₀'.1)
    · intro hi
      rw [hℓ]
      exact ⟨subset_convexHull ℝ _ (Set.mem_range_self _),
        fun z hz => hi ▸ hi₀'.2 z hz⟩


/-- An exposed face of a finite hull is the hull of the generators it contains. -/
theorem exposed_hull_eq {I E : Type*} [Fintype I] [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] (weight : I → E) {F : Set E}
    (hF : IsExposed ℝ (convexHull ℝ (Set.range weight)) F) (hne : F.Nonempty) :
    convexHull ℝ (weight '' {i | weight i ∈ F}) = F := by
  obtain ⟨ℓ, i₀, hface, hi₀, hbound, heq⟩ := exists_exposing_vertex weight hF hne
  exact (@convexHull_eq_toExposed I inferInstance E inferInstance inferInstance inferInstance
    weight {i | weight i ∈ F} ⟨i₀, hi₀⟩ ℓ (ℓ (weight i₀)) hbound
      (fun i hi => (heq i).mp hi)
      (fun i hi => lt_of_le_of_ne (hbound i) (fun h => hi ((heq i).mpr h)))).trans hface.symm


section Vertices
variable {E : Type v} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]

private theorem exposed_of_irredundant [DecidableEq E] (s : Finset E) (q : E) (hq : q ∈ s)
    (hnot : q ∉ convexHull ℝ (s.erase q : Set E)) :
    IsExposed ℝ (convexHull ℝ (s : Set E)) {q} := by
  classical
  obtain ⟨f, c, hsmall, hcut⟩ := geometric_hahn_banach_closed_point
    (convex_convexHull ℝ (s.erase q : Set E))
    ((s.erase q).finite_toSet.isClosed_convexHull ℝ) hnot
  have hbound (z : s) : f z.val ≤ f q := by
    by_cases hz : z.val = q
    · exact (congrArg f hz).le
    · exact ((hsmall z.val
        (subset_convexHull ℝ _ (Finset.mem_erase.mpr ⟨hz, z.property⟩))).trans hcut).le
  have hvalue (z : s) (hz : z ∈ {z : s | z.val = q}) : f z.val = f q :=
    congrArg f hz
  have hstrict (z : s) (hz : z ∉ {z : s | z.val = q}) : f z.val < f q :=
    (hsmall z.val
      (subset_convexHull ℝ _ (Finset.mem_erase.mpr ⟨hz, z.property⟩))).trans hcut
  have hselected : (Subtype.val : s → E) '' {z : s | z.val = q} = {q} := by
    ext x
    change (∃ z : s, z.val = q ∧ z.val = x) ↔ x = q
    constructor
    · rintro ⟨z, hz, hzx⟩
      exact hzx.symm.trans hz
    · intro hx
      exact ⟨⟨q, hq⟩, rfl, hx.symm⟩
  have hrange : Set.range (Subtype.val : s → E) = (s : Set E) :=
    Subtype.range_coe_subtype
  have heq := @convexHull_eq_toExposed s inferInstance E
    inferInstance inferInstance inferInstance (Subtype.val : s → E) {z : s | z.val = q}
      ⟨⟨q, hq⟩, rfl⟩ f (f q) hbound hvalue hstrict
  rw [hselected, convexHull_singleton, hrange] at heq
  rw [heq]
  exact ContinuousLinearMap.toExposed.isExposed

private theorem finset_hull_subset (s : Finset E) {Q : Set E} (hQ : Convex ℝ Q)
    (hvertex : ∀ q, IsExposed ℝ (convexHull ℝ (s : Set E)) {q} → q ∈ Q) :
    convexHull ℝ (s : Set E) ⊆ Q := by
  classical
  by_cases hs : s = ∅
  · subst s
    simpa only [Finset.coe_empty, convexHull_empty] using Set.empty_subset Q
  let C := s.powerset.filter (fun t : Finset E =>
    convexHull ℝ (t : Set E) = convexHull ℝ (s : Set E))
  have hC : s ∈ C := by simp [C]
  obtain ⟨t, ht, hmin⟩ := C.exists_min_image Finset.card ⟨s, hC⟩
  have htsub : t ⊆ s := Finset.mem_powerset.mp (Finset.mem_filter.mp ht).1
  have hthull : convexHull ℝ (t : Set E) = convexHull ℝ (s : Set E) :=
    (Finset.mem_filter.mp ht).2
  have hnecessary (q : E) (hq : q ∈ t) : q ∉ convexHull ℝ (t.erase q : Set E) := by
    intro hqHull
    have hred : convexHull ℝ (t.erase q : Set E) = convexHull ℝ (t : Set E) := by
      apply Set.Subset.antisymm (convexHull_mono (by
        intro x hx
        exact Finset.mem_of_mem_erase hx))
      apply convexHull_min _ (convex_convexHull ℝ _)
      intro x hx
      by_cases hxq : x = q
      · simpa only [hxq] using hqHull
      · exact subset_convexHull ℝ _ (Finset.mem_erase.mpr ⟨hxq, hx⟩)
    have heC : t.erase q ∈ C := Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr (by
        intro x hx
        exact htsub (Finset.mem_of_mem_erase hx)), hred.trans hthull⟩
    exact Nat.not_le_of_lt (Finset.card_erase_lt_of_mem hq) (hmin _ heC)
  rw [← hthull]
  apply convexHull_min _ hQ
  intro q hq
  apply hvertex
  rw [← hthull]
  exact exposed_of_irredundant t q hq (hnecessary q hq)

/-- A finite hull lies in a convex set containing all its singleton exposed faces. -/
theorem finite_hull_subset_of_vertices {I : Type u} [Fintype I] (w : I → E)
    {Q : Set E} (hQ : Convex ℝ Q)
    (hvertex : ∀ q, IsExposed ℝ (convexHull ℝ (Set.range w)) {q} → q ∈ Q) :
    convexHull ℝ (Set.range w) ⊆ Q := by
  classical
  let s := Finset.univ.image w
  have hs : (s : Set E) = Set.range w := by simp [s]
  rw [← hs]
  exact finset_hull_subset s hQ (fun q hq => hvertex q (by simpa only [hs] using hq))

end Vertices

end GroupActions
end
