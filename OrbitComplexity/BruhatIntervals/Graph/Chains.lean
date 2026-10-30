import OrbitComplexity.BruhatIntervals.Graph.Recursion
import OrbitComplexity.BruhatIntervals.Graph.ChainLabels
import OrbitComplexity.BruhatIntervals.Order.Chains
import Mathlib.Data.List.Chain

/-!
# Saturated chains and interval label spans

Interval label spans split at every top cover. The consecutive labels of a saturated chain,
and the cover labels incident to any interval vertex, give the same span.

## Main results

* `labelSpan_properties`: top-cover, saturated-chain, and incident-cover descriptions of the span.
* `labelSpan_split`: splitting an interval at a vertex adds its two subinterval spans.

## References

* A. Björner and F. Brenti, *Combinatorics of Coxeter Groups*, Springer GTM 231 (2005),
  Sections 2.2 and 2.7.
-/

namespace BruhatIntervals

variable {Index W V : Type*} [Group W] {matrix : CoxeterMatrix Index}
  {cs : CoxeterSystem matrix W} [AddCommGroup V] [Module ℝ V]
  (realization : Realization cs (V := V))

private theorem reflection_label (x y : W) (h : (bruhatGraph cs).Adj x y) :
    (realization.rootReflection
      ⟨edgeLabel realization x y h, edgeLabel_positive realization x y h⟩).val = y * x⁻¹ := by
  have heq := congrArg (· * x⁻¹) (edgeLabel_target realization x y h)
  simpa only [mul_inv_cancel_right] using heq.symm

private theorem diamond_span {z x x' y : W}
    (hzx : (bruhatGraph cs).Adj z x) (hzx' : (bruhatGraph cs).Adj z x')
    (hxy : (bruhatGraph cs).Adj x y) (hx'y : (bruhatGraph cs).Adj x' y) (hzy : z ≠ y) :
    Submodule.span ℝ ({edgeLabel realization x y hxy, edgeLabel realization z x hzx} : Set V) =
      Submodule.span ℝ
        ({edgeLabel realization x' y hx'y, edgeLabel realization z x' hzx'} : Set V) := by
  let α : {root : V // root ∈ realization.positiveRoots} :=
    ⟨edgeLabel realization x y hxy, edgeLabel_positive realization x y hxy⟩
  let β : {root : V // root ∈ realization.positiveRoots} :=
    ⟨edgeLabel realization z x hzx, edgeLabel_positive realization z x hzx⟩
  let γ : {root : V // root ∈ realization.positiveRoots} :=
    ⟨edgeLabel realization x' y hx'y, edgeLabel_positive realization x' y hx'y⟩
  let τ : {root : V // root ∈ realization.positiveRoots} :=
    ⟨edgeLabel realization z x' hzx', edgeLabel_positive realization z x' hzx'⟩
  have hprod : (realization.rootReflection α).val * (realization.rootReflection β).val =
      (realization.rootReflection γ).val * (realization.rootReflection τ).val := by
    dsimp only [α, β, γ, τ]
    rw [reflection_label, reflection_label, reflection_label, reflection_label]
    group
  have hne : (realization.rootReflection α).val * (realization.rootReflection β).val ≠ 1 := by
    dsimp only [α, β]
    rw [reflection_label, reflection_label]
    intro heq
    have htarget : y * z⁻¹ = 1 := by
      calc
        y * z⁻¹ = y * x⁻¹ * (x * z⁻¹) := by group
        _ = 1 := heq
    exact hzy (mul_inv_eq_one.mp htarget).symm
  exact (realization.rootProduct_span α β γ τ hprod hne).1

private theorem cover_span {u v : W} :
    let : PartialOrder W := cs.bruhatPartialOrder
    u ⋖ v → ∀ h : (bruhatGraph cs).Adj u v,
      labelSpan realization u v = Submodule.span ℝ ({(edgeLabel realization u v h)} : Set V) := by
  let : PartialOrder W := cs.bruhatPartialOrder
  dsimp only
  intro hcover h
  have hlength := ((bruhat_covBy_iff cs u v).mp hcover).2
  rw [(labelSpan_eq_covers realization u v hcover.le).2.1]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro α ⟨x, hx, hux, hlenx, rfl⟩
    have hxv : x = v := by
      by_contra hne
      have hlt := hx.2.length_lt_of_ne hne
      omega
    subst x
    exact Submodule.subset_span rfl
  · apply Submodule.span_le.mpr
    rintro α rfl
    exact Submodule.subset_span
      ⟨v, ⟨hcover.le, Relation.ReflTransGen.refl⟩, h, hlength, rfl⟩


private theorem top_cover_span (u v w : W) (huw : cs.BruhatLE u w) :
    let : PartialOrder W := cs.bruhatPartialOrder
    w ⋖ v → ∀ h : (bruhatGraph cs).Adj w v,
      labelSpan realization u v =
        labelSpan realization u w ⊔ Submodule.span ℝ ({(edgeLabel realization w v h)} : Set V) := by
  let : PartialOrder W := cs.bruhatPartialOrder
  dsimp only
  intro hcover hadj
  suffices aux : ∀ n m : ℕ, ∀ u v w : W, cs.length v - cs.length u = n →
      cs.length u = m → cs.BruhatLE u w → w ⋖ v →
      ∀ h : (bruhatGraph cs).Adj w v,
        labelSpan realization u v = labelSpan realization u w ⊔
          Submodule.span ℝ ({(edgeLabel realization w v h)} : Set V) by
    exact aux (cs.length v - cs.length u) (cs.length u) u v w rfl rfl huw hcover hadj
  intro n
  induction n using Nat.strong_induction_on with
  | h n ihGap =>
    intro m
    induction m using Nat.strong_induction_on with
    | h m ihLower =>
      intro u v w hgap hlenU huw hcover hadj
      have huv : cs.BruhatLE u v := huw.trans hcover.le
      have hcoverlen := ((bruhat_covBy_iff cs w v).mp hcover).2
      by_cases heq : u = w
      · subst w
        rw [labelSpan_self, bot_sup_eq]
        exact cover_span realization hcover hadj
      have regular : ∀ w : W, cs.BruhatLE u w → w ⋖ v →
          ∀ h : (bruhatGraph cs).Adj w v, ∀ i : Index, cs.IsRightDescent v i →
          v * cs.simple i ≠ w →
          labelSpan realization u v = labelSpan realization u w ⊔
            Submodule.span ℝ ({(edgeLabel realization w v h)} : Set V) := by
        intro w huw hcover hadj i hv hne
        have hvlen := cs.isRightDescent_iff.mp hv
        have hsimple : v * cs.simple i ⋖ v := (bruhat_covBy_iff cs _ _).mpr
          ⟨(cs.bruhatStep_mul_simple_of_isRightDescent i hv).bruhatLE, hvlen.symm⟩
        let t := w * v⁻¹
        have ht : cs.IsReflection t := (bruhatGraph cs).adj_symm hadj
        have htarget : t * v = w := by dsimp only [t]; group
        have hdiamond : w * cs.simple i ⋖ v * cs.simple i ∧ w * cs.simple i ⋖ w := by
          have h := (strong_weak_diamond cs v t i ht).1 hsimple
            (htarget.symm ▸ hcover) (htarget.symm ▸ hne)
          simpa only [htarget] using h
        have hwdesc : cs.IsRightDescent w i :=
          cs.isRightDescent_iff.mpr ((bruhat_covBy_iff cs _ _).mp hdiamond.2).2.symm
        have hshift := (bruhatStep_iff_adj.mp (bruhat_covBy_step cs hdiamond.1)).1
        by_cases hu : cs.IsRightDescent u i
        · have hulen := cs.isRightDescent_iff.mp hu
          have hlow := (bruhatLE_descent_iff cs i hu hwdesc).mp huw
          have hih := ihLower (cs.length (u * cs.simple i)) (by omega)
            (u * cs.simple i) (v * cs.simple i) (w * cs.simple i) (by omega) rfl
            hlow hdiamond.1 hshift
          have hrec := (labelSpan_recursion realization u v huv i hv).1 hu
          have hrecw := (labelSpan_recursion realization u w huw i hwdesc).1 hu
          calc
            labelSpan realization u v =
                labelSpan realization (u * cs.simple i) (v * cs.simple i) := hrec
            _ = labelSpan realization (u * cs.simple i) (w * cs.simple i) ⊔
                (ℝ ∙ edgeLabel realization (w * cs.simple i) (v * cs.simple i) hshift) := hih
            _ = labelSpan realization u w ⊔ (ℝ ∙ edgeLabel realization w v hadj) := by
              rw [← hrecw, edgeLabel_mul_right realization w v hadj (cs.simple i)]
        · have hulen := cs.not_isRightDescent_iff.mp hu
          have hlow := bruhatLE_mul_of_ascent cs huw i hu
          have htop := bruhatLE_mul_of_ascent cs huv i hu
          have hih := ihGap (cs.length (v * cs.simple i) - cs.length u) (by
            have := htop.length_le
            omega) (cs.length u) u (v * cs.simple i) (w * cs.simple i) rfl rfl
            hlow hdiamond.1 hshift
          have hrec := (labelSpan_recursion realization u v huv i hv).2 hu
          have hrecw := (labelSpan_recursion realization u w huw i hwdesc).2 hu
          calc
            labelSpan realization u v =
                (labelSpan realization u (w * cs.simple i) ⊔
                  (ℝ ∙ edgeLabel realization (w * cs.simple i) (v * cs.simple i) hshift)) ⊔
                  (ℝ ∙ edgeLabel realization u (u * cs.simple i)
                    ((cs.isReflection_simple i).conj u)) := by rw [hrec, hih]
            _ = (labelSpan realization u (w * cs.simple i) ⊔
                  (ℝ ∙ edgeLabel realization u (u * cs.simple i)
                    ((cs.isReflection_simple i).conj u))) ⊔
                  (ℝ ∙ edgeLabel realization w v hadj) := by
              rw [edgeLabel_mul_right realization w v hadj (cs.simple i)]
              ac_rfl
            _ = labelSpan realization u w ⊔ (ℝ ∙ edgeLabel realization w v hadj) := by
              rw [← hrecw]
      by_cases hav : ∃ i : Index, cs.IsRightDescent v i ∧ v * cs.simple i ≠ w
      · obtain ⟨i, hi, hne⟩ := hav
        exact regular w huw hcover hadj i hi hne
      have hvne : v ≠ 1 := by
        intro heq
        have hlt := (bruhat_covBy_step cs hcover).length_lt
        rw [heq, cs.length_one] at hlt
        omega
      obtain ⟨i, hi⟩ := cs.exists_rightDescent_of_ne_one hvne
      have hsimple : v * cs.simple i = w := by
        by_contra hne
        exact hav ⟨i, hi, hne⟩
      obtain ⟨z, huz, hcovzw⟩ := exists_le_bruhat_covBy cs huw heq
      obtain ⟨w', ⟨hne, hcovzw', hcovw'v⟩, _⟩ :=
        bruhat_rank_two_diamond cs z w v hcovzw hcover
      have huw' : cs.BruhatLE u w' := huz.trans hcovzw'.le
      have hzw := (bruhatStep_iff_adj.mp (bruhat_covBy_step cs hcovzw)).1
      have hzw' := (bruhatStep_iff_adj.mp (bruhat_covBy_step cs hcovzw')).1
      have hw'v := (bruhatStep_iff_adj.mp (bruhat_covBy_step cs hcovw'v)).1
      have hfirst := regular w' huw' hcovw'v hw'v i hi (by rwa [hsimple, ne_eq, eq_comm])
      have hlenw' := ((bruhat_covBy_iff cs w' v).mp hcovw'v).2
      have hsecond := ihGap (cs.length w' - cs.length u) (by
        have := huw'.length_le
        omega) (cs.length u) u w' z rfl rfl huz hcovzw' hzw'
      have hthird := ihGap (cs.length w - cs.length u) (by
        have := huw.length_le
        omega) (cs.length u) u w z rfl rfl huz hcovzw hzw
      have hzyne : z ≠ v := by
        intro heq
        have hlt := (bruhat_covBy_step cs hcovzw).length_lt.trans
          (bruhat_covBy_step cs hcover).length_lt
        rw [heq] at hlt
        exact Nat.lt_irrefl _ hlt
      have hplanes := diamond_span realization hzw hzw' hadj hw'v hzyne
      rw [Submodule.span_insert, Submodule.span_insert] at hplanes
      calc
        labelSpan realization u v =
            (labelSpan realization u z ⊔ (ℝ ∙ edgeLabel realization z w' hzw')) ⊔
              (ℝ ∙ edgeLabel realization w' v hw'v) := by rw [hfirst, hsecond]
        _ = labelSpan realization u z ⊔
            ((ℝ ∙ edgeLabel realization w' v hw'v) ⊔
              (ℝ ∙ edgeLabel realization z w' hzw')) := by ac_rfl
        _ = labelSpan realization u z ⊔
            ((ℝ ∙ edgeLabel realization w v hadj) ⊔
              (ℝ ∙ edgeLabel realization z w hzw)) := by rw [hplanes]
        _ = (labelSpan realization u z ⊔ (ℝ ∙ edgeLabel realization z w hzw)) ⊔
            (ℝ ∙ edgeLabel realization w v hadj) := by ac_rfl
        _ = labelSpan realization u w ⊔ (ℝ ∙ edgeLabel realization w v hadj) := by rw [← hthird]


private theorem chain_compare (vertices : List W) (u v : W)
    (hhead : vertices.head? = some u) (hlast : vertices.getLast? = some v)
    (hchain : vertices.IsChain
      (fun x y => cs.BruhatLE x y ∧ cs.length y = cs.length x + 1)) : cs.BruhatLE u v := by
  induction vertices generalizing u v with
  | nil => simp at hhead
  | cons first rest ih =>
    cases rest with
    | nil =>
      have hfirst : first = u := Option.some.inj hhead
      have hfinal : first = v := Option.some.inj hlast
      rw [← hfirst, ← hfinal]
    | cons second rest =>
      have hfirst : first = u := Option.some.inj hhead
      subst first
      have hrel := List.isChain_cons_cons.mp hchain
      exact hrel.1.1.trans
        (ih second v rfl (by simpa only [List.getLast?_cons_cons] using hlast) hrel.2)

private theorem chain_span (vertices : List W) (u v : W)
    (hhead : vertices.head? = some u) (hlast : vertices.getLast? = some v)
    (hchain : vertices.IsChain
      (fun x y => cs.BruhatLE x y ∧ cs.length y = cs.length x + 1)) :
    labelSpan realization u v = chainLabelSpan realization vertices := by
  let : PartialOrder W := cs.bruhatPartialOrder
  induction vertices using List.reverseRecOn generalizing u v with
  | nil => simp at hhead
  | append_singleton vertices last ih =>
    have hfinal : last = v := by simpa [List.getLast?_append] using hlast
    subst last
    by_cases hnil : vertices = []
    · subst vertices
      have hvu : v = u := Option.some.inj hhead
      subst v
      simpa only [List.nil_append, chainLabelSpan_singleton] using labelSpan_self realization u
    · let w := vertices.getLast hnil
      have hlast' : vertices.getLast? = some w := List.getLast?_eq_getLast_of_ne_nil hnil
      have hhead' : vertices.head? = some u := by
        rw [List.head?_append_of_ne_nil vertices hnil] at hhead
        exact hhead
      have hchain' := hchain.left_of_append
      have hrel : cs.BruhatLE w v ∧ cs.length v = cs.length w + 1 :=
        (List.isChain_append.mp hchain).2.2 w (by simp [hlast']) v (by simp)
      have huw := chain_compare vertices u w hhead' hlast' hchain'
      have hcov : w ⋖ v := (bruhat_covBy_iff cs w v).mpr hrel
      have hadj := (bruhatStep_iff_adj.mp (bruhat_covBy_step cs hcov)).1
      calc
        labelSpan realization u v =
            labelSpan realization u w ⊔ (ℝ ∙ edgeLabel realization w v hadj) :=
          top_cover_span realization u v w huw hcov hadj
        _ = chainLabelSpan realization vertices ⊔ (ℝ ∙ edgeLabel realization w v hadj) := by
          rw [ih u w hhead' hlast' hchain']
        _ = chainLabelSpan realization (vertices ++ [v]) :=
          (chainLabelSpan_snoc realization vertices w v hlast' hadj).symm


/-- Splitting a Bruhat interval at one of its vertices adds the label spans of the subintervals. -/
theorem labelSpan_split (u w v : W) (huw : cs.BruhatLE u w) (hwv : cs.BruhatLE w v) :
    labelSpan realization u v = labelSpan realization u w ⊔ labelSpan realization w v := by
  obtain ⟨first, hfirsthead, hfirstlast, hfirstchain, _⟩ := exists_bruhat_chain cs u w huw
  obtain ⟨second, hsecondhead, hsecondlast, hsecondchain, _⟩ := exists_bruhat_chain cs w v hwv
  let initial := first.dropLast
  let final := second.tail
  have hfirsteq : initial ++ [w] = first :=
    List.dropLast_append_getLast? w (by simp [hfirstlast])
  have hsecondeq : w :: final = second := List.cons_head?_tail (by simp [hsecondhead])
  have hfirsthead' : (initial ++ [w]).head? = some u := by rw [hfirsteq]; exact hfirsthead
  have hfirstlast' : (initial ++ [w]).getLast? = some w := by rw [hfirsteq]; exact hfirstlast
  have hsecondhead' : (w :: final).head? = some w := rfl
  have hsecondlast' : (w :: final).getLast? = some v := by rw [hsecondeq]; exact hsecondlast
  have hchainfirst : (initial ++ [w]).IsChain
      (fun x y => cs.BruhatLE x y ∧ cs.length y = cs.length x + 1) := by
    rw [hfirsteq]
    exact hfirstchain
  have hchainsecond : (w :: final).IsChain
      (fun x y => cs.BruhatLE x y ∧ cs.length y = cs.length x + 1) := by
    rw [hsecondeq]
    exact hsecondchain
  have hhead : (initial ++ w :: final).head? = some u := by
    cases hinitial : initial with
    | nil => simpa only [hinitial, List.nil_append, List.head?_cons] using hfirsthead'
    | cons a rest =>
      simpa only [hinitial, List.cons_append, List.head?_cons] using hfirsthead'
  have hlast : (initial ++ w :: final).getLast? = some v := by
    rw [List.getLast?_append_of_ne_nil initial (by simp)]
    exact hsecondlast'
  have hchain : (initial ++ w :: final).IsChain
      (fun x y => cs.BruhatLE x y ∧ cs.length y = cs.length x + 1) := by
    have h := hchainfirst.append_overlap
      (show ([w] ++ final).IsChain _ from hchainsecond) (by simp)
    simpa only [List.append_assoc, List.cons_append, List.nil_append] using h
  calc
    labelSpan realization u v = chainLabelSpan realization (initial ++ w :: final) :=
      chain_span realization _ u v hhead hlast hchain
    _ = chainLabelSpan realization (initial ++ [w]) ⊔ chainLabelSpan realization (w :: final) :=
      chainLabelSpan_overlap realization initial w final
    _ = labelSpan realization u w ⊔ labelSpan realization w v := by
      rw [← chain_span realization _ u w hfirsthead' hfirstlast' hchainfirst,
        ← chain_span realization _ w v hsecondhead' hsecondlast' hchainsecond]

private theorem incident_span (u v w : W) (hw : w ∈ bruhatInterval cs u v) :
    labelSpan realization u v = Submodule.span ℝ
      {α : V | ∃ x ∈ bruhatInterval cs u v, ∃ h : (bruhatGraph cs).Adj w x,
        (cs.length x = cs.length w + 1 ∨ cs.length w = cs.length x + 1) ∧
          edgeLabel realization w x h = α} := by
  apply le_antisymm
  · rw [labelSpan_split realization u w v hw.1 hw.2]
    apply sup_le
    · rw [(labelSpan_eq_covers realization u w hw.1).2.2]
      apply Submodule.span_le.mpr
      rintro α ⟨x, hx, hxw, hlength, rfl⟩
      exact Submodule.subset_span
        ⟨x, ⟨hx.1, hx.2.trans hw.2⟩, (bruhatGraph cs).adj_symm hxw,
          Or.inr hlength, (edgeLabel_symm realization x w hxw).symm⟩
    · rw [(labelSpan_eq_covers realization w v hw.2).2.1]
      apply Submodule.span_le.mpr
      rintro α ⟨x, hx, hwx, hlength, rfl⟩
      exact Submodule.subset_span
        ⟨x, ⟨hw.1.trans hx.1, hx.2⟩, hwx, Or.inl hlength, rfl⟩
  · apply Submodule.span_le.mpr
    rintro α ⟨x, hx, hwx, _, rfl⟩
    exact Submodule.subset_span ⟨w, hw, x, hx, hwx, rfl⟩

/-- Top-cover splitting, every saturated-chain span, and every incident-cover span describe the
same label space of a Bruhat interval. -/
theorem labelSpan_properties (u v : W) (_huv : cs.BruhatLE u v) :
    (∀ w ∈ bruhatInterval cs u v, ∀ h : (bruhatGraph cs).Adj w v,
      cs.length v = cs.length w + 1 →
        labelSpan realization u v = labelSpan realization u w ⊔
          Submodule.span ℝ ({(edgeLabel realization w v h)} : Set V)) ∧
    (∀ vertices : List W,
      vertices.head? = some u → vertices.getLast? = some v →
      vertices.IsChain (fun x y => cs.BruhatLE x y ∧ cs.length y = cs.length x + 1) →
      labelSpan realization u v = Submodule.span ℝ
        {α : V | ∃ x y : W, (x, y) ∈ vertices.zip vertices.tail ∧
          ∃ h : (bruhatGraph cs).Adj x y, edgeLabel realization x y h = α}) ∧
    (∀ w ∈ bruhatInterval cs u v, labelSpan realization u v = Submodule.span ℝ
      {α : V | ∃ x ∈ bruhatInterval cs u v, ∃ h : (bruhatGraph cs).Adj w x,
        (cs.length x = cs.length w + 1 ∨ cs.length w = cs.length x + 1) ∧
          edgeLabel realization w x h = α}) := by
  let : PartialOrder W := cs.bruhatPartialOrder
  refine ⟨?_, ?_, ?_⟩
  · intro w hw h hlength
    have hstep := bruhatStep_iff_adj.mpr ⟨h, by omega⟩
    exact top_cover_span realization u v w hw.1
      ((bruhat_covBy_iff cs w v).mpr ⟨hstep.bruhatLE, hlength⟩) h
  · intro vertices hhead hlast hchain
    exact chain_span realization vertices u v hhead hlast hchain
  · intro w hw
    exact incident_span realization u v w hw

end BruhatIntervals

