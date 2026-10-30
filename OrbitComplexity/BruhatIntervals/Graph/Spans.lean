import OrbitComplexity.BruhatIntervals.Graph.Basic
import OrbitComplexity.BruhatIntervals.Graph.LongEdges
import OrbitComplexity.BruhatIntervals.Order.Covers

/-!
# Spanning interval labels by covers

Every interval edge label belongs to the span of the interval's cover labels. The proof refines
a long edge into three directed edges and uses the two-dimensional reflection-product span.

## Main results

* `labelSpan_eq_all_covers`: interval cover labels span all interval edge labels.
* `edgeLabel_mem_of_diamond`: two labels at one end of a diamond span either label at its other end.

## References

* M. Dyer, *On the Bruhat Graph of a Coxeter System*, Compositio Mathematica 78 (1991), Section 3.
-/

namespace BruhatIntervals

variable {Index W V : Type*} [Group W] {matrix : CoxeterMatrix Index}
  {cs : CoxeterSystem matrix W} [AddCommGroup V] [Module ℝ V]
  (realization : Realization cs (V := V))

private theorem label_reflection (x y : W) (h : (bruhatGraph cs).Adj x y) :
    (realization.rootReflection
      ⟨edgeLabel realization x y h, edgeLabel_positive realization x y h⟩).val = y * x⁻¹ := by
  have htarget := edgeLabel_target realization x y h
  have hright := congrArg (· * x⁻¹) htarget
  simpa only [mul_inv_cancel_right] using hright.symm

private theorem long_label_mem {x a b y : W} (hxy : (bruhatGraph cs).Adj x y)
    (hfirst : cs.BruhatStep x a) (hmiddle : cs.BruhatStep a b)
    (hlast : cs.BruhatStep b y) (plane : Submodule ℝ V)
    (hfirst_mem : edgeLabel realization x a (bruhatStep_iff_adj.mp hfirst).1 ∈ plane)
    (hmiddle_mem : edgeLabel realization a b (bruhatStep_iff_adj.mp hmiddle).1 ∈ plane) :
    edgeLabel realization x y hxy ∈ plane := by
  let hp := (bruhatStep_iff_adj.mp hfirst).1
  let hq := (bruhatStep_iff_adj.mp hmiddle).1
  let hr := (bruhatStep_iff_adj.mp hlast).1
  let α : {root : V // root ∈ realization.positiveRoots} :=
    ⟨edgeLabel realization x y hxy, edgeLabel_positive realization x y hxy⟩
  let β : {root : V // root ∈ realization.positiveRoots} :=
    ⟨edgeLabel realization x a hp, edgeLabel_positive realization x a hp⟩
  let γ : {root : V // root ∈ realization.positiveRoots} :=
    ⟨edgeLabel realization b y hr, edgeLabel_positive realization b y hr⟩
  let τ : {root : V // root ∈ realization.positiveRoots} :=
    ⟨edgeLabel realization a b hq, edgeLabel_positive realization a b hq⟩
  have hp_twice : a * x⁻¹ * a = x := by
    have hself := hp.mul_self
    change (a * x⁻¹) * (a * x⁻¹) = 1 at hself
    have hright := congrArg (· * x) hself
    simpa only [mul_assoc, inv_mul_cancel, mul_one, one_mul] using hright
  have hprod : (realization.rootReflection α).val * (realization.rootReflection β).val =
      (realization.rootReflection γ).val * (realization.rootReflection τ).val := by
    dsimp only [α, β, γ, τ]
    rw [label_reflection, label_reflection, label_reflection, label_reflection]
    calc
      y * x⁻¹ * (a * x⁻¹) = y * (a⁻¹ * (a * x⁻¹ * a)) * x⁻¹ := by group
      _ = y * b⁻¹ * (b * a⁻¹) := by rw [hp_twice]; group
  have hne : (realization.rootReflection α).val * (realization.rootReflection β).val ≠ 1 := by
    dsimp only [α, β]
    rw [label_reflection, label_reflection]
    intro heq
    have hp_self := hp.mul_self
    change (a * x⁻¹) * (a * x⁻¹) = 1 at hp_self
    have heq' : y * x⁻¹ = a * x⁻¹ := mul_right_cancel (heq.trans hp_self.symm)
    have hya : y = a := mul_right_cancel heq'
    have hlt := hmiddle.length_lt.trans hlast.length_lt
    rw [hya] at hlt
    exact Nat.lt_irrefl _ hlt
  obtain ⟨hspan, hdim⟩ := realization.rootProduct_span α β γ τ hprod hne
  have hdistinct : β ≠ τ := by
    intro heq
    have href := congrArg (fun root => (realization.rootReflection root).val) heq
    change (realization.rootReflection
      ⟨edgeLabel realization x a hp, edgeLabel_positive realization x a hp⟩).val =
        (realization.rootReflection
          ⟨edgeLabel realization a b hq, edgeLabel_positive realization a b hq⟩).val at href
    rw [label_reflection, label_reflection] at href
    have hbx : b = x := by
      calc
        b = (b * a⁻¹) * a := by group
        _ = (a * x⁻¹) * a := by rw [← href]
        _ = x := hp_twice
    have hlt := hfirst.length_lt.trans hmiddle.length_lt
    rw [hbx] at hlt
    exact Nat.lt_irrefl _ hlt
  have hle : Submodule.span ℝ ({β.val, τ.val} : Set V) ≤
      Submodule.span ℝ ({α.val, β.val} : Set V) := by
    apply Submodule.span_le.mpr
    rintro root (rfl | rfl)
    · exact Submodule.subset_span (Or.inr rfl)
    · rw [hspan]
      exact Submodule.subset_span (Or.inr rfl)
  have : FiniteDimensional ℝ (Submodule.span ℝ ({α.val, β.val} : Set V)) :=
    FiniteDimensional.span_of_finite ℝ (Set.toFinite _)
  have heq := Submodule.eq_of_le_of_finrank_eq hle
    ((realization.positiveRoots_pair_finrank β τ hdistinct).trans hdim.symm)
  have hα : α.val ∈ Submodule.span ℝ ({β.val, τ.val} : Set V) := by
    rw [heq]
    exact Submodule.subset_span (Or.inl rfl)
  apply Submodule.span_le.mpr ?_ hα
  rintro root (rfl | rfl)
  · exact hfirst_mem
  · exact hmiddle_mem

/-- Two distinct labels at one end of a four-edge diamond span either label at its other end. -/
theorem edgeLabel_mem_of_diamond {z x x' y : W}
    (hzx : (bruhatGraph cs).Adj z x) (hzx' : (bruhatGraph cs).Adj z x')
    (hxy : (bruhatGraph cs).Adj x y) (hx'y : (bruhatGraph cs).Adj x' y)
    (hxx' : x ≠ x') (hzy : z ≠ y) (plane : Submodule ℝ V)
    (hfirst : edgeLabel realization z x hzx ∈ plane)
    (hsecond : edgeLabel realization z x' hzx' ∈ plane) :
    edgeLabel realization x y hxy ∈ plane := by
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
    rw [label_reflection, label_reflection, label_reflection, label_reflection]
    group
  have hne : (realization.rootReflection α).val * (realization.rootReflection β).val ≠ 1 := by
    dsimp only [α, β]
    rw [label_reflection, label_reflection]
    intro heq
    have hyz : y * z⁻¹ = 1 := by
      calc
        y * z⁻¹ = y * x⁻¹ * (x * z⁻¹) := by group
        _ = 1 := heq
    exact hzy (mul_inv_eq_one.mp hyz).symm
  obtain ⟨hspan, hdim⟩ := realization.rootProduct_span α β γ τ hprod hne
  have hdistinct : β ≠ τ := by
    intro heq
    apply hxx'
    have href := congrArg (fun root => (realization.rootReflection root).val) heq
    change (realization.rootReflection
      ⟨edgeLabel realization z x hzx, edgeLabel_positive realization z x hzx⟩).val =
        (realization.rootReflection
          ⟨edgeLabel realization z x' hzx', edgeLabel_positive realization z x' hzx'⟩).val at href
    rw [label_reflection, label_reflection] at href
    exact mul_right_cancel href
  have hle : Submodule.span ℝ ({β.val, τ.val} : Set V) ≤
      Submodule.span ℝ ({α.val, β.val} : Set V) := by
    apply Submodule.span_le.mpr
    rintro root (rfl | rfl)
    · exact Submodule.subset_span (Or.inr rfl)
    · rw [hspan]
      exact Submodule.subset_span (Or.inr rfl)
  have : FiniteDimensional ℝ (Submodule.span ℝ ({α.val, β.val} : Set V)) :=
    FiniteDimensional.span_of_finite ℝ (Set.toFinite _)
  have heq := Submodule.eq_of_le_of_finrank_eq hle
    ((realization.positiveRoots_pair_finrank β τ hdistinct).trans hdim.symm)
  have hα : α.val ∈ Submodule.span ℝ ({β.val, τ.val} : Set V) := by
    rw [heq]
    exact Submodule.subset_span (Or.inl rfl)
  apply Submodule.span_le.mpr ?_ hα
  rintro root (rfl | rfl)
  · exact hfirst
  · exact hsecond

private theorem edgeLabel_mem_of_covers (u v : W) (plane : Submodule ℝ V)
    (hcover : ∀ x ∈ bruhatInterval cs u v, ∀ y ∈ bruhatInterval cs u v,
      ∀ h : (bruhatGraph cs).Adj x y, cs.length y = cs.length x + 1 →
        edgeLabel realization x y h ∈ plane) :
    ∀ x y : W, cs.BruhatLE u x → cs.BruhatLE y v → cs.BruhatStep x y →
      ∀ h : (bruhatGraph cs).Adj x y, edgeLabel realization x y h ∈ plane := by
  suffices aux : ∀ n : ℕ, ∀ x y : W, cs.length y - cs.length x = n →
      cs.BruhatLE u x → cs.BruhatLE y v → cs.BruhatStep x y →
      ∀ h : (bruhatGraph cs).Adj x y, edgeLabel realization x y h ∈ plane by
    intro x y hux hyv hstep h
    exact aux (cs.length y - cs.length x) x y rfl hux hyv hstep h
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro x y hgap hux hyv hstep h
    have hxy := hstep.bruhatLE
    have hlt := hstep.length_lt
    by_cases hunit : cs.length y = cs.length x + 1
    · exact hcover x ⟨hux, hxy.trans hyv⟩ y ⟨hux.trans hxy, hyv⟩ h hunit
    · obtain ⟨a, b, hfirst, hmiddle, hlast, _⟩ :=
        long_edge_path cs x y hstep (by omega)
      have hxa := hfirst.length_lt
      have hab := hmiddle.length_lt
      have hby := hlast.length_lt
      apply long_label_mem realization h hfirst hmiddle hlast plane
      · exact ih (cs.length a - cs.length x) (by omega) x a rfl
          hux (hmiddle.bruhatLE.trans (hlast.bruhatLE.trans hyv)) hfirst _
      · exact ih (cs.length b - cs.length a) (by omega) a b rfl
          (hux.trans hfirst.bruhatLE) (hlast.bruhatLE.trans hyv) hmiddle _

/-- All edge labels of a Bruhat interval are spanned by its cover labels. -/
theorem labelSpan_eq_all_covers (u v : W) :
    labelSpan realization u v = Submodule.span ℝ
      {α : V | ∃ x ∈ bruhatInterval cs u v, ∃ y ∈ bruhatInterval cs u v,
        ∃ h : (bruhatGraph cs).Adj x y, cs.length y = cs.length x + 1 ∧
          edgeLabel realization x y h = α} := by
  rw [labelSpan_eq_ordered]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro α ⟨x, y, hux, hyv, hxy, hlt, rfl⟩
    refine edgeLabel_mem_of_covers realization u v _ ?_ x y hux hyv
      (bruhatStep_iff_adj.mpr ⟨hxy, hlt⟩) hxy
    intro a ha b hb hab hlength
    exact Submodule.subset_span ⟨a, ha, b, hb, hab, hlength, rfl⟩
  · apply Submodule.span_le.mpr
    rintro α ⟨x, hx, y, hy, hxy, hlength, rfl⟩
    exact Submodule.subset_span ⟨x, y, hx.1, hy.2, hxy, by omega, rfl⟩

end BruhatIntervals

