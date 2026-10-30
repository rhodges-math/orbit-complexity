import OrbitComplexity.BruhatIntervals.Graph.CoverSpans
import OrbitComplexity.BruhatIntervals.Graph.Diamonds
import OrbitComplexity.BruhatIntervals.Graph.Labels

/-!
# The right-descent recurrence for interval label spans

The label span satisfies a two-case recurrence at a right descent of the upper endpoint.
The proof uses covers incident to the endpoints and strong/weak Bruhat diamonds.

## Main results

* `labelSpan_recursion`: the common-descent and lower-ascent cases of the label-span recurrence.

## References

* A. Björner and F. Brenti, *Combinatorics of Coxeter Groups*, Springer GTM 231 (2005),
  Section 2.2.
-/

namespace BruhatIntervals

variable {Index W V : Type*} [Group W] {matrix : CoxeterMatrix Index}
  {cs : CoxeterSystem matrix W} [AddCommGroup V] [Module ℝ V]
  (realization : Realization cs (V := V))

private theorem descent_cover (w : W) (i : Index) (hw : cs.IsRightDescent w i) :
    let : PartialOrder W := cs.bruhatPartialOrder
    w * cs.simple i ⋖ w := by
  let : PartialOrder W := cs.bruhatPartialOrder
  apply (bruhat_covBy_iff cs _ _).mpr
  exact ⟨(cs.bruhatStep_mul_simple_of_isRightDescent i hw).bruhatLE,
    (cs.isRightDescent_iff.mp hw).symm⟩

private theorem ascent_cover (w : W) (i : Index) (hw : ¬ cs.IsRightDescent w i) :
    let : PartialOrder W := cs.bruhatPartialOrder
    w ⋖ w * cs.simple i := by
  let : PartialOrder W := cs.bruhatPartialOrder
  apply (bruhat_covBy_iff cs _ _).mpr
  have hlength := cs.not_isRightDescent_iff.mp hw
  exact ⟨(cs.bruhatStep_mul_simple i (by omega)).bruhatLE, hlength⟩

private theorem downward_diamond {x y : W} (i : Index) :
    let : PartialOrder W := cs.bruhatPartialOrder
    x ⋖ y → cs.IsRightDescent y i → x ≠ y * cs.simple i →
      x * cs.simple i ⋖ y * cs.simple i ∧ x * cs.simple i ⋖ x := by
  let : PartialOrder W := cs.bruhatPartialOrder
  dsimp only
  intro hcover hy hne
  let t := x * y⁻¹
  have htarget : t * y = x := by dsimp only [t]; group
  have ht : cs.IsReflection t :=
    (bruhatGraph cs).adj_symm (bruhatStep_iff_adj.mp (bruhat_covBy_step cs hcover)).1
  have href : t * y ⋖ y := htarget.symm ▸ hcover
  have hne' : y * cs.simple i ≠ t * y := htarget.symm ▸ Ne.symm hne
  have h := (strong_weak_diamond cs y t i ht).1 (descent_cover y i hy) href hne'
  simpa only [htarget] using h

private theorem upward_diamond {x y : W} (i : Index) :
    let : PartialOrder W := cs.bruhatPartialOrder
    x ⋖ y → ¬ cs.IsRightDescent x i → y ≠ x * cs.simple i →
      x * cs.simple i ⋖ y * cs.simple i ∧ y ⋖ y * cs.simple i := by
  let : PartialOrder W := cs.bruhatPartialOrder
  dsimp only
  intro hcover hx hne
  let t := y * x⁻¹
  have htarget : t * x = y := by dsimp only [t]; group
  have ht : cs.IsReflection t := (bruhatStep_iff_adj.mp (bruhat_covBy_step cs hcover)).1
  have href : x ⋖ t * x := htarget.symm ▸ hcover
  have hne' : x * cs.simple i ≠ t * x := htarget.symm ▸ Ne.symm hne
  have h := (strong_weak_diamond cs x t i ht).2 (ascent_cover x i hx) href hne'
  simpa only [htarget] using h


private theorem descent_of_cover {w : W} (i : Index) :
    let : PartialOrder W := cs.bruhatPartialOrder
    w * cs.simple i ⋖ w → cs.IsRightDescent w i := by
  let : PartialOrder W := cs.bruhatPartialOrder
  dsimp only
  intro h
  exact cs.isRightDescent_iff.mpr ((bruhat_covBy_iff cs _ _).mp h).2.symm

private theorem ascent_of_cover {w : W} (i : Index) :
    let : PartialOrder W := cs.bruhatPartialOrder
    w ⋖ w * cs.simple i → ¬ cs.IsRightDescent w i := by
  let : PartialOrder W := cs.bruhatPartialOrder
  dsimp only
  intro h
  exact cs.not_isRightDescent_iff.mpr ((bruhat_covBy_iff cs _ _).mp h).2

private theorem reverse_diamond_mem {z x x' y : W}
    (hzx : (bruhatGraph cs).Adj z x) (hzx' : (bruhatGraph cs).Adj z x')
    (hxy : (bruhatGraph cs).Adj x y) (hx'y : (bruhatGraph cs).Adj x' y)
    (hxx' : x ≠ x') (hzy : z ≠ y) (plane : Submodule ℝ V)
    (hfirst : edgeLabel realization x y hxy ∈ plane)
    (hsecond : edgeLabel realization x' y hx'y ∈ plane) :
    edgeLabel realization z x hzx ∈ plane := by
  rw [edgeLabel_symm realization z x hzx]
  apply edgeLabel_mem_of_diamond realization
    ((bruhatGraph cs).adj_symm hxy) ((bruhatGraph cs).adj_symm hx'y)
    ((bruhatGraph cs).adj_symm hzx) ((bruhatGraph cs).adj_symm hzx')
    hxx' (Ne.symm hzy) plane
  · rw [← edgeLabel_symm realization x y hxy]
    exact hfirst
  · rw [← edgeLabel_symm realization x' y hx'y]
    exact hsecond

private theorem descent_span (u v : W) (huv : cs.BruhatLE u v) (i : Index)
    (hu : cs.IsRightDescent u i) (hv : cs.IsRightDescent v i) :
    labelSpan realization u v = labelSpan realization (u * cs.simple i) (v * cs.simple i) := by
  let : PartialOrder W := cs.bruhatPartialOrder
  suffices aux : ∀ n : ℕ, ∀ u v : W, cs.length v - cs.length u = n →
      cs.BruhatLE u v → cs.IsRightDescent u i → cs.IsRightDescent v i →
      labelSpan realization u v =
        labelSpan realization (u * cs.simple i) (v * cs.simple i) by
    exact aux (cs.length v - cs.length u) u v rfl huv hu hv
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro u v hgap huv hu hv
    by_cases heq : u = v
    · subst v
      rw [labelSpan_self, labelSpan_self]
    have huv' := (bruhatLE_descent_iff cs i hu hv).mp huv
    have hucover := descent_cover u i hu
    have hvcover := descent_cover v i hv
    have huascent := cs.isRightDescent_iff_not_isRightDescent_mul.mp hu
    have hvascent := cs.isRightDescent_iff_not_isRightDescent_mul.mp hv
    have hune : u ≠ v * cs.simple i := by
      intro h
      exact hvascent (h ▸ hu)
    apply le_antisymm
    · rw [(labelSpan_eq_covers realization u v huv).2.2]
      apply Submodule.span_le.mpr
      rintro α ⟨x, hx, hxv, hlength, rfl⟩
      have hstep := bruhatStep_iff_adj.mpr ⟨hxv, by omega⟩
      have hcover : x ⋖ v := (bruhat_covBy_iff cs x v).mpr ⟨hstep.bruhatLE, hlength⟩
      by_cases hspecial : x = v * cs.simple i
      · subst x
        obtain ⟨z, huz, hcovzx⟩ := exists_le_bruhat_covBy cs hx.1 hune
        obtain ⟨w, ⟨hwne, hcovzw, hcovwv⟩, _⟩ :=
          bruhat_rank_two_diamond cs z (v * cs.simple i) v hcovzx hvcover
        have hdiamond := downward_diamond i hcovwv hv hwne
        have hwdesc := descent_of_cover i hdiamond.2
        have huw : cs.BruhatLE u w := huz.trans hcovzw.le
        have hwlen := ((bruhat_covBy_iff cs w v).mp hcovwv).2
        have hrec := ih (cs.length w - cs.length u) (by
          have hulen := huw.length_le
          omega) u w rfl huw hu hwdesc
        have hzx := (bruhatStep_iff_adj.mp (bruhat_covBy_step cs hcovzx)).1
        have hzw := (bruhatStep_iff_adj.mp (bruhat_covBy_step cs hcovzw)).1
        have hwv := (bruhatStep_iff_adj.mp (bruhat_covBy_step cs hcovwv)).1
        have hzyne : z ≠ v := by
          intro h
          have hlt := (bruhat_covBy_step cs hcovzx).length_lt.trans hstep.length_lt
          rw [h] at hlt
          exact Nat.lt_irrefl _ hlt
        apply edgeLabel_mem_of_diamond realization hzx hzw hxv hwv
          (Ne.symm hwne) hzyne (labelSpan realization (u * cs.simple i) (v * cs.simple i))
        · exact Submodule.subset_span
            ⟨z, ⟨hucover.le.trans huz, hcovzx.le⟩,
              v * cs.simple i, ⟨huv', Relation.ReflTransGen.refl⟩, hzx, rfl⟩
        · have hlabel : edgeLabel realization z w hzw ∈ labelSpan realization u w :=
            Submodule.subset_span
              ⟨z, ⟨huz, hcovzw.le⟩, w, ⟨huw, Relation.ReflTransGen.refl⟩, hzw, rfl⟩
          rw [hrec] at hlabel
          exact labelSpan_mono realization Relation.ReflTransGen.refl hdiamond.1.le hlabel
      · have hdiamond := downward_diamond i hcover hv hspecial
        have hxdesc := descent_of_cover i hdiamond.2
        have hlow := (bruhatLE_descent_iff cs i hu hxdesc).mp hx.1
        rw [← edgeLabel_mul_right realization x v hxv (cs.simple i)]
        exact Submodule.subset_span
          ⟨x * cs.simple i, ⟨hlow, hdiamond.1.le⟩,
            v * cs.simple i, ⟨huv', Relation.ReflTransGen.refl⟩, _, rfl⟩
    · rw [(labelSpan_eq_covers realization (u * cs.simple i) (v * cs.simple i) huv').2.1]
      apply Submodule.span_le.mpr
      rintro α ⟨x, hx, hux, hlength, rfl⟩
      have hstep := bruhatStep_iff_adj.mpr ⟨hux, by omega⟩
      have hcover : u * cs.simple i ⋖ x :=
        (bruhat_covBy_iff cs _ _).mpr ⟨hstep.bruhatLE, hlength⟩
      by_cases hspecial : x = u
      · subst x
        obtain ⟨z, hcovuz, hzv⟩ := exists_bruhat_covBy_le cs hx.2 hune
        obtain ⟨w, ⟨hwne, hcovuw, hcovwz⟩, _⟩ :=
          bruhat_rank_two_diamond cs (u * cs.simple i) u z hucover hcovuz
        have hdiamond : u ⋖ w * cs.simple i ∧ w ⋖ w * cs.simple i := by
          simpa only [cs.simple_mul_simple_cancel_right] using
            upward_diamond i hcovuw huascent (by
              simpa only [cs.simple_mul_simple_cancel_right] using hwne)
        have hwascent := ascent_of_cover i hdiamond.2
        have hwsdesc : cs.IsRightDescent (w * cs.simple i) i := by
          apply cs.isRightDescent_iff.mpr
          simpa only [cs.simple_mul_simple_cancel_right] using
            (cs.not_isRightDescent_iff.mp hwascent).symm
        have hw_vs : cs.BruhatLE w (v * cs.simple i) := hcovwz.le.trans hzv
        have hws_v : cs.BruhatLE (w * cs.simple i) v := by
          simpa only [cs.simple_mul_simple_cancel_right] using
            hw_vs.mul_simple_of_not_isRightDescent i hvascent
        have hwlen := ((bruhat_covBy_iff cs _ _).mp hcovuw).2
        have hulen := cs.isRightDescent_iff.mp hu
        have hwslen := cs.not_isRightDescent_iff.mp hwascent
        have hrec : labelSpan realization (w * cs.simple i) v =
            labelSpan realization w (v * cs.simple i) := by
          simpa only [cs.simple_mul_simple_cancel_right] using
            ih (cs.length v - cs.length (w * cs.simple i)) (by
              have hwvlen := hws_v.length_le
              omega) (w * cs.simple i) v rfl hws_v hwsdesc hv
        have huw := (bruhatStep_iff_adj.mp (bruhat_covBy_step cs hcovuw)).1
        have huz := (bruhatStep_iff_adj.mp (bruhat_covBy_step cs hcovuz)).1
        have hwz := (bruhatStep_iff_adj.mp (bruhat_covBy_step cs hcovwz)).1
        have hlow_ne : u * cs.simple i ≠ z := by
          intro h
          have hlt := hstep.length_lt.trans (bruhat_covBy_step cs hcovuz).length_lt
          rw [h] at hlt
          exact Nat.lt_irrefl _ hlt
        apply reverse_diamond_mem realization hux huw huz hwz
          (Ne.symm hwne) hlow_ne (labelSpan realization u v)
        · exact Submodule.subset_span
            ⟨u, ⟨Relation.ReflTransGen.refl, huv⟩,
              z, ⟨hcovuz.le, hzv.trans hvcover.le⟩, huz, rfl⟩
        · have hlabel : edgeLabel realization w z hwz ∈
              labelSpan realization w (v * cs.simple i) :=
            Submodule.subset_span
              ⟨w, ⟨Relation.ReflTransGen.refl, hw_vs⟩, z, ⟨hcovwz.le, hzv⟩, hwz, rfl⟩
          rw [← hrec] at hlabel
          exact labelSpan_mono realization hdiamond.1.le Relation.ReflTransGen.refl hlabel
      · have hdiamond : u ⋖ x * cs.simple i ∧ x ⋖ x * cs.simple i := by
          simpa only [cs.simple_mul_simple_cancel_right] using
            upward_diamond i hcover huascent (by
              simpa only [cs.simple_mul_simple_cancel_right] using hspecial)
        have hupper : cs.BruhatLE (x * cs.simple i) v := by
          simpa only [cs.simple_mul_simple_cancel_right] using
            hx.2.mul_simple_of_not_isRightDescent i hvascent
        rw [← edgeLabel_mul_right realization (u * cs.simple i) x hux (cs.simple i)]
        simp only [cs.simple_mul_simple_cancel_right]
        exact Submodule.subset_span
          ⟨u, ⟨Relation.ReflTransGen.refl, huv⟩,
            x * cs.simple i, ⟨hdiamond.1.le, hupper⟩, _, rfl⟩


private theorem ascent_span (u v : W) (huv : cs.BruhatLE u v) (i : Index)
    (hu : ¬ cs.IsRightDescent u i) (hv : cs.IsRightDescent v i) :
    labelSpan realization u v = labelSpan realization u (v * cs.simple i) ⊔
      Submodule.span ℝ ({(edgeLabel realization u (u * cs.simple i)
        ((cs.isReflection_simple i).conj u))} : Set V) := by
  let : PartialOrder W := cs.bruhatPartialOrder
  have hlow : cs.BruhatLE u (v * cs.simple i) := bruhatLE_mul_of_ascent cs huv i hu
  have hhigh : cs.BruhatLE (u * cs.simple i) v :=
    huv.mul_simple_of_isRightDescent i hv
  apply le_antisymm
  · rw [(labelSpan_eq_covers realization u v huv).2.1]
    apply Submodule.span_le.mpr
    rintro α ⟨x, hx, hux, hlength, rfl⟩
    have hstep := bruhatStep_iff_adj.mpr ⟨hux, by omega⟩
    have hcover : u ⋖ x := (bruhat_covBy_iff cs u x).mpr ⟨hstep.bruhatLE, hlength⟩
    by_cases heq : x = u * cs.simple i
    · subst x
      apply Submodule.mem_sup_right
      exact Submodule.subset_span rfl
    · have hdiamond := upward_diamond i hcover hu heq
      have hxascent := ascent_of_cover i hdiamond.2
      have hxupper := bruhatLE_mul_of_ascent cs hx.2 i hxascent
      apply Submodule.mem_sup_left
      exact Submodule.subset_span
        ⟨u, ⟨Relation.ReflTransGen.refl, hlow⟩, x, ⟨hx.1, hxupper⟩, hux, rfl⟩
  · apply sup_le
    · exact labelSpan_mono realization Relation.ReflTransGen.refl (descent_cover v i hv).le
    · apply Submodule.span_le.mpr
      rintro α rfl
      exact Submodule.subset_span
        ⟨u, ⟨Relation.ReflTransGen.refl, huv⟩,
          u * cs.simple i, ⟨(ascent_cover u i hu).le, hhigh⟩, _, rfl⟩

/-- At a right descent of the upper endpoint, common lower descent preserves the label span;
a lower ascent adds the line of its simple edge to the span with shortened upper endpoint. -/
theorem labelSpan_recursion (u v : W) (huv : cs.BruhatLE u v) (i : Index)
    (hv : cs.IsRightDescent v i) :
    (cs.IsRightDescent u i →
      labelSpan realization u v =
        labelSpan realization (u * cs.simple i) (v * cs.simple i)) ∧
    (¬ cs.IsRightDescent u i →
      labelSpan realization u v = labelSpan realization u (v * cs.simple i) ⊔
        Submodule.span ℝ ({(edgeLabel realization u (u * cs.simple i)
          ((cs.isReflection_simple i).conj u))} : Set V)) := by
  exact ⟨fun hu => descent_span realization u v huv i hu hv,
    fun hu => ascent_span realization u v huv i hu hv⟩

end BruhatIntervals

