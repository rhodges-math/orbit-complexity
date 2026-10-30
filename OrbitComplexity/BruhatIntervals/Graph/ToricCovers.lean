import OrbitComplexity.BruhatIntervals.Graph.Toric

/-!
# Moving zero dimension increments along chains

A non-toric interval has a cover at either end with the same label span. The proof moves a zero
dimension increment upward or downward through an adjacent one increment using a rank-two diamond.

## Main results

* `exists_same_span_top_cover`: a non-toric interval has a top cover with unchanged span.
* `exists_same_span_bottom_cover`: a non-toric interval has a bottom cover with unchanged span.

## References

* A. Björner and F. Brenti, *Combinatorics of Coxeter Groups*, Springer GTM 231 (2005),
  Sections 2.2 and 2.7.
-/

namespace BruhatIntervals

variable {Index W V : Type*} [Group W] {matrix : CoxeterMatrix Index}
  {cs : CoxeterSystem matrix W} [AddCommGroup V] [Module ℝ V]
  (realization : Realization cs (V := V))

private theorem line_step (B D : Submodule ℝ V) [FiniteDimensional ℝ B]
    [FiniteDimensional ℝ D] (root : V) (hspan : D = B ⊔ (ℝ ∙ root)) (hne : D ≠ B) :
    Module.finrank ℝ D = Module.finrank ℝ B + 1 := by
  classical
  have : FiniteDimensional ℝ (ℝ ∙ root) :=
    FiniteDimensional.span_of_finite ℝ (Set.finite_singleton root)
  have hline : Module.finrank ℝ (ℝ ∙ root) ≤ 1 := by
    simpa using finrank_span_le_card (R := ℝ) ({root} : Set V)
  have hle : B ≤ D := by rw [hspan]; exact le_sup_left
  have hstrict := Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne hle (Ne.symm hne))
  have hbound := Submodule.finrank_add_le_finrank_add_finrank B (ℝ ∙ root)
  rw [← hspan] at hbound
  omega

private theorem bottom_span (u w v : W) (hwv : cs.BruhatLE w v) :
    let : PartialOrder W := cs.bruhatPartialOrder
    u ⋖ w → ∀ h : (bruhatGraph cs).Adj u w,
      labelSpan realization u v =
        labelSpan realization w v ⊔ (ℝ ∙ edgeLabel realization u w h) := by
  let : PartialOrder W := cs.bruhatPartialOrder
  dsimp only
  intro hcov h
  have hlen := ((bruhat_covBy_iff cs u w).mp hcov).2
  have hline := (labelSpan_properties realization u w hcov.le).1 u
    ⟨Relation.ReflTransGen.refl, hcov.le⟩ h hlen
  rw [labelSpan_self, bot_sup_eq] at hline
  calc
    labelSpan realization u v = labelSpan realization u w ⊔ labelSpan realization w v :=
      labelSpan_split realization u w v hcov.le hwv
    _ = labelSpan realization w v ⊔ (ℝ ∙ edgeLabel realization u w h) := by
      rw [hline, sup_comm]

/-- A non-toric Bruhat interval has a top cover whose lower subinterval has the same label span. -/
theorem exists_same_span_top_cover (u v : W) (huv : cs.BruhatLE u v)
    (hnot : ¬ IsToricInterval realization u v) :
    let : PartialOrder W := cs.bruhatPartialOrder
    ∃ w : W, cs.BruhatLE u w ∧ w ⋖ v ∧ labelSpan realization u v = labelSpan realization u w := by
  let : PartialOrder W := cs.bruhatPartialOrder
  suffices aux : ∀ n : ℕ, ∀ u v : W, cs.length v - cs.length u = n →
      cs.BruhatLE u v → ¬ IsToricInterval realization u v →
      ∃ w : W, cs.BruhatLE u w ∧ w ⋖ v ∧
        labelSpan realization u v = labelSpan realization u w by
    exact aux (cs.length v - cs.length u) u v rfl huv hnot
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro u v hgap huv hnot
    by_cases heq : u = v
    · subst v
      exact (hnot (by simp [IsToricInterval, algebraicDim, labelSpan_self])).elim
    obtain ⟨w, huw, hcovwv⟩ := exists_le_bruhat_covBy cs huv heq
    by_cases hsame : labelSpan realization u v = labelSpan realization u w
    · exact ⟨w, huw, hcovwv, hsame⟩
    have hwvlen := ((bruhat_covBy_iff cs w v).mp hcovwv).2
    have hadj := (bruhatStep_iff_adj.mp (bruhat_covBy_step cs hcovwv)).1
    have hformula := (labelSpan_properties realization u v huv).1 w ⟨huw, hcovwv.le⟩
      hadj hwvlen
    have hdim : algebraicDim realization u v = algebraicDim realization u w + 1 :=
      line_step _ _ (edgeLabel realization w v hadj) hformula hsame
    have hlt : algebraicDim realization u v < cs.length v - cs.length u := by
      have hbound := algebraicDim_le_length realization u v huv
      have hne : algebraicDim realization u v ≠ cs.length v - cs.length u := hnot
      omega
    have hnotw : ¬ IsToricInterval realization u w := by
      intro htoric
      change algebraicDim realization u w = cs.length w - cs.length u at htoric
      have := huw.length_le
      omega
    obtain ⟨z, huz, hcovzw, hsamew⟩ := ih (cs.length w - cs.length u) (by
      have := huw.length_le
      omega) u w rfl huw hnotw
    obtain ⟨w', ⟨hwne, hcovzw', hcovw'v⟩, _⟩ :=
      bruhat_rank_two_diamond cs z w v hcovzw hcovwv
    have hdimsame : algebraicDim realization u w = algebraicDim realization u z :=
      congrArg (fun plane : Submodule ℝ V => Module.finrank ℝ plane) hsamew
    have hstep : algebraicDim realization u v - algebraicDim realization u z = 1 := by omega
    have hswap := swap_zero_one realization u v z w w' huv
      ⟨huz, hcovzw.le.trans hcovwv.le⟩ ⟨huw, hcovwv.le⟩
      ⟨huz.trans hcovzw'.le, hcovw'v.le⟩ (Ne.symm hwne)
      hcovzw hcovwv hcovzw' hcovw'v hstep
    exact ⟨w', huz.trans hcovzw'.le, hcovw'v, hswap.resolve_left hsame⟩


private theorem middle_eq (A B D : Submodule ℝ V)
    [FiniteDimensional ℝ B] [FiniteDimensional ℝ D]
    (hAB : A ≤ B) (hBD : B ≤ D)
    (hstep : Module.finrank ℝ D - Module.finrank ℝ A = 1) (hne : B ≠ D) : A = B := by
  have hlow := Submodule.finrank_mono hAB
  have hhigh := Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne hBD hne)
  exact Submodule.eq_of_le_of_finrank_eq hAB (by omega)

private theorem swap_dual (u v x y1 y2 : W)
    (hx : x ∈ bruhatInterval cs u v) (hy1 : y1 ∈ bruhatInterval cs u v)
    (hy2 : y2 ∈ bruhatInterval cs u v) (hne : y1 ≠ y2) :
    let : PartialOrder W := cs.bruhatPartialOrder
    u ⋖ y1 → y1 ⋖ x → u ⋖ y2 → y2 ⋖ x →
    algebraicDim realization u v - algebraicDim realization x v = 1 →
    labelSpan realization u v = labelSpan realization y1 v ∨
      labelSpan realization u v = labelSpan realization y2 v := by
  let : PartialOrder W := cs.bruhatPartialOrder
  dsimp only
  intro huy1 hy1x huy2 hy2x hstep
  by_cases hfirst : labelSpan realization u v = labelSpan realization y1 v
  · exact Or.inl hfirst
  by_cases hsecond : labelSpan realization u v = labelSpan realization y2 v
  · exact Or.inr hsecond
  have hA1 := middle_eq (labelSpan realization x v)
    (labelSpan realization y1 v) (labelSpan realization u v)
    (labelSpan_mono realization hy1x.le Relation.ReflTransGen.refl)
    (labelSpan_mono realization huy1.le Relation.ReflTransGen.refl) hstep (Ne.symm hfirst)
  have hA2 := middle_eq (labelSpan realization x v)
    (labelSpan realization y2 v) (labelSpan realization u v)
    (labelSpan_mono realization hy2x.le Relation.ReflTransGen.refl)
    (labelSpan_mono realization huy2.le Relation.ReflTransGen.refl) hstep (Ne.symm hsecond)
  have ha := (bruhatStep_iff_adj.mp (bruhat_covBy_step cs hy1x)).1
  have hb := (bruhatStep_iff_adj.mp (bruhat_covBy_step cs hy2x)).1
  have hc := (bruhatStep_iff_adj.mp (bruhat_covBy_step cs huy1)).1
  have hd := (bruhatStep_iff_adj.mp (bruhat_covBy_step cs huy2)).1
  have hlabel1 : edgeLabel realization y1 x ha ∈ labelSpan realization x v := by
    rw [hA1]
    exact Submodule.subset_span
      ⟨y1, ⟨Relation.ReflTransGen.refl, hy1.2⟩, x, ⟨hy1x.le, hx.2⟩, ha, rfl⟩
  have hlabel2 : edgeLabel realization y2 x hb ∈ labelSpan realization x v := by
    rw [hA2]
    exact Submodule.subset_span
      ⟨y2, ⟨Relation.ReflTransGen.refl, hy2.2⟩, x, ⟨hy2x.le, hx.2⟩, hb, rfl⟩
  have huxne : u ≠ x := by
    intro heq
    have hlt := (bruhat_covBy_step cs huy1).length_lt.trans
      (bruhat_covBy_step cs hy1x).length_lt
    rw [heq] at hlt
    exact Nat.lt_irrefl _ hlt
  have hinput1 : edgeLabel realization x y1 ((bruhatGraph cs).adj_symm ha) ∈
      labelSpan realization x v := by
    rw [← edgeLabel_symm realization y1 x ha]
    exact hlabel1
  have hinput2 : edgeLabel realization x y2 ((bruhatGraph cs).adj_symm hb) ∈
      labelSpan realization x v := by
    rw [← edgeLabel_symm realization y2 x hb]
    exact hlabel2
  have hreverse := edgeLabel_mem_of_diamond realization
    ((bruhatGraph cs).adj_symm ha) ((bruhatGraph cs).adj_symm hb)
    ((bruhatGraph cs).adj_symm hc) ((bruhatGraph cs).adj_symm hd)
    hne (Ne.symm huxne) (labelSpan realization x v) hinput1 hinput2
  have hlower : edgeLabel realization u y1 hc ∈ labelSpan realization x v := by
    rw [edgeLabel_symm realization u y1 hc]
    exact hreverse
  have hformula := bottom_span realization u y1 v hy1.2 huy1 hc
  apply False.elim
  apply hfirst
  apply hformula.trans
  apply sup_eq_left.mpr
  apply Submodule.span_le.mpr
  rintro root rfl
  exact hA1 ▸ hlower

/-- A non-toric Bruhat interval has a bottom cover whose upper subinterval has the same span. -/
theorem exists_same_span_bottom_cover (u v : W) (huv : cs.BruhatLE u v)
    (hnot : ¬ IsToricInterval realization u v) :
    let : PartialOrder W := cs.bruhatPartialOrder
    ∃ w : W, u ⋖ w ∧ cs.BruhatLE w v ∧ labelSpan realization u v = labelSpan realization w v := by
  let : PartialOrder W := cs.bruhatPartialOrder
  suffices aux : ∀ n : ℕ, ∀ u v : W, cs.length v - cs.length u = n →
      cs.BruhatLE u v → ¬ IsToricInterval realization u v →
      ∃ w : W, u ⋖ w ∧ cs.BruhatLE w v ∧
        labelSpan realization u v = labelSpan realization w v by
    exact aux (cs.length v - cs.length u) u v rfl huv hnot
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro u v hgap huv hnot
    by_cases heq : u = v
    · subst v
      exact (hnot (by simp [IsToricInterval, algebraicDim, labelSpan_self])).elim
    obtain ⟨w, hcovuw, hwv⟩ := exists_bruhat_covBy_le cs huv heq
    by_cases hsame : labelSpan realization u v = labelSpan realization w v
    · exact ⟨w, hcovuw, hwv, hsame⟩
    have huwlen := ((bruhat_covBy_iff cs u w).mp hcovuw).2
    have hadj := (bruhatStep_iff_adj.mp (bruhat_covBy_step cs hcovuw)).1
    have hformula := bottom_span realization u w v hwv hcovuw hadj
    have hdim : algebraicDim realization u v = algebraicDim realization w v + 1 :=
      line_step _ _ (edgeLabel realization u w hadj) hformula hsame
    have hlt : algebraicDim realization u v < cs.length v - cs.length u := by
      have hbound := algebraicDim_le_length realization u v huv
      have hne : algebraicDim realization u v ≠ cs.length v - cs.length u := hnot
      omega
    have hnotw : ¬ IsToricInterval realization w v := by
      intro htoric
      change algebraicDim realization w v = cs.length v - cs.length w at htoric
      have := hwv.length_le
      omega
    obtain ⟨z, hcovwz, hzv, hsamew⟩ := ih (cs.length v - cs.length w) (by
      have := hwv.length_le
      omega) w v rfl hwv hnotw
    obtain ⟨w', ⟨hwne, hcovuw', hcovw'z⟩, _⟩ :=
      bruhat_rank_two_diamond cs u w z hcovuw hcovwz
    have hdimsame : algebraicDim realization w v = algebraicDim realization z v :=
      congrArg (fun plane : Submodule ℝ V => Module.finrank ℝ plane) hsamew
    have hstep : algebraicDim realization u v - algebraicDim realization z v = 1 := by omega
    have hswap := swap_dual realization u v z w w'
      ⟨hcovuw.le.trans hcovwz.le, hzv⟩ ⟨hcovuw.le, hwv⟩
      ⟨hcovuw'.le, hcovw'z.le.trans hzv⟩ (Ne.symm hwne)
      hcovuw hcovwz hcovuw' hcovw'z hstep
    exact ⟨w', hcovuw', hcovw'z.le.trans hzv, hswap.resolve_left hsame⟩

end BruhatIntervals

