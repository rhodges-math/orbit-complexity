import OrbitComplexity.BruhatIntervals.Graph.ToricCovers

/-!
# Maximal toric subintervals

The algebraic dimension of an interval is the largest length of a toric lower interval, of a
toric upper interval, and of any toric subinterval. Each largest value is attained.

## Main results

* `toric_interval_maxima`: the three attained maxima are the interval's algebraic dimension.

## References

* A. Björner and F. Brenti, *Combinatorics of Coxeter Groups*, Springer GTM 231 (2005),
  Sections 2.2 and 2.7.
-/

namespace BruhatIntervals

variable {Index W V : Type*} [Group W] {matrix : CoxeterMatrix Index}
  {cs : CoxeterSystem matrix W} [AddCommGroup V] [Module ℝ V]
  (realization : Realization cs (V := V))

private theorem lower_attain (u v : W) (huv : cs.BruhatLE u v) :
    ∃ w ∈ bruhatInterval cs u v, IsToricInterval realization u w ∧
      algebraicDim realization u v = cs.length w - cs.length u := by
  let : PartialOrder W := cs.bruhatPartialOrder
  suffices aux : ∀ n : ℕ, ∀ u v : W, cs.length v - cs.length u = n → cs.BruhatLE u v →
      ∃ w ∈ bruhatInterval cs u v, IsToricInterval realization u w ∧
        algebraicDim realization u v = cs.length w - cs.length u by
    exact aux (cs.length v - cs.length u) u v rfl huv
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro u v hgap huv
    by_cases htoric : IsToricInterval realization u v
    · exact ⟨v, ⟨huv, Relation.ReflTransGen.refl⟩, htoric, htoric⟩
    obtain ⟨v', huv', hcov, hsame⟩ := exists_same_span_top_cover realization u v huv htoric
    have hlength := ((bruhat_covBy_iff cs v' v).mp hcov).2
    obtain ⟨w, hw, htoricw, hdimw⟩ := ih (cs.length v' - cs.length u) (by
      have := huv'.length_le
      omega) u v' rfl huv'
    have hdim : algebraicDim realization u v = algebraicDim realization u v' :=
      congrArg (fun plane : Submodule ℝ V => Module.finrank ℝ plane) hsame
    exact ⟨w, ⟨hw.1, hw.2.trans hcov.le⟩, htoricw, hdim.trans hdimw⟩

private theorem upper_attain (u v : W) (huv : cs.BruhatLE u v) :
    ∃ w ∈ bruhatInterval cs u v, IsToricInterval realization w v ∧
      algebraicDim realization u v = cs.length v - cs.length w := by
  let : PartialOrder W := cs.bruhatPartialOrder
  suffices aux : ∀ n : ℕ, ∀ u v : W, cs.length v - cs.length u = n → cs.BruhatLE u v →
      ∃ w ∈ bruhatInterval cs u v, IsToricInterval realization w v ∧
        algebraicDim realization u v = cs.length v - cs.length w by
    exact aux (cs.length v - cs.length u) u v rfl huv
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro u v hgap huv
    by_cases htoric : IsToricInterval realization u v
    · exact ⟨u, ⟨Relation.ReflTransGen.refl, huv⟩, htoric, htoric⟩
    obtain ⟨u', hcov, hu'v, hsame⟩ := exists_same_span_bottom_cover realization u v huv htoric
    have hlength := ((bruhat_covBy_iff cs u u').mp hcov).2
    obtain ⟨w, hw, htoricw, hdimw⟩ := ih (cs.length v - cs.length u') (by
      have := hu'v.length_le
      omega) u' v rfl hu'v
    have hdim : algebraicDim realization u v = algebraicDim realization u' v :=
      congrArg (fun plane : Submodule ℝ V => Module.finrank ℝ plane) hsame
    exact ⟨w, ⟨hcov.le.trans hw.1, hw.2⟩, htoricw, hdim.trans hdimw⟩

/-- The longest toric lower intervals, upper intervals, and subintervals all have length equal
to the ambient interval's algebraic dimension, and each of the three maxima is attained. -/
theorem toric_interval_maxima (u v : W) (huv : cs.BruhatLE u v) :
    IsGreatest {n : ℕ | ∃ w ∈ bruhatInterval cs u v,
      IsToricInterval realization u w ∧ cs.length w - cs.length u = n}
      (algebraicDim realization u v) ∧
    IsGreatest {n : ℕ | ∃ w ∈ bruhatInterval cs u v,
      IsToricInterval realization w v ∧ cs.length v - cs.length w = n}
      (algebraicDim realization u v) ∧
    IsGreatest {n : ℕ | ∃ x ∈ bruhatInterval cs u v, ∃ y ∈ bruhatInterval cs u v,
      cs.BruhatLE x y ∧ IsToricInterval realization x y ∧ cs.length y - cs.length x = n}
      (algebraicDim realization u v) := by
  obtain ⟨lower, hlower, htoricLower, hdimLower⟩ := lower_attain realization u v huv
  obtain ⟨upper, hupper, htoricUpper, hdimUpper⟩ := upper_attain realization u v huv
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · exact ⟨lower, hlower, htoricLower, hdimLower.symm⟩
  · rintro n ⟨w, hw, htoric, hlength⟩
    have hmono : algebraicDim realization u w ≤ algebraicDim realization u v :=
      Submodule.finrank_mono (labelSpan_mono realization Relation.ReflTransGen.refl hw.2)
    change algebraicDim realization u w = cs.length w - cs.length u at htoric
    simpa only [htoric, hlength] using hmono
  · exact ⟨upper, hupper, htoricUpper, hdimUpper.symm⟩
  · rintro n ⟨w, hw, htoric, hlength⟩
    have hmono : algebraicDim realization w v ≤ algebraicDim realization u v :=
      Submodule.finrank_mono (labelSpan_mono realization hw.1 Relation.ReflTransGen.refl)
    change algebraicDim realization w v = cs.length v - cs.length w at htoric
    simpa only [htoric, hlength] using hmono
  · exact ⟨u, ⟨Relation.ReflTransGen.refl, huv⟩,
      lower, hlower, hlower.1, htoricLower, hdimLower.symm⟩
  · rintro n ⟨x, hx, y, hy, _, htoric, hlength⟩
    have hmono : algebraicDim realization x y ≤ algebraicDim realization u v :=
      Submodule.finrank_mono (labelSpan_mono realization hx.1 hy.2)
    change algebraicDim realization x y = cs.length y - cs.length x at htoric
    simpa only [htoric, hlength] using hmono

end BruhatIntervals

