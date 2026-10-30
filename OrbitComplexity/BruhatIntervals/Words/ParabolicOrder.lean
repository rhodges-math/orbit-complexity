import OrbitComplexity.BruhatIntervals.Words.Parabolic
import OrbitComplexity.BruhatIntervals.Words.Support

/-!
# Bruhat comparison of parabolic representatives

A subword of a reduced parabolic-prefix factorization splits into a parabolic prefix and a
subword of the representative's suffix. Minimality puts the lower representative below that
suffix subword, giving monotonicity of minimal left representatives and their support sizes.

## Main results

* `minimalLeftRep_mono`: Bruhat comparison descends to the minimal left representatives.
* `supportCard_minimalLeftRep_mono`: their support cardinalities increase accordingly.
* `minimalLeftRep_support_maximum`: the top representative attains their maximum support size.

## References

* A. Björner and F. Brenti, *Combinatorics of Coxeter Groups*, Springer GTM 231 (2005),
  Section 2.4.
-/

namespace BruhatIntervals

universe u v

variable {Index : Type u} {W : Type v} [Group W] {matrix : CoxeterMatrix Index}
  (cs : CoxeterSystem matrix W)

private theorem reduced_append {first last : List Index} (hfirst : cs.IsReduced first)
    (hlast : cs.IsReduced last)
    (hlength : cs.length (cs.wordProd first * cs.wordProd last) =
      cs.length (cs.wordProd first) + cs.length (cs.wordProd last)) :
    cs.IsReduced (first ++ last) := by
  rw [CoxeterSystem.IsReduced, cs.wordProd_append, hlength, hfirst.eq, hlast.eq,
    List.length_append]

private theorem minimal_le_translate {indices : Set Index} {b g : W}
    (hb : IsMinimalLeftRep cs indices b) (hg : g ∈ cs.parabolic indices) :
    cs.BruhatLE b (g * b) := by
  obtain ⟨first, hfirst, hfirstprod⟩ := cs.exists_isReduced g
  obtain ⟨last, hlast, hlastprod⟩ := cs.exists_isReduced b
  have hlength : cs.length (cs.wordProd first * cs.wordProd last) =
      cs.length (cs.wordProd first) + cs.length (cs.wordProd last) := by
    rw [← hfirstprod, ← hlastprod]
    exact cs.length_mul_of_forall_not_isLeftDescent hg ((isMinimalLeftRep_iff cs).mp hb)
  have hred := reduced_append cs hfirst hlast hlength
  have hbelow := cs.bruhatLE_wordProd_of_sublist hred (List.sublist_append_right first last)
  simpa only [cs.wordProd_append, ← hfirstprod, ← hlastprod] using hbelow

/-- Bruhat comparison of parabolic-prefix products implies comparison of their minimal
left parabolic representatives. -/
theorem minimalLeftRep_mono {indices : Set Index} {a b c d : W}
    (ha : a ∈ cs.parabolic indices) (hb : IsMinimalLeftRep cs indices b)
    (hc : c ∈ cs.parabolic indices) (hd : IsMinimalLeftRep cs indices d)
    (hle : cs.BruhatLE (a * b) (c * d)) : cs.BruhatLE b d := by
  obtain ⟨first, hfirst, hletters, hfirstprod⟩ :=
    cs.exists_isReduced_wordProd_eq_of_mem_parabolic hc
  obtain ⟨last, hlast, hlastprod⟩ := cs.exists_isReduced d
  have hlength : cs.length (cs.wordProd first * cs.wordProd last) =
      cs.length (cs.wordProd first) + cs.length (cs.wordProd last) := by
    rw [hfirstprod, ← hlastprod]
    exact cs.length_mul_of_forall_not_isLeftDescent hc ((isMinimalLeftRep_iff cs).mp hd)
  have hred := reduced_append cs hfirst hlast hlength
  have hwhole : cs.wordProd (first ++ last) = c * d := by
    rw [cs.wordProd_append, hfirstprod, ← hlastprod]
  obtain ⟨subword, hsubword, hproduct⟩ := (subword_property cs hred hwhole).mp hle
  obtain ⟨initial, final, rfl, hinitial, hfinal⟩ := List.sublist_append_iff.mp hsubword
  have hparabolic : cs.wordProd initial ∈ cs.parabolic indices :=
    cs.wordProd_mem_parabolic fun i hi => hletters i (hinitial.subset hi)
  have htranslate : (cs.wordProd initial)⁻¹ * a ∈ cs.parabolic indices :=
    (cs.parabolic indices).mul_mem ((cs.parabolic indices).inv_mem hparabolic) ha
  have hremaining : cs.wordProd final = (cs.wordProd initial)⁻¹ * a * b := by
    rw [cs.wordProd_append] at hproduct
    have heq := congrArg (fun value => (cs.wordProd initial)⁻¹ * value) hproduct
    simpa only [← mul_assoc, inv_mul_cancel, one_mul] using heq
  have hbelow : cs.BruhatLE b (cs.wordProd final) := by
    rw [hremaining]
    exact minimal_le_translate cs hb htranslate
  apply hbelow.trans
  rw [hlastprod]
  exact cs.bruhatLE_wordProd_of_sublist hlast hfinal

/-- The support cardinalities of minimal left representatives increase along Bruhat
comparison of the corresponding parabolic-prefix products. -/
theorem supportCard_minimalLeftRep_mono {indices : Set Index} {a b c d : W}
    (ha : a ∈ cs.parabolic indices) (hb : IsMinimalLeftRep cs indices b)
    (hc : c ∈ cs.parabolic indices) (hd : IsMinimalLeftRep cs indices d)
    (hle : cs.BruhatLE (a * b) (c * d)) : supportCard cs b ≤ supportCard cs d :=
  supportCard_mono cs (minimalLeftRep_mono cs ha hb hc hd hle)

/-- The support size of the top minimal left representative is the attained maximum among
the minimal left representatives of all lower parabolic-prefix products. -/
theorem minimalLeftRep_support_maximum {indices : Set Index} {c d : W}
    (hc : c ∈ cs.parabolic indices) (hd : IsMinimalLeftRep cs indices d) :
    IsGreatest {size : ℕ | ∃ a b : W, a ∈ cs.parabolic indices ∧
      IsMinimalLeftRep cs indices b ∧ cs.BruhatLE (a * b) (c * d) ∧ supportCard cs b = size}
      (supportCard cs d) := by
  refine ⟨⟨c, d, hc, hd, cs.bruhatLE_refl _, rfl⟩, ?_⟩
  rintro size ⟨a, b, ha, hb, hle, rfl⟩
  exact supportCard_minimalLeftRep_mono cs ha hb hc hd hle

end BruhatIntervals
