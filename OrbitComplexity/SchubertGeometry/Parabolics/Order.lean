import OrbitComplexity.BruhatIntervals.Words.ParabolicRightOrder
import OrbitComplexity.ReductiveGroups.Roots.Parabolic.Longest
import OrbitComplexity.ReductiveGroups.Roots.Coxeter.BruhatSubword

/-! # Parabolic Bruhat ideals in Weyl groups

The ordinary root subword order equals the Coxeter Bruhat order. The interval below
a longest parabolic element is its parabolic Weyl subgroup. Right parabolic projection
identifies the lower ideal of a maximal coset element with the ideal of its minimum.
-/

noncomputable section
namespace SchubertGeometry
open ReductiveGroups BruhatIntervals
universe u v w x
variable {ι : Type u} {K : Type v} {M : Type w} {N : Type x}
  [Field K] [CharZero K] [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
  {P : RootPairing ι K M N} [Finite ι] [P.IsCrystallographic] [P.IsReduced]

/-- Ordinary root subword order agrees with the Coxeter Bruhat order. -/
theorem weyl_bruhat_iff (b : P.Base) (u v : P.weylGroup) :
    WeylBruhatLE b u v ↔ (weylCoxeterSystem b).BruhatLE u v := by
  constructor
  · rintro ⟨l, k, hk, hprod, hkprod, hred, _⟩
    have h := (weylCoxeterSystem b).bruhatLE_wordProd_of_sublist
      ((weylCoxeterSystem_isReduced_iff b l).mpr hred) hk
    simpa only [weylCoxeterSystem_wordProd, hprod, hkprod] using h
  · intro h
    obtain ⟨l, hred, hprod⟩ := (weylCoxeterSystem b).exists_isReduced v
    have hwhole : (weylCoxeterSystem b).BruhatLE u ((weylCoxeterSystem b).wordProd l) := by
      rwa [← hprod]
    obtain ⟨k, hk, hkprod⟩ :=
      ((weylCoxeterSystem b).bruhatLE_iff_exists_sublist_wordProd_eq hred).mp hwhole
    have hprod' : simpleWeylWord b l = v := by
      simpa only [weylCoxeterSystem_wordProd] using hprod.symm
    have hkprod' : simpleWeylWord b k = u := by
      simpa only [weylCoxeterSystem_wordProd] using hkprod
    have hsub := weylBruhatLE_of_sublist b ((weylCoxeterSystem_isReduced_iff b l).mp hred) hk
    simpa only [hprod', hkprod'] using hsub

private theorem parabolic_eq (b : P.Base) (J : Set b.support) :
    (weylCoxeterSystem b).parabolic J = standardParabolicSubgroup b J := by
  rw [CoxeterSystem.parabolic, standardParabolicSubgroup]
  congr 1
  ext a
  simp only [Set.mem_image, weylCoxeterSystem_simple, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨i, hi, he⟩
    exact ⟨i, hi, he.symm⟩
  · rintro ⟨i, hi, he⟩
    exact ⟨i, hi, he.symm⟩

private theorem minimal_iff (b : P.Base) (J : Set b.support) (d : P.weylGroup) :
    IsMinimalRightParabolic b J d ↔ (weylCoxeterSystem b).IsMinimalCosetRep J d := by
  change (∀ a ∈ standardParabolicSubgroup b J,
    rootInversionCount b d ≤ rootInversionCount b (d * a)) ↔
    ∀ a ∈ (weylCoxeterSystem b).parabolic J,
      (weylCoxeterSystem b).length d ≤ (weylCoxeterSystem b).length (d * a)
  rw [parabolic_eq]
  simp only [weylCoxeterSystem_length]

private theorem longest_greatest (b : P.Base) (J : Set b.support) :
    let : PartialOrder P.weylGroup := (weylCoxeterSystem b).bruhatPartialOrder
    IsGreatest ((weylCoxeterSystem b).parabolic J : Set P.weylGroup)
      (longestParabolicElement b J) := by
  let : PartialOrder P.weylGroup := (weylCoxeterSystem b).bruhatPartialOrder
  dsimp only
  have ha : longestParabolicElement b J ∈ (weylCoxeterSystem b).parabolic J := by
    rw [parabolic_eq]
    exact longestParabolicElement_mem b J
  have hd : IsMinimalLeftRep (weylCoxeterSystem b) J 1 := by
    intro a _
    simp only [CoxeterSystem.length_one]
    exact Nat.zero_le _
  have hdesc : ∀ i ∈ J,
      (weylCoxeterSystem b).IsLeftDescent (longestParabolicElement b J) i := by
    intro i hi
    by_contra hn
    have hinc := (weylCoxeterSystem b).not_isLeftDescent_iff.mp hn
    simp only [weylCoxeterSystem_simple, weylCoxeterSystem_length] at hinc
    have hmem := (standardParabolicSubgroup b J).mul_mem
      (simple_mem_standardParabolicSubgroup b J i hi) (longestParabolicElement_mem b J)
    have hbound := longestParabolicElement_max b J _ hmem
    omega
  apply (parabolic_greatest_iff_descents (weylCoxeterSystem b) ha hd).mp
  simpa only [mul_one] using hdesc

/-- The interval below a longest parabolic element is its parabolic Weyl subgroup. -/
theorem weylParabolic_bruhat_iff (b : P.Base) (J : Set b.support) (v : P.weylGroup) :
    WeylBruhatLE b v (longestParabolicElement b J) ↔
      v ∈ standardParabolicSubgroup b J := by
  constructor
  · intro hle
    obtain ⟨l, hl, hprod, hlen⟩ := exists_reduced_standardParabolic_word b J _
      (longestParabolicElement_mem b J)
    have hred : rootInversionCount b (simpleWeylWord b l) = l.length := by
      rw [hprod, hlen]
    rw [← hprod] at hle
    obtain ⟨k, hk, hkprod, _⟩ := (weylBruhatLE_iff_subword b v l hred).mp hle
    rw [← hkprod]
    exact SimpleWeylWord.mem_standardParabolicSubgroup b J k (fun i hi => hl i (hk.subset hi))
  · intro hv
    have hv' : v ∈ (weylCoxeterSystem b).parabolic J := by rwa [parabolic_eq]
    exact (weyl_bruhat_iff b v _).mpr ((longest_greatest b J).2 hv')

/-- A longest right parabolic suffix gives the saturated lower Bruhat ideal. -/
theorem weylParabolic_saturation (b : P.Base) (J : Set b.support) (w u : P.weylGroup)
    (hw : IsMinimalRightParabolic b J w) :
    WeylBruhatLE b u (w * longestParabolicElement b J) ↔
      WeylBruhatLE b (rightParabolicRepresentative b J u) w := by
  have hf : rightParabolicFactor b J u ∈ (weylCoxeterSystem b).parabolic J := by
    rw [parabolic_eq]
    exact rightParabolicFactor_mem b J u
  have h := bruhatLE_parabolic_maximum_iff (weylCoxeterSystem b) hf
    ((minimal_iff b J _).mp (rightParabolicRepresentative_minimal b J u))
    ((minimal_iff b J w).mp hw) (longest_greatest b J)
  rw [← rightParabolic_factorization b J u] at h
  exact (weyl_bruhat_iff b u (w * longestParabolicElement b J)).trans
    (h.trans (weyl_bruhat_iff b (rightParabolicRepresentative b J u) w).symm)

end SchubertGeometry
