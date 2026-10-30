import OrbitComplexity.SchubertGeometry.Parabolics.Order

/-! # Bruhat order on canonical left parabolic representatives

Canonical minimum representatives inherit Bruhat comparison and support monotonicity.
-/

noncomputable section
namespace SchubertGeometry
open ReductiveGroups BruhatIntervals
universe u v w x
variable {ι : Type u} {K : Type v} {M : Type w} {N : Type x}
  [Field K] [CharZero K] [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
  {P : RootPairing ι K M N} [Finite ι] [P.IsCrystallographic] [P.IsReduced]

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
    IsMinimalLeftParabolic b J d ↔ IsMinimalLeftRep (weylCoxeterSystem b) J d := by
  change (∀ a ∈ standardParabolicSubgroup b J,
    rootInversionCount b d ≤ rootInversionCount b (a * d)) ↔
    ∀ a ∈ (weylCoxeterSystem b).parabolic J,
      (weylCoxeterSystem b).length d ≤ (weylCoxeterSystem b).length (a * d)
  rw [parabolic_eq]
  simp only [weylCoxeterSystem_length]

/-- Canonical minimum left representatives preserve ordinary Bruhat comparison. -/
theorem leftParabolicRepresentative_mono (b : P.Base) (J : Set b.support)
    (u v : P.weylGroup) (huv : WeylBruhatLE b u v) :
    WeylBruhatLE b (leftParabolicRepresentative b J u) (leftParabolicRepresentative b J v) := by
  have hu : leftParabolicFactor b J u ∈ (weylCoxeterSystem b).parabolic J := by
    rw [parabolic_eq]
    exact leftParabolicFactor_mem b J u
  have hv : leftParabolicFactor b J v ∈ (weylCoxeterSystem b).parabolic J := by
    rw [parabolic_eq]
    exact leftParabolicFactor_mem b J v
  have hproducts : (weylCoxeterSystem b).BruhatLE
      (leftParabolicFactor b J u * leftParabolicRepresentative b J u)
      (leftParabolicFactor b J v * leftParabolicRepresentative b J v) := by
    rw [← leftParabolic_factorization b J u, ← leftParabolic_factorization b J v]
    exact (weyl_bruhat_iff b u v).mp huv
  exact (weyl_bruhat_iff b _ _).mpr (minimalLeftRep_mono (weylCoxeterSystem b) hu
    ((minimal_iff b J _).mp (leftParabolicRepresentative_minimal b J u)) hv
    ((minimal_iff b J _).mp (leftParabolicRepresentative_minimal b J v)) hproducts)

/-- Support sizes of canonical minimum left representatives increase along Bruhat order. -/
theorem leftParabolic_supportCard_mono (b : P.Base) (J : Set b.support)
    (u v : P.weylGroup) (huv : WeylBruhatLE b u v) :
    supportCard (weylCoxeterSystem b) (leftParabolicRepresentative b J u) ≤
      supportCard (weylCoxeterSystem b) (leftParabolicRepresentative b J v) :=
  supportCard_mono (weylCoxeterSystem b)
    ((weyl_bruhat_iff b _ _).mp (leftParabolicRepresentative_mono b J u v huv))

end SchubertGeometry
