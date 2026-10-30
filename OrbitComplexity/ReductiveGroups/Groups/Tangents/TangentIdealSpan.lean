import OrbitComplexity.ReductiveGroups.Groups.Representations.AdjointFirstOrder

/-!
# Tangent Ideal Span

A tangent derivation annihilates an ideal in the augmentation ideal
exactly when it annihilates a set of ideal generators. Dual-number points
keep the Leibniz and augmentation conditions together in a kernel. -/

noncomputable section
namespace ReductiveGroups

variable {K B : Type*} [Field K] [CommRing B] [HopfAlgebra K B]

/-- For generators vanishing at the identity, vanishing of a tangent on
the generated ideal is equivalent to vanishing on the generators. -/
theorem tangent_vanishes_idealSpan_iff
    (S : Set B)
    (hS : ∀ b ∈ S,
      algebraMap B (TauCeti.Bialgebra.CounitAlgebra K B K) b = 0)
    (d : Derivation K B (TauCeti.Bialgebra.CounitAlgebra K B K)) :
    (∀ b ∈ Ideal.span S, d b = 0) ↔ ∀ b ∈ S, d b = 0 := by
  constructor
  · intro hd b hb
    exact hd b (Ideal.subset_span hb)
  · intro hd
    have hker : Ideal.span S ≤ RingHom.ker (tangentDualPoint d).ofConv := by
      apply Ideal.span_le.mpr
      intro b hb
      apply RingHom.mem_ker.mpr
      apply TrivSqZeroExt.ext
      · simpa only [tangentDualPoint_fst, TrivSqZeroExt.fst_zero] using hS b hb
      · simpa only [tangentDualPoint_snd, TrivSqZeroExt.snd_zero] using hd b hb
    intro b hb
    have hz := RingHom.mem_ker.mp (hker hb)
    have hs := congrArg TrivSqZeroExt.snd hz
    simpa only [tangentDualPoint_snd, TrivSqZeroExt.snd_zero] using hs

end ReductiveGroups
