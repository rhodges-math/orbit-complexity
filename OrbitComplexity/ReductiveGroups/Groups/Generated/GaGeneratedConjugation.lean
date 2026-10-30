import OrbitComplexity.ReductiveGroups.Groups.Generated.GaGeneratedTangentCriterion

/-!
# Ga Generated Conjugation

Invariance of a Ga-generated Hopf ideal under a coordinate Hopf
endomorphism follows from stability of the generating tangents. -/

noncomputable section
namespace ReductiveGroups

universe u v
variable {K B : Type u} [Field K] [CharZero K]
  [CommRing B] [HopfAlgebra K B] {ι : Type v}

/-- A coordinate Hopf endomorphism that pulls every generating tangent back
to another generating tangent preserves the defining ideal of the generated
closed subgroup. This is the needed ideal orientation for a group action. -/
theorem GaGeneratedHopfIdeal.stable_of_tangent_closed
    (f : ι → B →ₐc[K] SymmetricAlgebra K K)
    (e : B →ₐc[K] B)
    (he : Function.Surjective e)
    (h : ∀ i, ∃ j, TauCeti.derivationComp (B := K) e
      (gaAffineGroupTangent (f i)) = gaAffineGroupTangent (f j))
    (b : B) (hb : b ∈ gaGeneratedHopfIdeal f) :
    e b ∈ gaGeneratedHopfIdeal f := by
  have hmap : (gaGeneratedHopfIdeal f).map e ≤ gaGeneratedHopfIdeal f := by
    apply (le_gaGeneratedHopfIdeal_iff_tangents f _).mpr
    intro i x hx
    obtain ⟨y, hy, rfl⟩ :=
      (TauCeti.HopfIdeal.mem_map_iff_of_surjective he).mp hx
    obtain ⟨j, hij⟩ := h i
    have hzero := (le_gaGeneratedHopfIdeal_iff_tangents f _).mp le_rfl j y hy
    have hval := congrArg (fun d => d y) hij
    rw [TauCeti.derivationComp_apply] at hval
    exact hval.trans hzero
  exact hmap (TauCeti.HopfIdeal.mem_map_of_mem e hb)

end ReductiveGroups
