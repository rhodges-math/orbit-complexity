import OrbitComplexity.ReductiveGroups.Groups.Generated.GaGeneratedSubgroup
import OrbitComplexity.ReductiveGroups.Groups.Tangents.SurjectiveTangentDescent

/-!
# Ga Generated Tangent Criterion

The generated closed subgroup can be tested using its generating
tangents: a Hopf ideal is killed by all additive-group morphisms exactly
when it is killed by all their tangent derivations. Characteristic zero
enters through uniqueness and reconstruction of Ga morphisms. -/

noncomputable section
namespace ReductiveGroups

universe u v
variable {K B : Type u} [Field K] [CharZero K] [CommRing B] [HopfAlgebra K B]

/-- For a Ga morphism, annihilation of a Hopf ideal is equivalent
to annihilation by the tangent. This requires the Hopf-ideal condition. -/
theorem gaMorphism_kills_hopfIdeal_iff
    (φ : B →ₐc[K] SymmetricAlgebra K K) (I : TauCeti.HopfIdeal K B) :
    (∀ b ∈ I, φ b = 0) ↔ (∀ b ∈ I, gaAffineGroupTangent φ b = 0) := by
  constructor
  · intro h b hb
    apply (TauCeti.Bialgebra.CounitAlgebra.algEquivSelf K B K).injective
    rw [map_zero, gaAffineGroupTangent, gaOriginDerivation_comp_apply,
      h b hb, map_zero, Polynomial.coeff_zero]
  · intro h b hb
    let q := (TauCeti.CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B) I).hom
    have hq : Function.Surjective q :=
      TauCeti.CommHopfAlgCat.mkQuotient_surjective (CommHopfAlgCat.of K B) I
    have hd : ∀ a, q a = 0 → gaAffineGroupTangent φ a = 0 := by
      intro a ha
      exact h a ((TauCeti.CommHopfAlgCat.mkQuotient_eq_zero_iff
        (CommHopfAlgCat.of K B) I a).mp ha)
    exact GaMorphism.kills_kernel_of_tangent_factors q φ
      (surjectiveTangentDescend q hq (gaAffineGroupTangent φ) hd)
      (surjectiveTangentDescend_comp q hq (gaAffineGroupTangent φ) hd).symm b
      ((TauCeti.CommHopfAlgCat.mkQuotient_eq_zero_iff
        (CommHopfAlgCat.of K B) I b).mpr hb)

/-- The defining universal property of the generated subgroup, expressed
entirely in terms of the generating tangent derivations. -/
theorem le_gaGeneratedHopfIdeal_iff_tangents
    {ι : Type v} (f : ι → B →ₐc[K] SymmetricAlgebra K K)
    (I : TauCeti.HopfIdeal K B) :
    I ≤ gaGeneratedHopfIdeal f ↔
      ∀ i b, b ∈ I → gaAffineGroupTangent (f i) b = 0 := by
  have hiff := TauCeti.CommHopfAlgCat.le_commonKernelHopfIdeal_iff
    (fun i => CommHopfAlgCat.ofHom (f i)) I
  constructor
  · intro h i
    apply (gaMorphism_kills_hopfIdeal_iff (f i) I).mp
    exact fun b hb => hiff.mp h i hb
  · intro h
    apply hiff.mpr
    intro i b hb
    exact (gaMorphism_kills_hopfIdeal_iff (f i) I).mpr (h i) b hb

end ReductiveGroups
