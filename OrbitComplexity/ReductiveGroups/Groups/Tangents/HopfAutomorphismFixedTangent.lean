import OrbitComplexity.ReductiveGroups.Groups.Hopf.HopfAutomorphismFixedSubgroup
import OrbitComplexity.ReductiveGroups.Groups.Tangents.TangentIdealSpan
import OrbitComplexity.ReductiveGroups.Groups.Tangents.SurjectiveTangentDescent

/-!
# Hopf Automorphism Fixed Tangent

The tangent image of the common fixed subgroup is exactly the
common fixed subspace of the differentials of its defining automorphisms. -/

noncomputable section
namespace ReductiveGroups

variable {K B : Type*} [Field K] [CommRing B] [HopfAlgebra K B] {ι : Type*}

/-- The original tangent belongs to the fixed-subgroup tangent
image exactly when its evaluations are fixed by the given automorphisms. -/
theorem tangent_mem_hopfAutomorphismFixed_iff
    (e : ι → B ≃ₐc[K] B)
    (d : Derivation K B (TauCeti.Bialgebra.CounitAlgebra K B K)) :
    d ∈ (TauCeti.derivationCompLieHom (B := K)
      (TauCeti.CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B)
        (hopfAutomorphismFixedHopfIdeal e)).hom).range ↔
      ∀ i b, d (e i b) = d b := by
  rw [tangent_mem_range_iff_kills_kernel _
    (TauCeti.CommHopfAlgCat.mkQuotient_surjective
      (CommHopfAlgCat.of K B) (hopfAutomorphismFixedHopfIdeal e))]
  have hq (a : B) :
      (TauCeti.CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B)
        (hopfAutomorphismFixedHopfIdeal e)).hom a = 0 ↔
          a ∈ (hopfAutomorphismFixedHopfIdeal e).toIdeal :=
    TauCeti.CommHopfAlgCat.mkQuotient_eq_zero_iff (CommHopfAlgCat.of K B)
      (hopfAutomorphismFixedHopfIdeal e) a
  simp only [hq]
  have hS (b : B) (hb : b ∈ hopfAutomorphismDifferenceSet e) :
      algebraMap B (TauCeti.Bialgebra.CounitAlgebra K B K) b = 0 := by
    have hmem : b ∈ hopfAutomorphismFixedHopfIdeal e := by
      rw [← TauCeti.HopfIdeal.mem_toIdeal, hopfAutomorphismFixedHopfIdeal_toIdeal]
      exact Ideal.subset_span hb
    rw [TauCeti.Bialgebra.CounitAlgebra.algebraMap_apply,
      (hopfAutomorphismFixedHopfIdeal e).counit_eq_zero hmem, map_zero]
    rfl
  change (∀ b ∈ (hopfAutomorphismFixedHopfIdeal e).toIdeal, d b = 0) ↔ _
  rw [hopfAutomorphismFixedHopfIdeal_toIdeal, hopfAutomorphismDifferenceIdeal,
    tangent_vanishes_idealSpan_iff _ hS]
  constructor
  · intro hd i b
    have h := hd (e i b - b) ⟨i, b, rfl⟩
    simpa only [map_sub, sub_eq_zero] using h
  · intro hd b hb
    obtain ⟨i, a, rfl⟩ := hb
    rw [map_sub, hd, sub_self]

/-- The same equality expressed by the tangent differential. -/
theorem HopfAutomorphismFixedTangent.hopfAutomorphismFixed_iff_differential
    (e : ι → B ≃ₐc[K] B)
    (d : Derivation K B (TauCeti.Bialgebra.CounitAlgebra K B K)) :
    d ∈ (TauCeti.derivationCompLieHom (B := K)
      (TauCeti.CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B)
        (hopfAutomorphismFixedHopfIdeal e)).hom).range ↔
      ∀ i, TauCeti.derivationComp (B := K) (e i).toBialgHom d = d := by
  rw [tangent_mem_hopfAutomorphismFixed_iff]
  constructor
  · intro hd i
    ext b
    change d (e i b) = d b
    exact hd i b
  · intro hd i b
    exact congrArg (fun f : Derivation K B
      (TauCeti.Bialgebra.CounitAlgebra K B K) => f b) (hd i)

end ReductiveGroups
