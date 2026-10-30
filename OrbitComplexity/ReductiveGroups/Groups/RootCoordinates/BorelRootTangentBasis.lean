import OrbitComplexity.ReductiveGroups.Groups.Borel.BorelFiniteRootGenerators
import OrbitComplexity.ReductiveGroups.Groups.Unipotent.BorelRootUnipotentLieDecomposition

/-!
# Borel Root Tangent Basis

Finite independent root parameters span exactly the tangent of
the Borel's Ga-only subgroup. -/

noncomputable section
namespace ReductiveGroups

open TauCeti

universe u
variable {K B ι : Type u} [Field K] [CommRing B] [HopfAlgebra K B]
  [Algebra.FiniteType K B] [CharZero K]

local notation "𝔤" => Derivation K B (Bialgebra.CounitAlgebra K B K)
local notation "M" => Multiplicative (ι →₀ ℤ)

/-- Nonzero vectors in distinct character spaces are independent. -/
theorem BorelRootCharacterVectors.linearIndependent
    (J : HopfIdeal K B) (π : B →ₐc[K] MonoidAlgebra K M)
    (hπ : Function.Surjective π) (e : borelRootCharacterIndex J π → 𝔤)
    (he : ∀ α, e α ∈ affineGroupCharacterWeightSpace π α.val)
    (he0 : ∀ α, e α ≠ 0) : LinearIndependent K e := by
  have hi : iSupIndep (fun α : M => affineGroupCharacterWeightSpace π α) := by
    simp_rw [AffineGroupCharacterWeightSpace.eq_rootSpace π hπ]
    rw [LieSubmodule.iSupIndep_toSubmodule]
    exact (LieModule.iSupIndep_genWeightSpace K (diagonalizableTangentImage π) 𝔤).comp
      (DFunLike.coe_injective.comp (characterDifferentialOnImage_injective π hπ))
  exact (hi.comp (Subtype.val_injective (p := fun α : M => α ≠ 1 ∧
    (derivationCompLieHom (B := K)
      (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B) J).hom).range.toSubmodule ⊓
        affineGroupCharacterWeightSpace π α ≠ ⊥))).linearIndependent _ he he0

/-- The finite root generators can be chosen with independent
tangents spanning the exact Ga-only Borel tangent. This is a linear
coordinate theorem; the ordered product isomorphism is
`exists_borelRootOrderedChart` (`Groups/BorelRootOrderedChart.lean`). -/
theorem exists_borelRootGenerators_tangent_basis
    [IsAlgClosed K] [Finite ι]
    (I J : HopfIdeal K B) (hJI : J ≤ I)
    (hI : HopfIdeal.IsMaximalTorus K (CommHopfAlgCat.of K B) I)
    (hJ : HopfIdeal.IsBorel K (CommHopfAlgCat.of K B) J)
    (π : B →ₐc[K] MonoidAlgebra K M) (hπ : Function.Surjective π)
    (hker : ∀ a : B, π a = 0 ↔ a ∈ I.toIdeal)
    (hB : reductiveCommHopfAlgProperty K (FiniteTypeCommHopfAlgCat.of K B)) :
    ∃ x : borelRootCharacterIndex J π → B →ₐc[K] SymmetricAlgebra K K,
      (∀ α, gaAffineGroupTangent (x α) ≠ 0 ∧
        gaAffineGroupTangent (x α) ∈ affineGroupCharacterWeightSpace π α.val ∧
        gaAffineGroupTangent (x α) ∈ (derivationCompLieHom (B := K)
          (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B) J).hom).range) ∧
      LinearIndependent K (fun α => gaAffineGroupTangent (x α)) ∧
      Submodule.span K (Set.range (fun α => gaAffineGroupTangent (x α))) =
        (derivationCompLieHom (B := K)
          (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B)
            (borelRootUnipotentHopfIdeal J π hπ)).hom).range.toSubmodule ∧
      gaGeneratedHopfIdeal x = borelRootUnipotentHopfIdeal J π hπ := by
  classical
  obtain ⟨x, hx, hgen⟩ := exists_finite_borelRootGenerators I J hI π hπ hker hB
  refine ⟨x, hx, BorelRootCharacterVectors.linearIndependent J π hπ _
    (fun α => (hx α).2.1) (fun α => (hx α).1), ?_, hgen⟩
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro d ⟨α, rfl⟩
    have hm := gaGenerated_tangent_mem_range x α
    rwa [hgen] at hm
  · rw [BorelRootUnipotentTangent.eq_character_sum I J hJI hI hJ π hπ hker hB]
    refine iSup₂_le fun α hα => ?_
    intro d hd
    by_cases hd0 : d = 0
    · rw [hd0]
      exact Submodule.zero_mem _
    · have hocc : (derivationCompLieHom (B := K)
          (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B) J).hom).range.toSubmodule ⊓
            affineGroupCharacterWeightSpace π α ≠ ⊥ :=
        (Submodule.ne_bot_iff _).mpr ⟨d, hd, hd0⟩
      let β : borelRootCharacterIndex J π := ⟨α, hα, hocc⟩
      have hw : affineGroupCharacterWeightSpace π α ≠ ⊥ := by
        intro he
        exact hd0 (by simpa [he] using hd.2)
      have hspan := eq_span_singleton_of_mem_of_finrank_eq_one
        (ReductiveCharacterRoots.characterWeightSpace_finrank_eq_one I hI π hπ hker hB α hα hw)
        (hx β).2.1 (hx β).1
      have hm : d ∈ Submodule.span K {gaAffineGroupTangent (x β)} := by
        rw [← hspan]
        exact hd.2
      have hsub : ({gaAffineGroupTangent (x β)} : Set 𝔤) ⊆
          Set.range (fun γ => gaAffineGroupTangent (x γ)) :=
        Set.singleton_subset_iff.mpr ⟨β, rfl⟩
      exact Submodule.span_mono hsub hm

end ReductiveGroups
