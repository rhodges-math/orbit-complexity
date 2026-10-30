import OrbitComplexity.ReductiveGroups.Groups.Unipotent.BorelRootUnipotentSubgroup
import OrbitComplexity.ReductiveGroups.Groups.Reductive.ReductiveCharacterRoots

/-!
# Borel Finite Root Generators

One nonzero root vector for each occurring Borel character suffices to
generate the same closed subgroup as the exhaustive root-vector family. -/

noncomputable section
namespace ReductiveGroups

open TauCeti

universe u
variable {K B ι : Type u} [Field K] [CommRing B] [HopfAlgebra K B]
  [Algebra.FiniteType K B]

local notation "𝔤" => Derivation K B (Bialgebra.CounitAlgebra K B K)
local notation "M" => Multiplicative (ι →₀ ℤ)

/-- Nonidentity characters having a nonzero vector in the fixed
subgroup tangent. In the Borel case these are precisely its positive roots. -/
abbrev borelRootCharacterIndex
    (J : HopfIdeal K B) (π : B →ₐc[K] MonoidAlgebra K M) :=
  {α : M // α ≠ 1 ∧
    (derivationCompLieHom (B := K)
      (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B) J).hom).range.toSubmodule ⊓
        affineGroupCharacterWeightSpace π α ≠ ⊥}

private theorem borelRootCharacter_weight_ne_bot
    (J : HopfIdeal K B) (π : B →ₐc[K] MonoidAlgebra K M)
    (α : borelRootCharacterIndex J π) : affineGroupCharacterWeightSpace π α.val ≠ ⊥ := by
  intro he
  apply α.property.2
  rw [he, inf_bot_eq]

/-- Only finitely many characters occur, even though the original exhaustive
family was indexed by all root vectors. -/
theorem finite_borelRootCharacterIndex [CharZero K]
    (J : HopfIdeal K B) (π : B →ₐc[K] MonoidAlgebra K M)
    (hπ : Function.Surjective π) : Finite (borelRootCharacterIndex J π) := by
  let _ := finiteTypeAffineGroup_tangent_finite (K := K) (B := B)
  let f : borelRootCharacterIndex J π →
      {α : M // affineGroupCharacterWeightSpace π α ≠ ⊥} :=
    fun α => ⟨α.val, borelRootCharacter_weight_ne_bot J π α⟩
  have hf : Function.Injective f := by
    intro α β hab
    apply Subtype.ext
    exact congrArg (fun a : {α : M // affineGroupCharacterWeightSpace π α ≠ ⊥} => a.val) hab
  exact Finite.of_injective
    (fun α => occurringCharacterLieWeightEquiv π hπ (f α))
    ((occurringCharacterLieWeightEquiv π hπ).injective.comp hf)

/-- Choose one nonzero additive root subgroup per occurring Borel
character. Its closed generated subgroup is unchanged.  -/
theorem exists_finite_borelRootGenerators
    [IsAlgClosed K] [CharZero K] [Finite ι]
    (I J : HopfIdeal K B)
    (hI : HopfIdeal.IsMaximalTorus K (CommHopfAlgCat.of K B) I)
    (π : B →ₐc[K] MonoidAlgebra K M) (hπ : Function.Surjective π)
    (hker : ∀ a : B, π a = 0 ↔ a ∈ I.toIdeal)
    (hB : reductiveCommHopfAlgProperty K (FiniteTypeCommHopfAlgCat.of K B)) :
    ∃ x : borelRootCharacterIndex J π → B →ₐc[K] SymmetricAlgebra K K,
      (∀ α, gaAffineGroupTangent (x α) ≠ 0 ∧
        gaAffineGroupTangent (x α) ∈ affineGroupCharacterWeightSpace π α.val ∧
        gaAffineGroupTangent (x α) ∈ (derivationCompLieHom (B := K)
          (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B) J).hom).range) ∧
      gaGeneratedHopfIdeal x = borelRootUnipotentHopfIdeal J π hπ := by
  classical
  have hex (α : borelRootCharacterIndex J π) : ∃ d : 𝔤,
      d ∈ (derivationCompLieHom (B := K)
        (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B) J).hom).range.toSubmodule ⊓
        affineGroupCharacterWeightSpace π α.val ∧ d ≠ 0 :=
    (Submodule.ne_bot_iff _).mp α.property.2
  choose e he he0 using hex
  let r (α : borelRootCharacterIndex J π) : borelRootVectorIndex J π :=
    ⟨α.val, ⟨e α, α.property.1, (he α).2, (he α).1⟩⟩
  let x (α : borelRootCharacterIndex J π) := borelRootVectorGa J π hπ (r α)
  have hx (α : borelRootCharacterIndex J π) : gaAffineGroupTangent (x α) = e α :=
    borelRootVectorGa_tangent J π hπ (r α)
  refine ⟨x, fun α => ?_, le_antisymm ?_ ?_⟩
  · rw [hx]
    exact ⟨he0 α, (he α).2, (he α).1⟩
  · apply (le_gaGeneratedHopfIdeal_iff_tangents (borelRootVectorGa J π hπ) _).mpr
    intro s a ha
    rw [borelRootVectorGa_tangent]
    by_cases hs0 : s.2.val = 0
    · rw [hs0]
      rfl
    · have hocc : (derivationCompLieHom (B := K)
          (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B) J).hom).range.toSubmodule ⊓
            affineGroupCharacterWeightSpace π s.1 ≠ ⊥ := by
        apply (Submodule.ne_bot_iff _).mpr
        exact ⟨s.2.val, ⟨s.2.property.2.2, s.2.property.2.1⟩, hs0⟩
      let α : borelRootCharacterIndex J π := ⟨s.1, s.2.property.1, hocc⟩
      have hspan := eq_span_singleton_of_mem_of_finrank_eq_one
        (ReductiveCharacterRoots.characterWeightSpace_finrank_eq_one I hI π hπ hker hB
          α.val α.property.1 (borelRootCharacter_weight_ne_bot J π α))
        (he α).2 (he0 α)
      have hs : s.2.val ∈ Submodule.span K {e α} := by
        rw [← hspan]
        exact s.2.property.2.1
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hs
      have hzero := gaGenerated_tangent_eq_zero_on_ideal x α a ha
      rw [hx] at hzero
      rw [← hc]
      change c • (e α) a = 0
      rw [hzero, smul_zero]
  · apply (le_gaGeneratedHopfIdeal_iff_tangents x _).mpr
    intro α a ha
    exact gaGenerated_tangent_eq_zero_on_ideal (borelRootVectorGa J π hπ) (r α) a ha

end ReductiveGroups
