import OrbitComplexity.ReductiveGroups.Groups.Reductive.ReductiveCharacterRoots
import OrbitComplexity.ReductiveGroups.Groups.Generated.GaGeneratedTangentCriterion
import OrbitComplexity.ReductiveGroups.Groups.Tangents.ClosedSubgroupTangentInclusion

/-!
# Character Ga Subgroup Containment

A Ga map with a nonzero character-root tangent lies in an
original closed subgroup exactly when its whole character space lies in
that subgroup's tangent image. -/

noncomputable section
namespace ReductiveGroups

universe u
variable {K B ι : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  [CommRing B] [HopfAlgebra K B] [Algebra.FiniteType K B] [Finite ι]

local notation "𝔤" => Derivation K B (TauCeti.Bialgebra.CounitAlgebra K B K)

/-- The equivalence is

```lean
(∀ a ∈ J, x a = 0) ↔
      ∀ d : 𝔤, d ∈ affineGroupCharacterWeightSpace π α →
        d ∈ (TauCeti.derivationCompLieHom (B := K)
          (TauCeti.CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B) J).hom).range
```
-/
theorem CharacterGa.kills_iff_weightSpace_contained
    (I : TauCeti.HopfIdeal K B)
    (hI : TauCeti.HopfIdeal.IsMaximalTorus K (CommHopfAlgCat.of K B) I)
    (π : B →ₐc[K] MonoidAlgebra K (Multiplicative (ι →₀ ℤ)))
    (hπ : Function.Surjective π)
    (hker : ∀ a : B, π a = 0 ↔ a ∈ I.toIdeal)
    (hB : TauCeti.reductiveCommHopfAlgProperty K
      (TauCeti.FiniteTypeCommHopfAlgCat.of K B))
    (α : Multiplicative (ι →₀ ℤ)) (hα : α ≠ 1)
    (J : TauCeti.HopfIdeal K B) (x : B →ₐc[K] SymmetricAlgebra K K)
    (hx : gaAffineGroupTangent x ∈ affineGroupCharacterWeightSpace π α)
    (hx0 : gaAffineGroupTangent x ≠ 0) :
    (∀ a ∈ J, x a = 0) ↔
      ∀ d : 𝔤, d ∈ affineGroupCharacterWeightSpace π α →
        d ∈ (TauCeti.derivationCompLieHom (B := K)
          (TauCeti.CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B) J).hom).range := by
  have hocc : affineGroupCharacterWeightSpace π α ≠ ⊥ := by
    intro hbot
    exact hx0 (by simpa [hbot] using hx)
  have hspan := eq_span_singleton_of_mem_of_finrank_eq_one
    (ReductiveCharacterRoots.characterWeightSpace_finrank_eq_one I hI π hπ hker hB α hα hocc) hx hx0
  rw [gaMorphism_kills_hopfIdeal_iff x J, ← tangent_mem_hopfQuotient_iff J]
  constructor
  · intro hxJ d hd
    rw [hspan] at hd
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hd
    exact ((TauCeti.derivationCompLieHom (B := K)
      (TauCeti.CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B) J).hom).range).smul_mem c hxJ
  · intro h
    exact h _ hx

end ReductiveGroups
