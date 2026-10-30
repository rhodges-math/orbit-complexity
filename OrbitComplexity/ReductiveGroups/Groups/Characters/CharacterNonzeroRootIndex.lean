import OrbitComplexity.ReductiveGroups.Groups.Tangents.CharacterLieRootIndex

/-!
# Character Nonzero Root Index

Nonidentity occurring characters correspond exactly to nonzero
Lie weights, with the original character differential as evaluation. -/

noncomputable section
namespace ReductiveGroups

universe u
variable {K B ι : Type u} [Field K] [CharZero K] [CommRing B]
  [HopfAlgebra K B] [Algebra.FiniteType K B]

local notation "𝔤" => Derivation K B (TauCeti.Bialgebra.CounitAlgebra K B K)

/-- The equality is

```lean
occurringCharacterLieWeightEquiv π hπ α t =
      characterDifferentialOnImage π hπ α.val t
```
-/
@[simp] theorem occurringCharacterLieWeightEquiv_apply
    (π : B →ₐc[K] MonoidAlgebra K (Multiplicative (ι →₀ ℤ)))
    (hπ : Function.Surjective π)
    (α : {α : Multiplicative (ι →₀ ℤ) // affineGroupCharacterWeightSpace π α ≠ ⊥})
    (t : diagonalizableTangentImage π) :
    occurringCharacterLieWeightEquiv π hπ α t =
      characterDifferentialOnImage π hπ α.val t := rfl

/-- Restrict the character/weight correspondence to the nonidentity
characters and nonzero Lie weights.  -/
def nonidentityCharacterLieWeightEquiv
    (π : B →ₐc[K] MonoidAlgebra K (Multiplicative (ι →₀ ℤ)))
    (hπ : Function.Surjective π) :
    {α : Multiplicative (ι →₀ ℤ) // affineGroupCharacterWeightSpace π α ≠ ⊥ ∧ α ≠ 1} ≃
      {χ : LieModule.Weight K (diagonalizableTangentImage π) 𝔤 // χ.IsNonZero} := by
  let e := occurringCharacterLieWeightEquiv π hπ
  let F : {α : Multiplicative (ι →₀ ℤ) //
      affineGroupCharacterWeightSpace π α ≠ ⊥ ∧ α ≠ 1} →
      {χ : LieModule.Weight K (diagonalizableTangentImage π) 𝔤 // χ.IsNonZero} :=
    fun α => ⟨e ⟨α.val, α.property.1⟩, by
      intro hz
      have hz' : characterDifferentialOnImage π hπ α.val = 0 := by
        apply LinearMap.ext
        intro t
        exact congrFun hz t
      exact α.property.2 ((characterDifferentialOnImage_eq_zero_iff π hπ α.val).mp hz')⟩
  apply Equiv.ofBijective F
  constructor
  · intro α β hab
    apply Subtype.ext
    have he : e ⟨α.val, α.property.1⟩ = e ⟨β.val, β.property.1⟩ :=
      congrArg Subtype.val hab
    exact congrArg (fun a : {a : Multiplicative (ι →₀ ℤ) //
      affineGroupCharacterWeightSpace π a ≠ ⊥} => a.val) (e.injective he)
  · intro χ
    obtain ⟨α, ⟨hα, hχ⟩, _⟩ := existsUnique_character_of_lieWeight π hπ χ.val
    have hα1 : α ≠ 1 := by
      intro heq
      apply χ.property
      rw [heq] at hχ
      funext t
      change χ.val t = 0
      simpa only [characterDifferentialOnImage_one, LinearMap.zero_apply] using congrFun hχ t
    refine ⟨⟨α, hα, hα1⟩, ?_⟩
    apply Subtype.ext
    apply LieModule.Weight.ext
    intro t
    exact (congrFun hχ t).symm

/-- The equality is

```lean
(nonidentityCharacterLieWeightEquiv π hπ α).val t =
      characterDifferentialOnImage π hπ α.val t
```
-/
@[simp] theorem nonidentityCharacterLieWeightEquiv_apply
    (π : B →ₐc[K] MonoidAlgebra K (Multiplicative (ι →₀ ℤ)))
    (hπ : Function.Surjective π)
    (α : {α : Multiplicative (ι →₀ ℤ) //
      affineGroupCharacterWeightSpace π α ≠ ⊥ ∧ α ≠ 1})
    (t : diagonalizableTangentImage π) :
    (nonidentityCharacterLieWeightEquiv π hπ α).val t =
      characterDifferentialOnImage π hπ α.val t := rfl

end ReductiveGroups
