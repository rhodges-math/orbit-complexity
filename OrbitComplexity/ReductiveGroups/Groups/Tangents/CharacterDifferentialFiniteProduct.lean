import OrbitComplexity.ReductiveGroups.Groups.Diagonal.DiagonalizableTangentImage

/-!
# Character Differential Finite Product

Finite product character differentiation on a diagonalizable
group. -/

noncomputable section
namespace ReductiveGroups

variable {K M : Type*} [Field K] [CommGroup M]

private def characterDifferentialMonoidHom :
    M →* Multiplicative
      (Derivation K (MonoidAlgebra K M)
        (TauCeti.Bialgebra.CounitAlgebra K (MonoidAlgebra K M) K) →ₗ[K] K) where
  toFun α := Multiplicative.ofAdd (characterDifferential α)
  map_one' := by simp
  map_mul' α β := by simp [characterDifferential_mul]

/-- The differential of a finite character product is the natural-number
weighted sum of the differentials. -/
theorem characterDifferential_prod_pow
    {κ : Type*} [Fintype κ] (χ : κ → M) (m : κ → ℕ) :
    characterDifferential (K := K) (∏ j, χ j ^ m j) =
      ∑ j, m j • characterDifferential (K := K) (χ j) := by
  have h := map_prod (characterDifferentialMonoidHom (K := K) (M := M))
    (fun j : κ => χ j ^ m j) Finset.univ
  simp only [map_pow] at h
  exact congrArg Multiplicative.toAdd h

end ReductiveGroups
