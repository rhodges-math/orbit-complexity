import OrbitComplexity.ReductiveGroups.Groups.GaCoordinates.GaTangentDeterminesMorphism
import OrbitComplexity.ReductiveGroups.Groups.Hopf.SurjectiveBialgebraDescent

/-!
# Ga Morphism Descent

Integrate a tangent factorization by descending the Ga morphism. -/

noncomputable section
namespace ReductiveGroups

variable {K A B : Type*} [Field K] [CharZero K]
  [CommRing A] [HopfAlgebra K A] [CommRing B] [HopfAlgebra K B]

/-- A Ga morphism whose tangent factors through a closed affine subgroup
descends uniquely to that original subgroup, with the specified tangent. -/
theorem GaMorphismDescent.existsUnique_of_tangent_factor
    (ρ : A →ₐc[K] B) (hρ : Function.Surjective ρ)
    (φ : A →ₐc[K] SymmetricAlgebra K K)
    (d : Derivation K B (TauCeti.Bialgebra.CounitAlgebra K B K))
    (hφ : gaAffineGroupTangent φ = TauCeti.derivationComp (B := K) ρ d) :
    ∃! ψ : B →ₐc[K] SymmetricAlgebra K K,
      ψ.comp ρ = φ ∧ gaAffineGroupTangent ψ = d := by
  have hker := GaMorphism.kills_kernel_of_tangent_factors ρ φ d hφ
  let ψ := surjectiveBialgebraDescend ρ hρ φ hker
  have hcomp : ψ.comp ρ = φ := surjectiveBialgebraDescend_comp ρ hρ φ hker
  have htangent : gaAffineGroupTangent ψ = d := by
    apply TauCeti.derivationComp_injective_of_surjective ρ hρ
    have hchain : TauCeti.derivationComp (B := K) ρ (gaAffineGroupTangent ψ) =
        gaAffineGroupTangent φ := by
      rw [gaAffineGroupTangent, gaAffineGroupTangent]
      have h := congrArg (fun f => f (gaOriginDerivation K))
        (TauCeti.derivationComp_comp (B := K) ψ ρ)
      simpa only [LinearMap.comp_apply, hcomp] using h.symm
    exact hchain.trans hφ
  refine ⟨ψ, ⟨hcomp, htangent⟩, ?_⟩
  intro ψ' hψ'
  exact surjectiveBialgebraDescend_unique ρ hρ φ hker ψ' hψ'.1

end ReductiveGroups
