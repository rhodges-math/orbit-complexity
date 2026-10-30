import OrbitComplexity.ReductiveGroups.Groups.GaCoordinates.GaConjugate

/-!
# Tangents of conjugated additive subgroups

Precomposition of an additive-group coordinate map with conjugation differentiates
to the adjoint transform of its tangent vector.
-/

noncomputable section
namespace ReductiveGroups
open TauCeti
variable {K B : Type*} [Field K] [CommRing B] [HopfAlgebra K B]

/-- Conjugating an additive subgroup conjugates its tangent by the adjoint action. -/
theorem gaTangent_comp_conjugation (x : B →ₐc[K] SymmetricAlgebra K K)
    (g : WithConv (B →ₐ[K] K)) :
    gaAffineGroupTangent (x.comp (affineGroupConjugationBialgHom g)) =
      affineGroupAdjointLieEquiv g (gaAffineGroupTangent x) := by
  rw [gaAffineGroupTangent, derivationComp_comp, LinearMap.comp_apply,
    DerivationComp.conjugation]
  rfl

end ReductiveGroups
