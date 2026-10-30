import OrbitComplexity.ReductiveGroups.Groups.Characters.CharacterNonzeroRootIndex
import OrbitComplexity.ReductiveGroups.Groups.Reductive.ReductiveTorusRootSystem
import OrbitComplexity.ReductiveGroups.Lie.Cartan.CentralRadicalRootMultiplicity

/-!
# Reductive Character Roots

Root multiplicity for the adjoint characters of the original
maximal torus. Geometric reductivity and maximality discharge the Lie
hypotheses internally. -/

noncomputable section
namespace ReductiveGroups

universe u
variable {K B ι : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  [CommRing B] [HopfAlgebra K B] [Algebra.FiniteType K B] [Finite ι]

local notation "𝔤" => Derivation K B (TauCeti.Bialgebra.CounitAlgebra K B K)

/-- Original nonidentity adjoint characters index the roots of the
center quotient. The required Cartan properties come from the original
maximal torus and geometric reductivity,. -/
def ReductiveCharacterRoots.characterCenterQuotientRootEquiv
    (I : TauCeti.HopfIdeal K B)
    (hI : TauCeti.HopfIdeal.IsMaximalTorus K (CommHopfAlgCat.of K B) I)
    (π : B →ₐc[K] MonoidAlgebra K (Multiplicative (ι →₀ ℤ)))
    (hπ : Function.Surjective π)
    (hker : ∀ a : B, π a = 0 ↔ a ∈ I.toIdeal)
    (hB : TauCeti.reductiveCommHopfAlgProperty K
      (TauCeti.FiniteTypeCommHopfAlgCat.of K B)) :
    let _ := finiteTypeAffineGroup_tangent_finite (K := K) (B := B)
    let _ := MaximalTorusLieCartan.maximalTorus_coordinateTangent_isCartan I hI π hπ hker hB
    let _ := ReductiveTorusRootSystem.coordinateCenterQuotient_isCartan I hI π hπ hker hB
    {α : Multiplicative (ι →₀ ℤ) // affineGroupCharacterWeightSpace π α ≠ ⊥ ∧ α ≠ 1} ≃
      (centerQuotientCartan (diagonalizableTangentImage π)).root := by
  classical
  let _ := finiteTypeAffineGroup_tangent_finite (K := K) (B := B)
  let _ := MaximalTorusLieCartan.maximalTorus_coordinateTangent_isCartan I hI π hπ hker hB
  let _ := ReductiveTorusRootSystem.coordinateCenterQuotient_isCartan I hI π hπ hker hB
  exact ((nonidentityCharacterLieWeightEquiv π hπ).trans
    (nonzeroCenterQuotientWeightEquiv (diagonalizableTangentImage π))).trans
      (Equiv.subtypeEquivRight fun ψ => by simp [LieSubalgebra.root])

/-- Under the root correspondence, evaluation on the image of the original
torus tangent is exactly differentiation of the original character. -/
theorem ReductiveCharacterCenterQuotientRootEquiv.apply_map
    (I : TauCeti.HopfIdeal K B)
    (hI : TauCeti.HopfIdeal.IsMaximalTorus K (CommHopfAlgCat.of K B) I)
    (π : B →ₐc[K] MonoidAlgebra K (Multiplicative (ι →₀ ℤ)))
    (hπ : Function.Surjective π)
    (hker : ∀ a : B, π a = 0 ↔ a ∈ I.toIdeal)
    (hB : TauCeti.reductiveCommHopfAlgProperty K
      (TauCeti.FiniteTypeCommHopfAlgCat.of K B))
    (α : {α : Multiplicative (ι →₀ ℤ) //
      affineGroupCharacterWeightSpace π α ≠ ⊥ ∧ α ≠ 1})
    (t : diagonalizableTangentImage π) :
    (ReductiveCharacterRoots.characterCenterQuotientRootEquiv I hI π hπ hker hB α).val
      (centerQuotientCartanMap (diagonalizableTangentImage π) t) =
        characterDifferentialOnImage π hπ α.val t := by
  let _ := finiteTypeAffineGroup_tangent_finite (K := K) (B := B)
  let _ := MaximalTorusLieCartan.maximalTorus_coordinateTangent_isCartan I hI π hπ hker hB
  change (nonzeroCenterQuotientWeightEquiv (diagonalizableTangentImage π)
    (nonidentityCharacterLieWeightEquiv π hπ α)).val
      (centerQuotientCartanMap (diagonalizableTangentImage π) t) = _
  rw [NonzeroCenterQuotientWeightEquiv.apply_map,
    nonidentityCharacterLieWeightEquiv_apply]

/-- Every occurring nonidentity character of the maximal torus
has a one-dimensional adjoint character space. -/
theorem ReductiveCharacterRoots.characterWeightSpace_finrank_eq_one
    (I : TauCeti.HopfIdeal K B)
    (hI : TauCeti.HopfIdeal.IsMaximalTorus K (CommHopfAlgCat.of K B) I)
    (π : B →ₐc[K] MonoidAlgebra K (Multiplicative (ι →₀ ℤ)))
    (hπ : Function.Surjective π)
    (hker : ∀ a : B, π a = 0 ↔ a ∈ I.toIdeal)
    (hB : TauCeti.reductiveCommHopfAlgProperty K
      (TauCeti.FiniteTypeCommHopfAlgCat.of K B))
    (α : Multiplicative (ι →₀ ℤ)) (hα : α ≠ 1)
    (hocc : affineGroupCharacterWeightSpace π α ≠ ⊥) :
    Module.finrank K (affineGroupCharacterWeightSpace π α) = 1 := by
  let _ := finiteTypeAffineGroup_tangent_finite (K := K) (B := B)
  let _ := reductive_tangent_hasCentralRadical hB
  let _ := MaximalTorusLieCartan.maximalTorus_coordinateTangent_isCartan I hI π hπ hker hB
  let χ := nonidentityCharacterLieWeightEquiv π hπ ⟨α, hocc, hα⟩
  have heval : (χ.val : diagonalizableTangentImage π → K) =
      characterDifferentialOnImage π hπ α := by
    funext t
    exact nonidentityCharacterLieWeightEquiv_apply π hπ ⟨α, hocc, hα⟩ t
  rw [AffineGroupCharacterWeightSpace.eq_rootSpace π hπ α, ← heval]
  exact centralRadical_finrank_rootSpace_eq_one (diagonalizableTangentImage π)
    χ.val χ.property

end ReductiveGroups
