import OrbitComplexity.ReductiveGroups.Groups.Reductive.ReductiveCharacterRoots
import OrbitComplexity.ReductiveGroups.Lie.Cartan.CenterQuotientSubalgebra

/-!
# Character Root Subalgebra Containment

Containment of the original torus-character root space in an original
Cartan-containing subalgebra is equivalent to containment of its corresponding
root space after the center quotient. -/

noncomputable section
namespace ReductiveGroups
open LieAlgebra LieModule

universe u
variable {K B ι : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  [CommRing B] [HopfAlgebra K B] [Algebra.FiniteType K B] [Finite ι]

local notation "𝔤" => Derivation K B (TauCeti.Bialgebra.CounitAlgebra K B K)

/-- A Cartan-containing subalgebra contains a torus-character root space exactly when
its image in the center quotient contains the corresponding root space. -/
theorem characterRoot_subalgebra_containment_iff
    (I : TauCeti.HopfIdeal K B)
    (hI : TauCeti.HopfIdeal.IsMaximalTorus K (CommHopfAlgCat.of K B) I)
    (π : B →ₐc[K] MonoidAlgebra K (Multiplicative (ι →₀ ℤ)))
    (hπ : Function.Surjective π)
    (hker : ∀ a : B, π a = 0 ↔ a ∈ I.toIdeal)
    (hB : TauCeti.reductiveCommHopfAlgProperty K
      (TauCeti.FiniteTypeCommHopfAlgCat.of K B))
    (S : LieSubalgebra K 𝔤) (hHS : diagonalizableTangentImage π ≤ S)
    (α : {α : Multiplicative (ι →₀ ℤ) //
      affineGroupCharacterWeightSpace π α ≠ ⊥ ∧ α ≠ 1}) :
    letI := finiteTypeAffineGroup_tangent_finite (K := K) (B := B)
    letI := MaximalTorusLieCartan.maximalTorus_coordinateTangent_isCartan I hI π hπ hker hB
    letI := ReductiveTorusRootSystem.coordinateCenterQuotient_isCartan I hI π hπ hker hB
    (∀ z : 𝔤 ⧸ LieAlgebra.center K 𝔤,
      z ∈ rootSpace (centerQuotientCartan (diagonalizableTangentImage π))
        (ReductiveCharacterRoots.characterCenterQuotientRootEquiv I hI π hπ hker hB α).val →
      z ∈ S.map (centerQuotientLieHom (K := K))) ↔
    (∀ d : 𝔤, d ∈ affineGroupCharacterWeightSpace π α.val → d ∈ S) := by
  let _ := finiteTypeAffineGroup_tangent_finite (K := K) (B := B)
  let _ := MaximalTorusLieCartan.maximalTorus_coordinateTangent_isCartan I hI π hπ hker hB
  let _ := ReductiveTorusRootSystem.coordinateCenterQuotient_isCartan I hI π hπ hker hB
  let H := diagonalizableTangentImage π
  let β := ReductiveCharacterRoots.characterCenterQuotientRootEquiv I hI π hπ hker hB α
  have heval : (fun h : H => β.val (centerQuotientCartanMap H h)) =
      (characterDifferentialOnImage π hπ α.val : H → K) := by
    funext h
    exact ReductiveCharacterCenterQuotientRootEquiv.apply_map I hI π hπ hker hB α h
  change (∀ z : 𝔤 ⧸ LieAlgebra.center K 𝔤,
      z ∈ rootSpace (centerQuotientCartan H) β.val →
      z ∈ S.map (centerQuotientLieHom (K := K))) ↔ _
  rw [centerQuotient_rootSpace_le_map_iff H S hHS, heval]
  rw [AffineGroupCharacterWeightSpace.eq_rootSpace π hπ α.val]
  rfl

end ReductiveGroups
