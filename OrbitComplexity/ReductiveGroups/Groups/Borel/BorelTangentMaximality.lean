import OrbitComplexity.ReductiveGroups.Groups.Borel.BorelSolvableRootSaturation

/-!
# Borel Tangent Maximality

The tangent image of the original Borel is maximal among solvable Lie
subalgebras of the original reductive tangent algebra. The proof integrates
only nonidentity character vectors, then uses geometric Borel
maximality and the Cartan weight decomposition. -/

noncomputable section
namespace ReductiveGroups
open TauCeti CategoryTheory

universe u
variable {K B ι : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  [CommRing B] [HopfAlgebra K B] [Algebra.FiniteType K B] [Finite ι]

local notation "𝔤" => Derivation K B (TauCeti.Bialgebra.CounitAlgebra K B K)

/-- The equality is

```lean
S = (derivationCompLieHom (B := K)
      (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B) J).hom).range
```
-/
theorem borel_tangentImage_maximal_solvable
    (I J : HopfIdeal K B) (hJI : J ≤ I)
    (hI : HopfIdeal.IsMaximalTorus K (CommHopfAlgCat.of K B) I)
    (hJ : HopfIdeal.IsBorel K (CommHopfAlgCat.of K B) J)
    (π : B →ₐc[K] MonoidAlgebra K (Multiplicative (ι →₀ ℤ)))
    (hπ : Function.Surjective π)
    (hker : ∀ a : B, π a = 0 ↔ a ∈ I.toIdeal)
    (hB : reductiveCommHopfAlgProperty K (FiniteTypeCommHopfAlgCat.of K B))
    (S : LieSubalgebra K 𝔤) [LieAlgebra.IsSolvable S]
    (hJS : (derivationCompLieHom (B := K)
      (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B) J).hom).range ≤ S) :
    S = (derivationCompLieHom (B := K)
      (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B) J).hom).range := by
  let _ := finiteTypeAffineGroup_tangent_finite (K := K) (B := B)
  let _ := MaximalTorusLieCartan.maximalTorus_coordinateTangent_isCartan I hI π hπ hker hB
  let H := diagonalizableTangentImage π
  let D := (derivationCompLieHom (B := K)
    (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B) J).hom).range
  have hHD : H ≤ D := by
    intro d hd
    apply (tangent_mem_hopfQuotient_iff J d).mpr
    intro a ha
    obtain ⟨t, rfl⟩ := hd
    change t (π a) = 0
    rw [(hker a).2 (hJI ha), map_zero]
  have hHS : H ≤ S := hHD.trans hJS
  have hSD : cartanStableSubmodule H S hHS ≤ cartanStableSubmodule H D hHD := by
    rw [CartanStableSubmodule.eq_iSup_inf_rootSpace H S hHS]
    refine iSup_le fun χ => ?_
    intro d hd
    have hdS : (d : 𝔤) ∈ S := hd.1
    have hdroot : (d : 𝔤) ∈ LieAlgebra.rootSpace H χ := hd.2
    by_cases hχ : χ.IsZero
    · have hz : LieAlgebra.rootSpace H χ = H.toLieSubmodule := by
        simpa only [hχ.eq] using (LieAlgebra.rootSpace_zero_eq K 𝔤 H)
      rw [hz] at hdroot
      exact hHD hdroot
    · obtain ⟨α, ⟨_, hαχ⟩, _⟩ := existsUnique_character_of_lieWeight π hπ χ
      have hα : α ≠ 1 := by
        intro hα1
        apply hχ
        change (χ : H → K) = 0
        rw [hαχ, hα1, characterDifferentialOnImage_one]
        rfl
      have hdW : (d : 𝔤) ∈ affineGroupCharacterWeightSpace π α := by
        rw [AffineGroupCharacterWeightSpace.eq_rootSpace π hπ α]
        change (d : 𝔤) ∈ LieAlgebra.rootSpace H
          (characterDifferentialOnImage π hπ α)
        exact hαχ ▸ hdroot
      exact BorelSolvableRootSaturation.mem_of_solvable_tangent_enlargement
        I J hJI hI hJ π hπ hker hB S hJS α hα d hdW hdS
  apply le_antisymm ?_ hJS
  intro d hd
  exact hSD hd

omit [Finite ι] in
/-- Coordinate-free form for the fixed maximal torus and Borel.
The split coordinate map used in the proof is constructed internally. -/
theorem BorelTangentMaximality.maximal_solvable_coordinateFree
    (I J : HopfIdeal K B) (hJI : J ≤ I)
    (hI : HopfIdeal.IsMaximalTorus K (CommHopfAlgCat.of K B) I)
    (hJ : HopfIdeal.IsBorel K (CommHopfAlgCat.of K B) J)
    (hB : reductiveCommHopfAlgProperty K (FiniteTypeCommHopfAlgCat.of K B))
    (S : LieSubalgebra K 𝔤) [LieAlgebra.IsSolvable S]
    (hJS : (derivationCompLieHom (B := K)
      (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B) J).hom).range ≤ S) :
    S = (derivationCompLieHom (B := K)
      (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B) J).hom).range := by
  obtain ⟨r, π, hπ, hker, _⟩ := TorusQuotientTangent.exists_tangentImage
    (FiniteTypeCommHopfAlgCat.of K B) I hI
  exact borel_tangentImage_maximal_solvable I J hJI hI hJ π hπ hker hB S hJS

end ReductiveGroups
