import OrbitComplexity.ReductiveGroups.Groups.RootCoordinates.BorelRootGeneration
import OrbitComplexity.ReductiveGroups.Groups.Borel.BorelCandidateBaseChange
import OrbitComplexity.ReductiveGroups.Groups.Tori.TorusGaLieSolvableCandidate

/-!
# Borel Solvable Root Saturation

Maximality of the fixed Borel forces every additive subgroup
whose tangent lies in a solvable enlargement of its tangent to lie in that
same Borel. Nonidentity character vectors have the required integration. -/

noncomputable section
namespace ReductiveGroups
open TauCeti CategoryTheory

universe u
variable {K B ι : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  [CommRing B] [HopfAlgebra K B] [Algebra.FiniteType K B] [Finite ι]

local notation "𝔤" => Derivation K B (TauCeti.Bialgebra.CounitAlgebra K B K)

/-- The equality is

```lean
∀ a ∈ J, x a = 0
```
-/
theorem BorelSolvableRootSaturation.kills_of_solvable_tangent_enlargement
    (I J : HopfIdeal K B) (hJI : J ≤ I)
    (hI : HopfIdeal.IsMaximalTorus K (CommHopfAlgCat.of K B) I)
    (hJ : HopfIdeal.IsBorel K (CommHopfAlgCat.of K B) J)
    (π : B →ₐc[K] MonoidAlgebra K (Multiplicative (ι →₀ ℤ)))
    (hπ : Function.Surjective π)
    (hker : ∀ a : B, π a = 0 ↔ a ∈ I.toIdeal)
    (hB : reductiveCommHopfAlgProperty K (FiniteTypeCommHopfAlgCat.of K B))
    (S : LieSubalgebra K 𝔤) [LieAlgebra.IsSolvable S]
    (hJS : (derivationCompLieHom (B := K)
      (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B) J).hom).range ≤ S)
    (x : B →ₐc[K] SymmetricAlgebra K K) (hx : gaAffineGroupTangent x ∈ S) :
    ∀ a ∈ J, x a = 0 := by
  let y : Option (borelRootVectorIndex J π) → B →ₐc[K] SymmetricAlgebra K K
    | none => x
    | some r => borelRootVectorGa J π hπ r
  let Q := CommHopfAlgCat.commonKernelHopfIdeal (torusGaGeneratorFamily π y)
  have hT : diagonalizableTangentImage π ≤ S := by
    intro d hd
    apply hJS
    apply (tangent_mem_hopfQuotient_iff J d).mpr
    intro a ha
    obtain ⟨t, rfl⟩ := hd
    change t (π a) = 0
    rw [(hker a).2 (hJI ha), map_zero]
  have hy : ∀ j, gaAffineGroupTangent (y j) ∈ S := by
    intro j
    cases j with
    | none => exact hx
    | some r =>
        change gaAffineGroupTangent (borelRootVectorGa J π hπ r) ∈ S
        rw [borelRootVectorGa_tangent]
        exact hJS r.2.property.2.2
  obtain ⟨V, n, b, hρ⟩ :=
    TauCeti.Comodule.exists_coordinateBialgHom_surjective (k := K) (H := B)
  have hQ : HopfIdeal.IsBorelCandidate K (FiniteTypeCommHopfAlgCat.of K B) Q :=
    TorusGaGenerated.borelCandidate_of_solvable_tangents π hπ y n
      (TauCeti.Comodule.coordinateBialgHom (H := B) b) hρ S hT hy
  have hQJ : Q ≤ J := by
    rw [← borel_commonKernelRootGenerators_eq I J hJI hI hJ π hπ hker hB]
    apply (CommHopfAlgCat.le_commonKernelHopfIdeal_iff
      (borelRootGeneratorFamily J π hπ) Q).mpr
    intro j a ha
    cases j with
    | none =>
        exact CommHopfAlgCat.commonKernelHopfIdeal_toIdeal_le_ker
          (torusGaGeneratorFamily π y) none ha
    | some r =>
        exact CommHopfAlgCat.commonKernelHopfIdeal_toIdeal_le_ker
          (torusGaGeneratorFamily π y) (some (some r)) ha
  have hJQ : J ≤ Q := borel_minimal_candidate_of_isAlgClosed
    (FiniteTypeCommHopfAlgCat.of K B) J Q hJ hQJ hQ
  intro a ha
  exact CommHopfAlgCat.commonKernelHopfIdeal_toIdeal_le_ker
    (torusGaGeneratorFamily π y) (some none) (hJQ ha)

/-- The equality is

```lean
d ∈ (derivationCompLieHom (B := K)
      (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B) J).hom).range
```
-/
theorem BorelSolvableRootSaturation.mem_of_solvable_tangent_enlargement
    (I J : HopfIdeal K B) (hJI : J ≤ I)
    (hI : HopfIdeal.IsMaximalTorus K (CommHopfAlgCat.of K B) I)
    (hJ : HopfIdeal.IsBorel K (CommHopfAlgCat.of K B) J)
    (π : B →ₐc[K] MonoidAlgebra K (Multiplicative (ι →₀ ℤ)))
    (hπ : Function.Surjective π)
    (hker : ∀ a : B, π a = 0 ↔ a ∈ I.toIdeal)
    (hB : reductiveCommHopfAlgProperty K (FiniteTypeCommHopfAlgCat.of K B))
    (S : LieSubalgebra K 𝔤) [LieAlgebra.IsSolvable S]
    (hJS : (derivationCompLieHom (B := K)
      (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B) J).hom).range ≤ S)
    (α : Multiplicative (ι →₀ ℤ)) (hα : α ≠ 1) (d : 𝔤)
    (hd : d ∈ affineGroupCharacterWeightSpace π α) (hdS : d ∈ S) :
    d ∈ (derivationCompLieHom (B := K)
      (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B) J).hom).range := by
  obtain ⟨x, hx, _⟩ := CharacterRootIntegration.existsUnique_of_latticeCharacterWeight π hπ α hα d
    hd
  have hxS : gaAffineGroupTangent x ∈ S := hx ▸ hdS
  have hkill := BorelSolvableRootSaturation.kills_of_solvable_tangent_enlargement
    I J hJI hI hJ π hπ hker hB S hJS x hxS
  apply (tangent_mem_hopfQuotient_iff J d).mpr
  rw [← hx]
  exact (gaMorphism_kills_hopfIdeal_iff x J).mp hkill

end ReductiveGroups
