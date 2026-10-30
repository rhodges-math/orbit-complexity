import OrbitComplexity.ReductiveGroups.Groups.Characters.CharacterRootIntegration
import OrbitComplexity.ReductiveGroups.Groups.Generated.GaGeneratedTangentCriterion
import OrbitComplexity.ReductiveGroups.Groups.Tangents.ClosedSubgroupIntersectionTangent
import OrbitComplexity.ReductiveGroups.Groups.Tangents.ClosedSubgroupTangentInclusion
import OrbitComplexity.ReductiveGroups.Groups.Tangents.CharacterLieRootIndex
import OrbitComplexity.ReductiveGroups.Groups.Diagonal.MaximalTorusLieCartan
import OrbitComplexity.ReductiveGroups.Lie.Solvable.SolvableCartanRootDecomposition
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.CommonKernel.Basic

/-!
# Borel Root Generated

Mixed original-torus and integrated original-Borel-root generators,
all inside the fixed Borel. -/

noncomputable section
namespace ReductiveGroups

open TauCeti CategoryTheory

universe u
variable {K B ι : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  [CommRing B] [HopfAlgebra K B] [Algebra.FiniteType K B]

local notation "𝔤" => Derivation K B (TauCeti.Bialgebra.CounitAlgebra K B K)
local notation "M" => Multiplicative (ι →₀ ℤ)

/-- Every nonidentity character vector of the fixed Borel tangent,
indexed with its character and both membership proofs. -/
abbrev borelRootVectorIndex
    (J : HopfIdeal K B) (π : B →ₐc[K] MonoidAlgebra K M) :=
  Σ α : M, {d : 𝔤 // α ≠ 1 ∧
    d ∈ affineGroupCharacterWeightSpace π α ∧
    d ∈ (TauCeti.derivationCompLieHom (B := K)
      (TauCeti.CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B) J).hom).range}

/-- The unique Ga morphism integrating a fixed Borel character
vector,. -/
noncomputable def borelRootVectorGa
    (J : HopfIdeal K B) (π : B →ₐc[K] MonoidAlgebra K M)
    (hπ : Function.Surjective π) (r : borelRootVectorIndex J π) :
    B →ₐc[K] SymmetricAlgebra K K :=
  Classical.choose (CharacterRootIntegration.existsUnique_of_latticeCharacterWeight
    π hπ r.1 r.2.property.1 r.2.val r.2.property.2.1)

/-- The equality is

```lean
gaAffineGroupTangent (borelRootVectorGa J π hπ r) = r.2.val
```
-/
@[simp] theorem borelRootVectorGa_tangent
    (J : HopfIdeal K B) (π : B →ₐc[K] MonoidAlgebra K M)
    (hπ : Function.Surjective π) (r : borelRootVectorIndex J π) :
    gaAffineGroupTangent (borelRootVectorGa J π hπ r) = r.2.val :=
  (Classical.choose_spec (CharacterRootIntegration.existsUnique_of_latticeCharacterWeight
    π hπ r.1 r.2.property.1 r.2.val r.2.property.2.1)).1

/-- The dependent codomain chooses the split torus for `none`
and the additive group for each Borel root vector. -/
def borelRootGeneratorCodomain
    (J : HopfIdeal K B) (π : B →ₐc[K] MonoidAlgebra K M)
    (j : Option (borelRootVectorIndex J π)) : CommHopfAlgCat.{u} K :=
  match j with
  | none => CommHopfAlgCat.of K (MonoidAlgebra K M)
  | some _ => CommHopfAlgCat.of K (SymmetricAlgebra K K)

/-- The exact mixed family in the original coordinate Hopf algebra. -/
def borelRootGeneratorFamily
    (J : HopfIdeal K B) (π : B →ₐc[K] MonoidAlgebra K M)
    (hπ : Function.Surjective π) :
    ∀ j, CommHopfAlgCat.of K B ⟶ borelRootGeneratorCodomain J π j
  | none => CommHopfAlgCat.ofHom π
  | some r => CommHopfAlgCat.ofHom (borelRootVectorGa J π hπ r)

/-- Every mixed generator factors through the same fixed original Borel:
its ideal is killed by the torus quotient and by each integrated root Ga. -/
theorem borel_le_commonKernelRootGenerators
    (I J : HopfIdeal K B) (hJI : J ≤ I)
    (π : B →ₐc[K] MonoidAlgebra K M) (hπ : Function.Surjective π)
    (hker : ∀ b : B, π b = 0 ↔ b ∈ I.toIdeal) :
    J ≤ CommHopfAlgCat.commonKernelHopfIdeal
      (borelRootGeneratorFamily J π hπ) := by
  apply (CommHopfAlgCat.le_commonKernelHopfIdeal_iff
    (borelRootGeneratorFamily J π hπ) J).mpr
  intro j b hb
  cases j with
  | none =>
      exact (hker b).2 (hJI hb)
  | some r =>
      have hd : ∀ a ∈ J,
          gaAffineGroupTangent (borelRootVectorGa J π hπ r) a = 0 := by
        intro a ha
        rw [borelRootVectorGa_tangent]
        exact (tangent_mem_hopfQuotient_iff J r.2.val).mp r.2.property.2.2 a ha
      exact (gaMorphism_kills_hopfIdeal_iff (borelRootVectorGa J π hπ r) J).mpr hd b hb

/-- The mixed generated quotient tangent contains the tangent of the fixed
original torus coordinate map. -/
theorem borelRootGenerators_torusTangent_mem
    (J : HopfIdeal K B) (π : B →ₐc[K] MonoidAlgebra K M)
    (hπ : Function.Surjective π) (d : 𝔤)
    (hd : d ∈ diagonalizableTangentImage π) :
    d ∈ (TauCeti.derivationCompLieHom (B := K)
      (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B)
        (CommHopfAlgCat.commonKernelHopfIdeal
          (borelRootGeneratorFamily J π hπ))).hom).range := by
  apply (tangent_mem_hopfQuotient_iff _ d).mpr
  intro b hb
  obtain ⟨t, rfl⟩ := hd
  have hzero : π b = 0 :=
    CommHopfAlgCat.commonKernelHopfIdeal_toIdeal_le_ker
      (borelRootGeneratorFamily J π hπ) none hb
  change t (π b) = 0
  rw [hzero, map_zero]

/-- The mixed generated quotient tangent contains every indexed original
Borel root vector. -/
theorem borelRootGenerators_rootTangent_mem
    (J : HopfIdeal K B) (π : B →ₐc[K] MonoidAlgebra K M)
    (hπ : Function.Surjective π) (r : borelRootVectorIndex J π) :
    r.2.val ∈ (TauCeti.derivationCompLieHom (B := K)
      (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B)
        (CommHopfAlgCat.commonKernelHopfIdeal
          (borelRootGeneratorFamily J π hπ))).hom).range := by
  apply (tangent_mem_hopfQuotient_iff _ r.2.val).mpr
  intro b hb
  have hzero : borelRootVectorGa J π hπ r b = 0 :=
    CommHopfAlgCat.commonKernelHopfIdeal_toIdeal_le_ker
      (borelRootGeneratorFamily J π hπ) (some r) hb
  rw [← borelRootVectorGa_tangent J π hπ r]
  apply (TauCeti.Bialgebra.CounitAlgebra.algEquivSelf K B K).injective
  rw [map_zero, gaAffineGroupTangent, gaOriginDerivation_comp_apply, hzero,
    map_zero, Polynomial.coeff_zero]

/-- The tangent of any original subgroup containing the fixed
maximal torus is spanned by its zero weight and all of its nonidentity
character vectors. Every such vector occurs in the mixed family, so its
generated quotient has the same tangent image. -/
theorem borelRootGenerators_tangent_eq
    [Finite ι]
    (I J : HopfIdeal K B) (hJI : J ≤ I)
    (hI : HopfIdeal.IsMaximalTorus K (CommHopfAlgCat.of K B) I)
    (π : B →ₐc[K] MonoidAlgebra K M) (hπ : Function.Surjective π)
    (hker : ∀ b : B, π b = 0 ↔ b ∈ I.toIdeal)
    (hB : reductiveCommHopfAlgProperty K
      (FiniteTypeCommHopfAlgCat.of K B)) :
    (TauCeti.derivationCompLieHom (B := K)
      (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B)
        (CommHopfAlgCat.commonKernelHopfIdeal
          (borelRootGeneratorFamily J π hπ))).hom).range =
      (TauCeti.derivationCompLieHom (B := K)
        (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B) J).hom).range := by
  let _ := finiteTypeAffineGroup_tangent_finite (K := K) (B := B)
  let _ := MaximalTorusLieCartan.maximalTorus_coordinateTangent_isCartan I hI π hπ hker hB
  let H := diagonalizableTangentImage π
  let S := (TauCeti.derivationCompLieHom (B := K)
    (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B) J).hom).range
  let G := (TauCeti.derivationCompLieHom (B := K)
    (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B)
      (CommHopfAlgCat.commonKernelHopfIdeal
        (borelRootGeneratorFamily J π hπ))).hom).range
  have hHS : H ≤ S := by
    intro d hd
    apply (tangent_mem_hopfQuotient_iff J d).mpr
    intro b hb
    obtain ⟨t, rfl⟩ := hd
    change t (π b) = 0
    rw [(hker b).2 (hJI hb), map_zero]
  have hHG : H ≤ G := by
    intro d hd
    exact borelRootGenerators_torusTangent_mem J π hπ d hd
  have hNle : cartanStableSubmodule H S hHS ≤
      cartanStableSubmodule H G hHG := by
    rw [CartanStableSubmodule.eq_iSup_inf_rootSpace H S hHS]
    refine iSup_le fun χ => ?_
    intro d hd
    have hdS : (d : 𝔤) ∈ S :=
      (mem_cartanStableSubmodule H S hHS d).mp hd.1
    have hdroot : (d : 𝔤) ∈ LieAlgebra.rootSpace H χ := hd.2
    by_cases hχ : χ.IsZero
    · have hz : LieAlgebra.rootSpace H χ = H.toLieSubmodule := by
        simpa only [hχ.eq] using (LieAlgebra.rootSpace_zero_eq K 𝔤 H)
      have hdH : (d : 𝔤) ∈ H := by
        rw [hz] at hdroot
        exact hdroot
      exact (mem_cartanStableSubmodule H G hHG d).mpr (hHG hdH)
    · obtain ⟨α, ⟨_, hαχ⟩, _⟩ :=
        existsUnique_character_of_lieWeight π hπ χ
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
      let r : borelRootVectorIndex J π := ⟨α, ⟨d, hα, hdW, hdS⟩⟩
      exact (mem_cartanStableSubmodule H G hHG d).mpr
        (borelRootGenerators_rootTangent_mem J π hπ r)
  have hSG : S ≤ G := by
    intro d hd
    exact (mem_cartanStableSubmodule H G hHG d).mp
      (hNle ((mem_cartanStableSubmodule H S hHS d).mpr hd))
  have hGS : G ≤ S :=
    hopfQuotient_tangentImage_antitone
      (CommHopfAlgCat.commonKernelHopfIdeal
        (borelRootGeneratorFamily J π hπ)) J
      (borel_le_commonKernelRootGenerators I J hJI π hπ hker)
  exact le_antisymm hGS hSG

end ReductiveGroups
