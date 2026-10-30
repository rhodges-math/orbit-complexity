import OrbitComplexity.ReductiveGroups.Groups.Representatives.WeylRepresentativeAbstract
import OrbitComplexity.ReductiveGroups.Groups.Representatives.RootRankOneReflectionTransport
import OrbitComplexity.ReductiveGroups.Groups.Representatives.RootRankOneConjugation
import OrbitComplexity.ReductiveGroups.Groups.Representatives.CharacterReflection

/-! # Character reflections form a Weyl representative system -/

noncomputable section
namespace ReductiveGroups

open TauCeti LieAlgebra LieAlgebra.IsKilling LieModule

universe u

variable {K B ι : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  [CommRing B] [HopfAlgebra K B] [Algebra.FiniteType K B] [Finite ι]

local notation "𝔤" => Derivation K B (Bialgebra.CounitAlgebra K B K)
local notation "M" => Multiplicative (ι →₀ ℤ)

/-- The chosen reflection points, indexed by the roots of the center
quotient, form a Weyl representative system for the torus point subgroup
`T(K)`, with transport meaning that `Ad(g)` maps every root's character space
onto the character space of the permuted root. -/
theorem reductive_isWeylRepresentativeSystem
    (I : HopfIdeal K B)
    (hI : HopfIdeal.IsMaximalTorus K (CommHopfAlgCat.of K B) I)
    (π : B →ₐc[K] MonoidAlgebra K M) (hπ : Function.Surjective π)
    (hker : ∀ a : B, π a = 0 ↔ a ∈ I.toIdeal)
    (hB : reductiveCommHopfAlgProperty K (FiniteTypeCommHopfAlgCat.of K B)) :
    let _ := finiteTypeAffineGroup_tangent_finite (K := K) (B := B)
    let _ := reductive_tangent_hasCentralRadical hB
    let _ := ReductiveTorusRootSystem.tangent_centerQuotient_isKilling hB
    let _ := MaximalTorusLieCartan.maximalTorus_coordinateTangent_isCartan I hI π hπ hker hB
    let _ := ReductiveTorusRootSystem.coordinateCenterQuotient_isCartan I hI π hπ hker hB
    let H := diagonalizableTangentImage π
    let P := rootSystem (centerQuotientCartan H)
    let E := ReductiveCharacterRoots.characterCenterQuotientRootEquiv I hI π hπ hker hB
    IsWeylRepresentativeSystem P
      (CommHopfAlgCat.quotientPointsSubgroup (CommHopfAlgCat.of K B) I (CommAlgCat.of K K))
      (fun r => characterReflectionPoint I hI π hπ hker hB (E.symm r))
      (fun g σ => ∀ r, (affineGroupCharacterWeightSpace π (E.symm r).val).map
          ((affineGroupAdjointLieEquiv g).toLinearEquiv : 𝔤 →ₗ[K] 𝔤) =
        affineGroupCharacterWeightSpace π (E.symm (σ r)).val) := by
  intro _ _ _ _ _ H P E
  have hspec := characterSl2PairChoice_isRootSl2Pair I hI π hπ hker hB
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r
    exact (hspec (E.symm r)).rootReflectionPoint_mem_normalizer I hπ hker
  · intro r
    exact (hspec (E.symm r)).rootReflectionPoint_sq_mem_torusPoints I hπ hker
  · exact affineGroupAdjoint_transport_one
      (fun r => affineGroupCharacterWeightSpace π (E.symm r).val)
  · intro g h σ τ hg hh
    exact affineGroupAdjoint_transport_mul
      (fun r => affineGroupCharacterWeightSpace π (E.symm r).val) g h σ τ hg hh
  · intro r s
    have hE : ∀ x : (centerQuotientCartan H).root,
        ReductiveCharacterRoots.characterCenterQuotientRootEquiv I hI π hπ hker hB (E.symm x) = x :=
      fun x => E.apply_symm_apply x
    have h := (hspec (E.symm r)).rootReflectionPoint_characterSpace_map I hI π hπ hker hB
      (E.symm r) (E.symm s)
    simp only [hE] at h
    exact h
  · intro g σ hg hTr r
    have hαβ : ∀ d ∈ affineGroupCharacterWeightSpace π (E.symm r).val,
        affineGroupAdjointRepresentation g d ∈
          affineGroupCharacterWeightSpace π (E.symm (σ r)).val := by
      intro d hd
      rw [← hTr r]
      exact Submodule.mem_map_of_mem hd
    exact conj_rootReflectionPoint_mem_torus_mul I hI π hπ hker hB g
      (fun t ht => (Subgroup.mem_normalizer_iff.mp hg t).mp ht)
      (hspec (E.symm r)) (hspec (E.symm (σ r))) hαβ

/-- Every word product of chosen reflection points normalizes `T(K)`. -/
theorem reductive_simpleWordPoint_mem_normalizer
    (I : HopfIdeal K B)
    (hI : HopfIdeal.IsMaximalTorus K (CommHopfAlgCat.of K B) I)
    (π : B →ₐc[K] MonoidAlgebra K M) (hπ : Function.Surjective π)
    (hker : ∀ a : B, π a = 0 ↔ a ∈ I.toIdeal)
    (hB : reductiveCommHopfAlgProperty K (FiniteTypeCommHopfAlgCat.of K B)) :
    let _ := finiteTypeAffineGroup_tangent_finite (K := K) (B := B)
    let _ := reductive_tangent_hasCentralRadical hB
    let _ := ReductiveTorusRootSystem.tangent_centerQuotient_isKilling hB
    let _ := MaximalTorusLieCartan.maximalTorus_coordinateTangent_isCartan I hI π hπ hker hB
    let _ := ReductiveTorusRootSystem.coordinateCenterQuotient_isCartan I hI π hπ hker hB
    let H := diagonalizableTangentImage π
    let P := rootSystem (centerQuotientCartan H)
    let E := ReductiveCharacterRoots.characterCenterQuotientRootEquiv I hI π hπ hker hB
    let n := fun r : (centerQuotientCartan H).root =>
      characterReflectionPoint I hI π hπ hker hB (E.symm r)
    ∀ (b : P.Base) (l : List b.support),
      simpleWordPoint n b l ∈ Subgroup.normalizer
        (CommHopfAlgCat.quotientPointsSubgroup (CommHopfAlgCat.of K B) I
          (CommAlgCat.of K K) : Set (WithConv (B →ₐ[K] K))) := by
  intro _ _ _ _ _ H P E n
  have hsys : IsWeylRepresentativeSystem P
      (CommHopfAlgCat.quotientPointsSubgroup (CommHopfAlgCat.of K B) I (CommAlgCat.of K K)) n
      (fun g σ => ∀ r, (affineGroupCharacterWeightSpace π (E.symm r).val).map
          ((affineGroupAdjointLieEquiv g).toLinearEquiv : 𝔤 →ₗ[K] 𝔤) =
        affineGroupCharacterWeightSpace π (E.symm (σ r)).val) :=
    reductive_isWeylRepresentativeSystem I hI π hπ hker hB
  intro b l
  exact hsys.simpleWordPoint_mem_normalizer b l

/-- **Root-space transport by words.** For a word `l` in the simple roots of a
base `b`, `Ad(n_l)` maps the character space of each root `r` onto the character
space of the root `w_l(r)`, where `w_l = simpleWeylWord b l` acts through Mathlib's
`weylGroupToPerm`. -/
theorem WeylRepresentativeReflections.simpleWordPoint_characterSpace_map
    (I : HopfIdeal K B)
    (hI : HopfIdeal.IsMaximalTorus K (CommHopfAlgCat.of K B) I)
    (π : B →ₐc[K] MonoidAlgebra K M) (hπ : Function.Surjective π)
    (hker : ∀ a : B, π a = 0 ↔ a ∈ I.toIdeal)
    (hB : reductiveCommHopfAlgProperty K (FiniteTypeCommHopfAlgCat.of K B)) :
    let _ := finiteTypeAffineGroup_tangent_finite (K := K) (B := B)
    let _ := reductive_tangent_hasCentralRadical hB
    let _ := ReductiveTorusRootSystem.tangent_centerQuotient_isKilling hB
    let _ := MaximalTorusLieCartan.maximalTorus_coordinateTangent_isCartan I hI π hπ hker hB
    let _ := ReductiveTorusRootSystem.coordinateCenterQuotient_isCartan I hI π hπ hker hB
    let H := diagonalizableTangentImage π
    let P := rootSystem (centerQuotientCartan H)
    let E := ReductiveCharacterRoots.characterCenterQuotientRootEquiv I hI π hπ hker hB
    let n := fun r : (centerQuotientCartan H).root =>
      characterReflectionPoint I hI π hπ hker hB (E.symm r)
    ∀ (b : P.Base) (l : List b.support) (r : (centerQuotientCartan H).root),
      (affineGroupCharacterWeightSpace π (E.symm r).val).map
          ((affineGroupAdjointLieEquiv (simpleWordPoint n b l)).toLinearEquiv : 𝔤 →ₗ[K] 𝔤) =
        affineGroupCharacterWeightSpace π
          (E.symm (P.weylGroupToPerm (simpleWeylWord b l) r)).val := by
  intro _ _ _ _ _ H P E n
  have hsys : IsWeylRepresentativeSystem P
      (CommHopfAlgCat.quotientPointsSubgroup (CommHopfAlgCat.of K B) I (CommAlgCat.of K K)) n
      (fun g σ => ∀ r, (affineGroupCharacterWeightSpace π (E.symm r).val).map
          ((affineGroupAdjointLieEquiv g).toLinearEquiv : 𝔤 →ₗ[K] 𝔤) =
        affineGroupCharacterWeightSpace π (E.symm (σ r)).val) :=
    reductive_isWeylRepresentativeSystem I hI π hπ hker hB
  intro b l
  exact hsys.simpleWordPoint_transport b l

/-- **Braid relations modulo `T(K)`.** For distinct simple roots `i, j` with
Coxeter number `m_{ij}`, the products along the two alternating words of length
`m_{ij}` differ by a factor in `T(K)`. -/
theorem reductive_simpleWordPoint_braid
    (I : HopfIdeal K B)
    (hI : HopfIdeal.IsMaximalTorus K (CommHopfAlgCat.of K B) I)
    (π : B →ₐc[K] MonoidAlgebra K M) (hπ : Function.Surjective π)
    (hker : ∀ a : B, π a = 0 ↔ a ∈ I.toIdeal)
    (hB : reductiveCommHopfAlgProperty K (FiniteTypeCommHopfAlgCat.of K B)) :
    let _ := finiteTypeAffineGroup_tangent_finite (K := K) (B := B)
    let _ := reductive_tangent_hasCentralRadical hB
    let _ := ReductiveTorusRootSystem.tangent_centerQuotient_isKilling hB
    let _ := MaximalTorusLieCartan.maximalTorus_coordinateTangent_isCartan I hI π hπ hker hB
    let _ := ReductiveTorusRootSystem.coordinateCenterQuotient_isCartan I hI π hπ hker hB
    let H := diagonalizableTangentImage π
    let P := rootSystem (centerQuotientCartan H)
    let E := ReductiveCharacterRoots.characterCenterQuotientRootEquiv I hI π hπ hker hB
    let n := fun r : (centerQuotientCartan H).root =>
      characterReflectionPoint I hI π hπ hker hB (E.symm r)
    ∀ (b : P.Base) (i j : b.support), i ≠ j →
      ∃ t ∈ CommHopfAlgCat.quotientPointsSubgroup (CommHopfAlgCat.of K B) I (CommAlgCat.of K K),
        simpleWordPoint n b (CoxeterSystem.braidWord (simpleCoxeterMatrix b) i j) =
          t * simpleWordPoint n b (CoxeterSystem.braidWord (simpleCoxeterMatrix b) j i) := by
  intro _ _ _ _ _ H P E n
  have hsys : IsWeylRepresentativeSystem P
      (CommHopfAlgCat.quotientPointsSubgroup (CommHopfAlgCat.of K B) I (CommAlgCat.of K K)) n
      (fun g σ => ∀ r, (affineGroupCharacterWeightSpace π (E.symm r).val).map
          ((affineGroupAdjointLieEquiv g).toLinearEquiv : 𝔤 →ₗ[K] 𝔤) =
        affineGroupCharacterWeightSpace π (E.symm (σ r)).val) :=
    reductive_isWeylRepresentativeSystem I hI π hπ hker hB
  intro b i j hij
  exact hsys.simpleWordPoint_braid b hij

/-- **Root-subgroup conjugation by words.** For a word `l`, root `r` and
`Ga` morphism `z` with tangent in the `r` character space, there is a
`Ga` morphism `z'` with tangent `Ad(n_l)(dz)` in the character space of `w_l(r)`
and `n_l z(u) n_l⁻¹ = z'(u)` for every `u`. -/
theorem reductive_simpleWordPoint_ga_conjugation
    (I : HopfIdeal K B)
    (hI : HopfIdeal.IsMaximalTorus K (CommHopfAlgCat.of K B) I)
    (π : B →ₐc[K] MonoidAlgebra K M) (hπ : Function.Surjective π)
    (hker : ∀ a : B, π a = 0 ↔ a ∈ I.toIdeal)
    (hB : reductiveCommHopfAlgProperty K (FiniteTypeCommHopfAlgCat.of K B)) :
    let _ := finiteTypeAffineGroup_tangent_finite (K := K) (B := B)
    let _ := reductive_tangent_hasCentralRadical hB
    let _ := ReductiveTorusRootSystem.tangent_centerQuotient_isKilling hB
    let _ := MaximalTorusLieCartan.maximalTorus_coordinateTangent_isCartan I hI π hπ hker hB
    let _ := ReductiveTorusRootSystem.coordinateCenterQuotient_isCartan I hI π hπ hker hB
    let H := diagonalizableTangentImage π
    let P := rootSystem (centerQuotientCartan H)
    let E := ReductiveCharacterRoots.characterCenterQuotientRootEquiv I hI π hπ hker hB
    let n := fun r : (centerQuotientCartan H).root =>
      characterReflectionPoint I hI π hπ hker hB (E.symm r)
    ∀ (b : P.Base) (l : List b.support) (r : (centerQuotientCartan H).root)
      (z : B →ₐc[K] SymmetricAlgebra K K),
      gaAffineGroupTangent z ∈ affineGroupCharacterWeightSpace π (E.symm r).val →
      ∃ z' : B →ₐc[K] SymmetricAlgebra K K,
        gaAffineGroupTangent z' = affineGroupAdjointRepresentation (simpleWordPoint n b l)
          (gaAffineGroupTangent z) ∧
        gaAffineGroupTangent z' ∈ affineGroupCharacterWeightSpace π
          (E.symm (P.weylGroupToPerm (simpleWeylWord b l) r)).val ∧
        ∀ u : K, simpleWordPoint n b l * gaAffineGroupPoints z (Multiplicative.ofAdd u) *
            (simpleWordPoint n b l)⁻¹ = gaAffineGroupPoints z' (Multiplicative.ofAdd u) := by
  intro _ _ _ _ _ H P E n
  have hsys : IsWeylRepresentativeSystem P
      (CommHopfAlgCat.quotientPointsSubgroup (CommHopfAlgCat.of K B) I (CommAlgCat.of K K)) n
      (fun g σ => ∀ r, (affineGroupCharacterWeightSpace π (E.symm r).val).map
          ((affineGroupAdjointLieEquiv g).toLinearEquiv : 𝔤 →ₗ[K] 𝔤) =
        affineGroupCharacterWeightSpace π (E.symm (σ r)).val) :=
    reductive_isWeylRepresentativeSystem I hI π hπ hker hB
  intro b l r z hz
  exact ga_conjugation_of_characterSpace_map π hπ _ _ _ (E.symm _).property.2
    (hsys.simpleWordPoint_transport b l r) z hz

/-- **Well-definedness modulo `T(K)`.** Two reduced words (for the Coxeter
system of the Weyl group) with the same Weyl element have word products
in the same `T(K)`-coset. -/
theorem reductive_simpleWordPoint_of_reduced
    (I : HopfIdeal K B)
    (hI : HopfIdeal.IsMaximalTorus K (CommHopfAlgCat.of K B) I)
    (π : B →ₐc[K] MonoidAlgebra K M) (hπ : Function.Surjective π)
    (hker : ∀ a : B, π a = 0 ↔ a ∈ I.toIdeal)
    (hB : reductiveCommHopfAlgProperty K (FiniteTypeCommHopfAlgCat.of K B)) :
    let _ := finiteTypeAffineGroup_tangent_finite (K := K) (B := B)
    let _ := reductive_tangent_hasCentralRadical hB
    let _ := ReductiveTorusRootSystem.tangent_centerQuotient_isKilling hB
    let _ := MaximalTorusLieCartan.maximalTorus_coordinateTangent_isCartan I hI π hπ hker hB
    let _ := ReductiveTorusRootSystem.coordinateCenterQuotient_isCartan I hI π hπ hker hB
    let H := diagonalizableTangentImage π
    let P := rootSystem (centerQuotientCartan H)
    let E := ReductiveCharacterRoots.characterCenterQuotientRootEquiv I hI π hπ hker hB
    let n := fun r : (centerQuotientCartan H).root =>
      characterReflectionPoint I hI π hπ hker hB (E.symm r)
    ∀ (b : P.Base) (l k : List b.support),
      (weylCoxeterSystem b).IsReduced l → (weylCoxeterSystem b).IsReduced k →
      simpleWeylWord b l = simpleWeylWord b k →
      ∃ t ∈ CommHopfAlgCat.quotientPointsSubgroup (CommHopfAlgCat.of K B) I (CommAlgCat.of K K),
        simpleWordPoint n b l = t * simpleWordPoint n b k := by
  intro _ _ _ _ _ H P E n
  have hsys : IsWeylRepresentativeSystem P
      (CommHopfAlgCat.quotientPointsSubgroup (CommHopfAlgCat.of K B) I (CommAlgCat.of K K)) n
      (fun g σ => ∀ r, (affineGroupCharacterWeightSpace π (E.symm r).val).map
          ((affineGroupAdjointLieEquiv g).toLinearEquiv : 𝔤 →ₗ[K] 𝔤) =
        affineGroupCharacterWeightSpace π (E.symm (σ r)).val) :=
    reductive_isWeylRepresentativeSystem I hI π hπ hker hB
  intro b l k hl hk heq
  exact hsys.simpleWordPoint_of_reduced b hl hk heq

end ReductiveGroups
