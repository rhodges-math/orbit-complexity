import OrbitComplexity.ReductiveGroups.Groups.Representatives.WeylRepresentativeReflections

/-! # Weyl representatives and conjugation of root subgroups -/

noncomputable section
namespace ReductiveGroups

open TauCeti LieAlgebra LieAlgebra.IsKilling LieModule

universe u
variable {K B ι : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  [CommRing B] [HopfAlgebra K B] [Algebra.FiniteType K B] [Finite ι]

local notation "𝔤" => Derivation K B (Bialgebra.CounitAlgebra K B K)
local notation "M" => Multiplicative (ι →₀ ℤ)

/-- The representative `ẇ` of a Weyl element `w` of the center-quotient
root system: the product of the chosen root reflection points along the chosen
reduced word of `w` for the base `b`. -/
def weylRepresentative
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
    let P := rootSystem (centerQuotientCartan (diagonalizableTangentImage π))
    P.Base → P.weylGroup → WithConv (B →ₐ[K] K) := by
  intro _ _ _ _ _ P b w
  exact weylElementPoint (fun r => characterReflectionPoint I hI π hπ hker hB
    ((ReductiveCharacterRoots.characterCenterQuotientRootEquiv I hI π hπ hker hB).symm r)) b w

/-- `ẇ` is the word product of the chosen reflection points along the chosen
reduced word of `w`. -/
theorem weylRepresentative_eq
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
    ∀ (b : P.Base) (w : P.weylGroup),
      weylRepresentative I hI π hπ hker hB b w = simpleWordPoint n b (chosenReducedWord b w) := by
  intro _ _ _ _ _ H P E n b w
  rfl

/-- `ẇ` normalizes the torus points `T(K)`. -/
theorem weylRepresentative_mem_normalizer
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
    ∀ (b : P.Base) (w : P.weylGroup),
      weylRepresentative I hI π hπ hker hB b w ∈ Subgroup.normalizer
        (CommHopfAlgCat.quotientPointsSubgroup (CommHopfAlgCat.of K B) I (CommAlgCat.of K K) :
          Set (WithConv (B →ₐ[K] K))) := by
  intro _ _ _ _ _ H P
  let E := ReductiveCharacterRoots.characterCenterQuotientRootEquiv I hI π hπ hker hB
  let n := fun r : (centerQuotientCartan H).root =>
    characterReflectionPoint I hI π hπ hker hB (E.symm r)
  have hsys : IsWeylRepresentativeSystem P
      (CommHopfAlgCat.quotientPointsSubgroup (CommHopfAlgCat.of K B) I (CommAlgCat.of K K)) n
      (fun g σ => ∀ r, (affineGroupCharacterWeightSpace π (E.symm r).val).map
          ((affineGroupAdjointLieEquiv g).toLinearEquiv : 𝔤 →ₗ[K] 𝔤) =
        affineGroupCharacterWeightSpace π (E.symm (σ r)).val) :=
    reductive_isWeylRepresentativeSystem I hI π hπ hker hB
  intro b w
  exact hsys.weylElementPoint_mem_normalizer b w

/-- **`ẇ` acts by `w` on root spaces.** `Ad(ẇ)` maps the character space of
every root `r` onto the character space of the root `w(r)`
(`weylGroupToPerm w r`). -/
theorem weylRepresentative_characterSpace_map
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
    ∀ (b : P.Base) (w : P.weylGroup) (r : (centerQuotientCartan H).root),
      (affineGroupCharacterWeightSpace π (E.symm r).val).map
          ((affineGroupAdjointLieEquiv (weylRepresentative I hI π hπ hker hB b w)).toLinearEquiv :
            𝔤 →ₗ[K] 𝔤) =
        affineGroupCharacterWeightSpace π (E.symm (P.weylGroupToPerm w r)).val := by
  intro _ _ _ _ _ H P E
  let n := fun r : (centerQuotientCartan H).root =>
    characterReflectionPoint I hI π hπ hker hB (E.symm r)
  have hsys : IsWeylRepresentativeSystem P
      (CommHopfAlgCat.quotientPointsSubgroup (CommHopfAlgCat.of K B) I (CommAlgCat.of K K)) n
      (fun g σ => ∀ r, (affineGroupCharacterWeightSpace π (E.symm r).val).map
          ((affineGroupAdjointLieEquiv g).toLinearEquiv : 𝔤 →ₗ[K] 𝔤) =
        affineGroupCharacterWeightSpace π (E.symm (σ r)).val) :=
    reductive_isWeylRepresentativeSystem I hI π hπ hker hB
  intro b w r
  exact hsys.weylElementPoint_transport b w r

/-- `ẇ` conjugates every root subgroup for the root `r` to the
root subgroup of the root `w(r)` with the transported tangent. -/
theorem weylRepresentative_ga_conjugation
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
    ∀ (b : P.Base) (w : P.weylGroup) (r : (centerQuotientCartan H).root)
      (z : B →ₐc[K] SymmetricAlgebra K K),
      gaAffineGroupTangent z ∈ affineGroupCharacterWeightSpace π (E.symm r).val →
      ∃ z' : B →ₐc[K] SymmetricAlgebra K K,
        gaAffineGroupTangent z' = affineGroupAdjointRepresentation
          (weylRepresentative I hI π hπ hker hB b w) (gaAffineGroupTangent z) ∧
        gaAffineGroupTangent z' ∈ affineGroupCharacterWeightSpace π
          (E.symm (P.weylGroupToPerm w r)).val ∧
        ∀ u : K, weylRepresentative I hI π hπ hker hB b w *
            gaAffineGroupPoints z (Multiplicative.ofAdd u) *
            (weylRepresentative I hI π hπ hker hB b w)⁻¹ =
          gaAffineGroupPoints z' (Multiplicative.ofAdd u) := by
  intro _ _ _ _ _ H P E b w r z hz
  have hmap := weylRepresentative_characterSpace_map I hI π hπ hker hB b w r
  exact ga_conjugation_of_characterSpace_map π hπ _ _ _ (E.symm _).property.2 hmap z hz

/-- **Conjugation law.** For the chosen root subgroups
`x_r = (characterSl2PairChoice … (E⁻¹ r)).1`, every Weyl element `w` and root
`r` there is `c ≠ 0` with `ẇ x_r(u) ẇ⁻¹ = x_{w(r)}(c u)` for all `u`. -/
theorem weylRepresentative_conj_rootSubgroup
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
    ∀ (b : P.Base) (w : P.weylGroup) (r : (centerQuotientCartan H).root),
      ∃ c : K, c ≠ 0 ∧ ∀ u : K,
        weylRepresentative I hI π hπ hker hB b w *
            gaAffineGroupPoints (characterSl2PairChoice I hI π hπ hker hB (E.symm r)).1
              (Multiplicative.ofAdd u) *
            (weylRepresentative I hI π hπ hker hB b w)⁻¹ =
          gaAffineGroupPoints
            (characterSl2PairChoice I hI π hπ hker hB (E.symm (P.weylGroupToPerm w r))).1
            (Multiplicative.ofAdd (c * u)) := by
  intro _ _ _ _ _ H P E b w r
  have hmap := weylRepresentative_characterSpace_map I hI π hπ hker hB b w r
  have hspec := characterSl2PairChoice_isRootSl2Pair I hI π hπ hker hB
  exact WeylRepresentativeReflections.conjugation_scaled_of_characterSpace_map I hI π hπ hker hB _ _
    _
    (E.symm _).property.2 (E.symm _).property.1 hmap _ _
    (hspec (E.symm r)).tangent_mem (hspec (E.symm r)).tangent_ne_zero
    (hspec (E.symm (P.weylGroupToPerm w r))).tangent_mem
    (hspec (E.symm (P.weylGroupToPerm w r))).tangent_ne_zero

end ReductiveGroups
