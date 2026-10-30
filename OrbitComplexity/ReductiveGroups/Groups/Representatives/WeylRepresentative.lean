import OrbitComplexity.ReductiveGroups.Groups.Representatives.WeylRepresentativeReflections
import OrbitComplexity.ReductiveGroups.Groups.Representatives.WeylConjugation

/-! # Multiplication laws for Weyl representatives -/

noncomputable section
namespace ReductiveGroups

open TauCeti LieAlgebra LieAlgebra.IsKilling LieModule

universe u
variable {K B ι : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  [CommRing B] [HopfAlgebra K B] [Algebra.FiniteType K B] [Finite ι]

local notation "𝔤" => Derivation K B (Bialgebra.CounitAlgebra K B K)
local notation "M" => Multiplicative (ι →₀ ℤ)

/-- `1̇ = 1`. -/
theorem weylRepresentative_one
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
    ∀ b : P.Base, weylRepresentative I hI π hπ hker hB b 1 = 1 := by
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
  intro b
  exact weylElementPoint_one n b

/-- **Length-additive products.** If `ℓ(uv) = ℓ(u) + ℓ(v)` then
`u̇ v̇ = t (uv)˙` for some `t ∈ T(K)`. -/
theorem weylRepresentative_mul_of_length_add
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
    ∀ (b : P.Base) (u v : P.weylGroup),
      (weylCoxeterSystem b).length (u * v) =
        (weylCoxeterSystem b).length u + (weylCoxeterSystem b).length v →
      ∃ t ∈ CommHopfAlgCat.quotientPointsSubgroup (CommHopfAlgCat.of K B) I (CommAlgCat.of K K),
        weylRepresentative I hI π hπ hker hB b u * weylRepresentative I hI π hπ hker hB b v =
          t * weylRepresentative I hI π hπ hker hB b (u * v) := by
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
  intro b u v huv
  exact hsys.weylElementPoint_mul_of_length_add b u v huv

/-- **Products of representatives.** For all `u, v` in the Weyl group,
`u̇ v̇ = t (uv)˙` for some `t ∈ T(K)`. -/
theorem weylRepresentative_mul
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
    ∀ (b : P.Base) (u v : P.weylGroup),
      ∃ t ∈ CommHopfAlgCat.quotientPointsSubgroup (CommHopfAlgCat.of K B) I (CommAlgCat.of K K),
        weylRepresentative I hI π hπ hker hB b u * weylRepresentative I hI π hπ hker hB b v =
          t * weylRepresentative I hI π hπ hker hB b (u * v) := by
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
  intro b u v
  exact hsys.weylElementPoint_mul b u v

/-- `ẇ⁻¹ = t (w⁻¹)˙` for some `t ∈ T(K)`. -/
theorem weylRepresentative_inv
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
      ∃ t ∈ CommHopfAlgCat.quotientPointsSubgroup (CommHopfAlgCat.of K B) I (CommAlgCat.of K K),
        (weylRepresentative I hI π hπ hker hB b w)⁻¹ =
          t * weylRepresentative I hI π hπ hker hB b w⁻¹ := by
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
  exact hsys.weylElementPoint_inv b w

/-- For every word `l` in the simple roots (reduced or not), the product
`n_l` of the chosen reflection points lies in `T(K) (π l)˙`, where `π l` is the
Weyl element of `l`. In particular any reduced word of `w` gives a product in
`T(K) ẇ`. -/
theorem SimpleWordPoint.eq_mul_weylRepresentative
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
      ∃ t ∈ CommHopfAlgCat.quotientPointsSubgroup (CommHopfAlgCat.of K B) I (CommAlgCat.of K K),
        simpleWordPoint n b l =
          t * weylRepresentative I hI π hπ hker hB b (simpleWeylWord b l) := by
  intro _ _ _ _ _ H P E n
  have hsys : IsWeylRepresentativeSystem P
      (CommHopfAlgCat.quotientPointsSubgroup (CommHopfAlgCat.of K B) I (CommAlgCat.of K K)) n
      (fun g σ => ∀ r, (affineGroupCharacterWeightSpace π (E.symm r).val).map
          ((affineGroupAdjointLieEquiv g).toLinearEquiv : 𝔤 →ₗ[K] 𝔤) =
        affineGroupCharacterWeightSpace π (E.symm (σ r)).val) :=
    reductive_isWeylRepresentativeSystem I hI π hπ hker hB
  intro b l
  exact hsys.simpleWordPoint_eq_mul_weylElementPoint b l

/-- The chosen reflection point of a simple root is the representative of its
simple reflection modulo `T(K)`. -/
theorem SimpleReflectionPoint.eq_mul_weylRepresentative
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
    ∀ (b : P.Base) (i : b.support),
      ∃ t ∈ CommHopfAlgCat.quotientPointsSubgroup (CommHopfAlgCat.of K B) I (CommAlgCat.of K K),
        characterReflectionPoint I hI π hπ hker hB (E.symm (i : (centerQuotientCartan H).root)) =
          t * weylRepresentative I hI π hπ hker hB b
            (RootPairing.weylGroup.ofIdx P (i : (centerQuotientCartan H).root)) := by
  intro _ _ _ _ _ H P E
  let n := fun r : (centerQuotientCartan H).root =>
    characterReflectionPoint I hI π hπ hker hB (E.symm r)
  have hsys : IsWeylRepresentativeSystem P
      (CommHopfAlgCat.quotientPointsSubgroup (CommHopfAlgCat.of K B) I (CommAlgCat.of K K)) n
      (fun g σ => ∀ r, (affineGroupCharacterWeightSpace π (E.symm r).val).map
          ((affineGroupAdjointLieEquiv g).toLinearEquiv : 𝔤 →ₗ[K] 𝔤) =
        affineGroupCharacterWeightSpace π (E.symm (σ r)).val) :=
    reductive_isWeylRepresentativeSystem I hI π hπ hker hB
  intro b i
  exact hsys.simple_eq_mul_weylElementPoint b i

end ReductiveGroups
