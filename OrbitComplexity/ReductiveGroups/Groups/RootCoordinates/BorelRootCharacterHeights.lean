import OrbitComplexity.ReductiveGroups.Groups.Borel.BorelFiniteRootGenerators
import OrbitComplexity.ReductiveGroups.Groups.Borel.BorelPositiveChamber
import OrbitComplexity.ReductiveGroups.Groups.Tangents.CharacterDifferentialFiniteProduct
import OrbitComplexity.ReductiveGroups.Lie.Roots.RootHeightLinearForm

/-!
# Borel Root Character Heights

Monomial relations among the original Borel root characters are
relations among positive root heights, for the base selected by the
original Borel in the root system of the center quotient. -/

noncomputable section
namespace ReductiveGroups

open TauCeti LieAlgebra LieAlgebra.IsKilling LieModule

universe u
variable {K B ι : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  [CommRing B] [HopfAlgebra K B] [Algebra.FiniteType K B] [Finite ι]

local notation "𝔤" => Derivation K B (Bialgebra.CounitAlgebra K B K)
local notation "M" => Multiplicative (ι →₀ ℤ)

/-- The occurring nonidentity character underlying a Borel root character. -/
def borelRootCharacterOccurring (J : HopfIdeal K B) (π : B →ₐc[K] MonoidAlgebra K M)
    (α : borelRootCharacterIndex J π) :
    {α : M // affineGroupCharacterWeightSpace π α ≠ ⊥ ∧ α ≠ 1} :=
  ⟨α.val, fun he => α.property.2 (by rw [he, inf_bot_eq]), α.property.1⟩

omit [IsAlgClosed K] [CharZero K] [Algebra.FiniteType K B] [Finite ι] in
/-- A finite monomial in characters differentiates, on the torus
tangent image, to the natural-multiplicity sum of the differentials. -/
theorem CharacterDifferentialOnImage.finsupp_prod
    (π : B →ₐc[K] MonoidAlgebra K M) (hπ : Function.Surjective π)
    {κ : Type*} (χ : κ → M) (m : κ →₀ ℕ) :
    characterDifferentialOnImage π hπ (m.prod fun j e => χ j ^ e) =
      m.sum fun j e => e • characterDifferentialOnImage π hπ (χ j) := by
  have hprod : (m.prod fun j e => χ j ^ e) = ∏ j : m.support, χ j ^ m j := by
    rw [Finsupp.prod, ← Finset.prod_coe_sort]
  have hdiff := characterDifferential_prod_pow (K := K)
    (fun j : m.support => χ j) (fun j => m j)
  rw [hprod, Finsupp.sum, ← Finset.sum_coe_sort]
  ext t
  simp only [characterDifferentialOnImage, LinearMap.comp_apply, hdiff,
    LinearMap.sum_apply, LinearMap.smul_apply]

/-- For every base of the center-quotient root system, a monomial
relation among original Borel root characters is the same relation among
the heights of their corresponding roots. -/
theorem borelRootCharacter_height_eq_sum
    (I J : HopfIdeal K B)
    (hI : HopfIdeal.IsMaximalTorus K (CommHopfAlgCat.of K B) I)
    (π : B →ₐc[K] MonoidAlgebra K M) (hπ : Function.Surjective π)
    (hker : ∀ a : B, π a = 0 ↔ a ∈ I.toIdeal)
    (hB : reductiveCommHopfAlgProperty K (FiniteTypeCommHopfAlgCat.of K B)) :
    letI := finiteTypeAffineGroup_tangent_finite (K := K) (B := B)
    letI := MaximalTorusLieCartan.maximalTorus_coordinateTangent_isCartan I hI π hπ hker hB
    letI := ReductiveTorusRootSystem.tangent_centerQuotient_isKilling hB
    letI := ReductiveTorusRootSystem.coordinateCenterQuotient_isCartan I hI π hπ hker hB
    ∀ (b : (rootSystem (centerQuotientCartan (diagonalizableTangentImage π))).Base)
      (m : borelRootCharacterIndex J π →₀ ℕ) (i : borelRootCharacterIndex J π),
      (m.prod fun j e => j.val ^ e) = i.val →
      b.height (ReductiveCharacterRoots.characterCenterQuotientRootEquiv I hI π hπ hker hB
          (borelRootCharacterOccurring J π i)) =
        m.sum fun j e => (e : ℤ) * b.height
          (ReductiveCharacterRoots.characterCenterQuotientRootEquiv I hI π hπ hker hB
            (borelRootCharacterOccurring J π j)) := by
  let _ := finiteTypeAffineGroup_tangent_finite (K := K) (B := B)
  let _ := MaximalTorusLieCartan.maximalTorus_coordinateTangent_isCartan I hI π hπ hker hB
  let _ := ReductiveTorusRootSystem.tangent_centerQuotient_isKilling hB
  let _ := ReductiveTorusRootSystem.coordinateCenterQuotient_isCartan I hI π hπ hker hB
  intro b m i hrel
  let H := diagonalizableTangentImage π
  let P := rootSystem (centerQuotientCartan H)
  let E := ReductiveCharacterRoots.characterCenterQuotientRootEquiv I hI π hπ hker hB
  let r : borelRootCharacterIndex J π → (centerQuotientCartan H).root :=
    fun j => E (borelRootCharacterOccurring J π j)
  have hr (j : borelRootCharacterIndex J π) (t : H) :
      P.root (r j) (centerQuotientCartanMap H t) =
        characterDifferentialOnImage π hπ j.val t :=
    ReductiveCharacterCenterQuotientRootEquiv.apply_map I hI π hπ hker hB
      (borelRootCharacterOccurring J π j) t
  have hroot : P.root (r i) = m.sum fun j e => e • P.root (r j) := by
    ext h
    obtain ⟨t, rfl⟩ := centerQuotientCartanMap_surjective H h
    rw [hr, ← hrel, CharacterDifferentialOnImage.finsupp_prod]
    simp only [Finsupp.sum, LinearMap.sum_apply,
      LinearMap.smul_apply, hr]
  have hK := congrArg (rootHeightLinearForm P b) hroot
  simp only [Finsupp.sum, map_sum, map_nsmul, rootHeightLinearForm_root] at hK
  change b.height (r i) = ∑ j ∈ m.support, (m j : ℤ) * b.height (r j)
  apply Int.cast_injective (α := K)
  rw [hK, Int.cast_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp [nsmul_eq_mul]

/-- The base selected by the Borel makes every Borel root
character positive. -/
theorem exists_borelRootCharacter_positive_base
    (I J : HopfIdeal K B) (hJI : J ≤ I)
    (hI : HopfIdeal.IsMaximalTorus K (CommHopfAlgCat.of K B) I)
    (hJ : HopfIdeal.IsBorel K (CommHopfAlgCat.of K B) J)
    (π : B →ₐc[K] MonoidAlgebra K M) (hπ : Function.Surjective π)
    (hker : ∀ a : B, π a = 0 ↔ a ∈ I.toIdeal)
    (hB : reductiveCommHopfAlgProperty K (FiniteTypeCommHopfAlgCat.of K B)) :
    letI := finiteTypeAffineGroup_tangent_finite (K := K) (B := B)
    letI := MaximalTorusLieCartan.maximalTorus_coordinateTangent_isCartan I hI π hπ hker hB
    letI := ReductiveTorusRootSystem.tangent_centerQuotient_isKilling hB
    letI := ReductiveTorusRootSystem.coordinateCenterQuotient_isCartan I hI π hπ hker hB
    ∃ b : (rootSystem (centerQuotientCartan (diagonalizableTangentImage π))).Base,
      ∀ i : borelRootCharacterIndex J π,
        b.IsPos (ReductiveCharacterRoots.characterCenterQuotientRootEquiv I hI π hπ hker hB
          (borelRootCharacterOccurring J π i)) := by
  let _ := finiteTypeAffineGroup_tangent_finite (K := K) (B := B)
  let _ := MaximalTorusLieCartan.maximalTorus_coordinateTangent_isCartan I hI π hπ hker hB
  let _ := ReductiveTorusRootSystem.tangent_centerQuotient_isKilling hB
  let _ := ReductiveTorusRootSystem.coordinateCenterQuotient_isCartan I hI π hπ hker hB
  obtain ⟨b, hb⟩ := exists_borel_character_positive_base I J hJI hI hJ π hπ hker hB
  refine ⟨b, fun i => (hb _).mpr ?_⟩
  let S := (derivationCompLieHom (B := K)
    (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B) J).hom).range
  let W := affineGroupCharacterWeightSpace π i.val
  obtain ⟨d, hd, hd0⟩ := (Submodule.ne_bot_iff _).mp i.property.2
  let C : Submodule K W := S.toSubmodule.comap W.subtype
  have hfin : Module.finrank K W = 1 :=
    ReductiveCharacterRoots.characterWeightSpace_finrank_eq_one I hI π hπ hker hB i.val
      i.property.1 (borelRootCharacterOccurring J π i).property.1
  let _ : IsSimpleOrder (Submodule K W) := is_simple_module_of_finrank_eq_one hfin
  have hCne : C ≠ ⊥ := by
    intro hC
    have hmem : (⟨d, hd.2⟩ : W) ∈ C := hd.1
    rw [hC] at hmem
    exact hd0 (by simpa using hmem)
  have hCtop : C = ⊤ := (eq_bot_or_eq_top C).resolve_left hCne
  intro z hz
  have hzC : (⟨z, hz⟩ : W) ∈ C := by rw [hCtop]; trivial
  exact hzC

/-- Positive natural degrees on the Borel root characters that
respect every monomial character relation. They are the root heights for
the base selected by the Borel. -/
theorem BorelRootCharacterHeights.exists_positive_degrees
    (I J : HopfIdeal K B) (hJI : J ≤ I)
    (hI : HopfIdeal.IsMaximalTorus K (CommHopfAlgCat.of K B) I)
    (hJ : HopfIdeal.IsBorel K (CommHopfAlgCat.of K B) J)
    (π : B →ₐc[K] MonoidAlgebra K M) (hπ : Function.Surjective π)
    (hker : ∀ a : B, π a = 0 ↔ a ∈ I.toIdeal)
    (hB : reductiveCommHopfAlgProperty K (FiniteTypeCommHopfAlgCat.of K B)) :
    ∃ d : borelRootCharacterIndex J π → ℕ, (∀ i, 0 < d i) ∧
      ∀ (m : borelRootCharacterIndex J π →₀ ℕ) (i : borelRootCharacterIndex J π),
        (m.prod fun j e => j.val ^ e) = i.val → m.weight d = d i := by
  let _ := finiteTypeAffineGroup_tangent_finite (K := K) (B := B)
  let _ := MaximalTorusLieCartan.maximalTorus_coordinateTangent_isCartan I hI π hπ hker hB
  let _ := ReductiveTorusRootSystem.tangent_centerQuotient_isKilling hB
  let _ := ReductiveTorusRootSystem.coordinateCenterQuotient_isCartan I hI π hπ hker hB
  obtain ⟨b, hpos⟩ :=
    exists_borelRootCharacter_positive_base I J hJI hI hJ π hπ hker hB
  let h : borelRootCharacterIndex J π → ℤ := fun j =>
    b.height (ReductiveCharacterRoots.characterCenterQuotientRootEquiv I hI π hπ hker hB
      (borelRootCharacterOccurring J π j))
  have hh (j) : 0 < h j := hpos j
  refine ⟨fun j => (h j).toNat, fun j => by simpa using hh j, ?_⟩
  intro m i hrel
  have hrel' := borelRootCharacter_height_eq_sum I J hI π hπ hker hB b m i hrel
  apply Nat.cast_injective (R := ℤ)
  rw [Finsupp.weight_apply, Finsupp.sum, Nat.cast_sum]
  change _ = ((h i).toNat : ℤ)
  rw [Int.toNat_of_nonneg (hh i).le]
  change h i = ∑ j ∈ m.support, (m j : ℤ) * h j at hrel'
  rw [hrel']
  symm
  apply Finset.sum_congr rfl
  intro j _
  simp [Int.toNat_of_nonneg (hh j).le]

end ReductiveGroups
