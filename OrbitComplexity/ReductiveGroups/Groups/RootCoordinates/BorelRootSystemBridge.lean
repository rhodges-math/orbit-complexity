import OrbitComplexity.ReductiveGroups.Groups.RootCoordinates.BorelRootClosedSubset
import OrbitComplexity.ReductiveGroups.Roots.Inversions.PositiveRootClosedSets

/-!
# Borel Root System Bridge

The bridge between original Borel root characters and the positive roots
of the center-quotient root system, for the base selected by the
original Borel. Closed sets of positive roots give closed sets of Borel
root characters, hence root subgroups `U_S`. -/

noncomputable section
namespace ReductiveGroups

open TauCeti LieAlgebra LieAlgebra.IsKilling LieModule

universe u
variable {K B ι : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  [CommRing B] [HopfAlgebra K B] [Algebra.FiniteType K B] [Finite ι]

local notation "𝔤" => Derivation K B (Bialgebra.CounitAlgebra K B K)
local notation "M" => Multiplicative (ι →₀ ℤ)

/-- The base of the center-quotient root system selected by the
original Borel: a root is positive exactly when its original character
space lies in the original Borel tangent. -/
noncomputable def borelRootBase
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
    (rootSystem (centerQuotientCartan (diagonalizableTangentImage π))).Base :=
  Classical.choose (exists_borel_character_positive_base I J hJI hI hJ π hπ hker hB)

/-- A root is positive for the chosen Borel base exactly when its corresponding
torus-character space lies in the tangent of the Borel subgroup. -/
theorem borelRootBase_isPos_iff
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
    ∀ α : {α : M // affineGroupCharacterWeightSpace π α ≠ ⊥ ∧ α ≠ 1},
      (borelRootBase I J hJI hI hJ π hπ hker hB).IsPos
          (ReductiveCharacterRoots.characterCenterQuotientRootEquiv I hI π hπ hker hB α) ↔
        ∀ d : 𝔤, d ∈ affineGroupCharacterWeightSpace π α.val →
          d ∈ (derivationCompLieHom (B := K)
            (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B) J).hom).range :=
  Classical.choose_spec (exists_borel_character_positive_base I J hJI hI hJ π hπ hker hB)

/-- Every Borel root character is positive for the Borel base. -/
theorem borelRootBase_isPos
    (I J : HopfIdeal K B) (hJI : J ≤ I)
    (hI : HopfIdeal.IsMaximalTorus K (CommHopfAlgCat.of K B) I)
    (hJ : HopfIdeal.IsBorel K (CommHopfAlgCat.of K B) J)
    (π : B →ₐc[K] MonoidAlgebra K M) (hπ : Function.Surjective π)
    (hker : ∀ a : B, π a = 0 ↔ a ∈ I.toIdeal)
    (hB : reductiveCommHopfAlgProperty K (FiniteTypeCommHopfAlgCat.of K B))
    (i : borelRootCharacterIndex J π) :
    letI := finiteTypeAffineGroup_tangent_finite (K := K) (B := B)
    letI := MaximalTorusLieCartan.maximalTorus_coordinateTangent_isCartan I hI π hπ hker hB
    letI := ReductiveTorusRootSystem.tangent_centerQuotient_isKilling hB
    letI := ReductiveTorusRootSystem.coordinateCenterQuotient_isCartan I hI π hπ hker hB
    (borelRootBase I J hJI hI hJ π hπ hker hB).IsPos
      (ReductiveCharacterRoots.characterCenterQuotientRootEquiv I hI π hπ hker hB
        (borelRootCharacterOccurring J π i)) := by
  let _ := finiteTypeAffineGroup_tangent_finite (K := K) (B := B)
  let _ := MaximalTorusLieCartan.maximalTorus_coordinateTangent_isCartan I hI π hπ hker hB
  let _ := ReductiveTorusRootSystem.tangent_centerQuotient_isKilling hB
  let _ := ReductiveTorusRootSystem.coordinateCenterQuotient_isCartan I hI π hπ hker hB
  apply (borelRootBase_isPos_iff I J hJI hI hJ π hπ hker hB _).mpr
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

/-- A monomial relation among Borel root characters is the same
nonnegative integral relation among their roots. -/
theorem borelRootCharacter_root_eq_sum
    (I J : HopfIdeal K B)
    (hI : HopfIdeal.IsMaximalTorus K (CommHopfAlgCat.of K B) I)
    (π : B →ₐc[K] MonoidAlgebra K M) (hπ : Function.Surjective π)
    (hker : ∀ a : B, π a = 0 ↔ a ∈ I.toIdeal)
    (hB : reductiveCommHopfAlgProperty K (FiniteTypeCommHopfAlgCat.of K B)) :
    letI := finiteTypeAffineGroup_tangent_finite (K := K) (B := B)
    letI := MaximalTorusLieCartan.maximalTorus_coordinateTangent_isCartan I hI π hπ hker hB
    letI := ReductiveTorusRootSystem.tangent_centerQuotient_isKilling hB
    letI := ReductiveTorusRootSystem.coordinateCenterQuotient_isCartan I hI π hπ hker hB
    ∀ (m : borelRootCharacterIndex J π →₀ ℕ) (i : borelRootCharacterIndex J π),
      (m.prod fun j e => j.val ^ e) = i.val →
      (rootSystem (centerQuotientCartan (diagonalizableTangentImage π))).root
          (ReductiveCharacterRoots.characterCenterQuotientRootEquiv I hI π hπ hker hB
            (borelRootCharacterOccurring J π i)) =
        m.sum fun j e => e • (rootSystem (centerQuotientCartan
          (diagonalizableTangentImage π))).root
            (ReductiveCharacterRoots.characterCenterQuotientRootEquiv I hI π hπ hker hB
              (borelRootCharacterOccurring J π j)) := by
  let _ := finiteTypeAffineGroup_tangent_finite (K := K) (B := B)
  let _ := MaximalTorusLieCartan.maximalTorus_coordinateTangent_isCartan I hI π hπ hker hB
  let _ := ReductiveTorusRootSystem.tangent_centerQuotient_isKilling hB
  let _ := ReductiveTorusRootSystem.coordinateCenterQuotient_isCartan I hI π hπ hker hB
  intro m i hrel
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
  change P.root (r i) = m.sum fun j e => e • P.root (r j)
  ext h
  obtain ⟨t, rfl⟩ := centerQuotientCartanMap_surjective H h
  rw [hr, ← hrel, CharacterDifferentialOnImage.finsupp_prod]
  simp only [Finsupp.sum, LinearMap.sum_apply, LinearMap.smul_apply, hr]

/-- **Closed sets transfer.** A set of roots closed among the positive roots
of the Borel base gives a closed set of Borel root characters. -/
theorem IsBorelRootCharacterClosed.of_isPositiveRootClosed
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
    ∀ R : Set (centerQuotientCartan (diagonalizableTangentImage π)).root,
      IsPositiveRootClosed (borelRootBase I J hJI hI hJ π hπ hker hB) R →
      IsBorelRootCharacterClosed J π
        {i | ReductiveCharacterRoots.characterCenterQuotientRootEquiv I hI π hπ hker hB
          (borelRootCharacterOccurring J π i) ∈ R} := by
  let _ := finiteTypeAffineGroup_tangent_finite (K := K) (B := B)
  let _ := MaximalTorusLieCartan.maximalTorus_coordinateTangent_isCartan I hI π hπ hker hB
  let _ := ReductiveTorusRootSystem.tangent_centerQuotient_isKilling hB
  let _ := ReductiveTorusRootSystem.coordinateCenterQuotient_isCartan I hI π hπ hker hB
  intro R hR m i hm hrel
  apply hR _ (borelRootBase_isPos I J hJI hI hJ π hπ hker hB i)
  rw [borelRootCharacter_root_eq_sum I J hI π hπ hker hB m i hrel]
  apply AddSubmonoid.sum_mem
  intro j hj
  have hmem : (rootSystem (centerQuotientCartan (diagonalizableTangentImage π))).root
      (ReductiveCharacterRoots.characterCenterQuotientRootEquiv I hI π hπ hker hB
        (borelRootCharacterOccurring J π j)) ∈
      (rootSystem (centerQuotientCartan (diagonalizableTangentImage π))).root '' R :=
    ⟨_, hm hj, rfl⟩
  exact AddSubmonoid.nsmul_mem _ (AddSubmonoid.subset_closure hmem) _

end ReductiveGroups
