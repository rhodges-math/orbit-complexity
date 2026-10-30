import OrbitComplexity.ReductiveGroups.Groups.Borel.BorelCompatibleBase
import OrbitComplexity.ReductiveGroups.Groups.Borel.BorelCenterQuotientMaximality
import OrbitComplexity.ReductiveGroups.Groups.Characters.CharacterRootSubalgebraContainment
import OrbitComplexity.ReductiveGroups.Groups.Characters.CharacterGaSubgroupContainment
import OrbitComplexity.ReductiveGroups.Lie.Roots.PositiveRootHullSolvable

/-!
# Borel Positive Chamber

The positive chamber determined by the original Borel, in the root
system of the center quotient and then in the original characters. -/

noncomputable section
namespace ReductiveGroups
open LieAlgebra LieAlgebra.IsKilling LieModule

universe u
variable {K B ι : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  [CommRing B] [HopfAlgebra K B] [Algebra.FiniteType K B] [Finite ι]

local notation "𝔤" => Derivation K B (TauCeti.Bialgebra.CounitAlgebra K B K)

/-- For these parameters,

```lean
let q
```
-/
theorem exists_borel_centerQuotient_positiveHull
    (I J : TauCeti.HopfIdeal K B) (hJI : J ≤ I)
    (hI : TauCeti.HopfIdeal.IsMaximalTorus K (CommHopfAlgCat.of K B) I)
    (hJ : TauCeti.HopfIdeal.IsBorel K (CommHopfAlgCat.of K B) J)
    (π : B →ₐc[K] MonoidAlgebra K (Multiplicative (ι →₀ ℤ)))
    (hπ : Function.Surjective π)
    (hker : ∀ a : B, π a = 0 ↔ a ∈ I.toIdeal)
    (hB : TauCeti.reductiveCommHopfAlgProperty K
      (TauCeti.FiniteTypeCommHopfAlgCat.of K B)) :
    let q := centerQuotientLieHom (K := K) (L := 𝔤)
    let H := (diagonalizableTangentImage π).map q
    let S := ((TauCeti.derivationCompLieHom (B := K)
      (TauCeti.CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B) J).hom).range).map q
    letI := finiteTypeAffineGroup_tangent_finite (K := K) (B := B)
    letI := ReductiveTorusRootSystem.tangent_centerQuotient_isKilling hB
    letI := ReductiveTorusRootSystem.coordinateCenterQuotient_isCartan I hI π hπ hker hB
    ∃ b : (rootSystem H).Base,
      cartanPositiveRootHull H b = S ∧
      ∀ α : H.root, b.IsPos α ↔
        ∀ z : 𝔤 ⧸ LieAlgebra.center K 𝔤, z ∈ rootSpace H α.val → z ∈ S := by
  let _ := finiteTypeAffineGroup_tangent_finite (K := K) (B := B)
  let _ := ReductiveTorusRootSystem.tangent_centerQuotient_isKilling hB
  let _ := ReductiveTorusRootSystem.coordinateCenterQuotient_isCartan I hI π hπ hker hB
  let q := centerQuotientLieHom (K := K) (L := 𝔤)
  let H := (diagonalizableTangentImage π).map q
  let S := ((TauCeti.derivationCompLieHom (B := K)
    (TauCeti.CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B) J).hom).range).map q
  have hHS : H ≤ S := borel_centerQuotientTorus_le I J hJI π hπ hker
  obtain ⟨b, hb⟩ := BorelCompatibleBase.exists_centerQuotientBase I hI π hπ hker hB J hJ hJI
  have hcontain := CartanStableSubmodule.le_positiveRootHull H S hHS b
    (fun α hα => hb α (fun z hz => hα hz))
  have hSle : S ≤ cartanPositiveRootHull H b := by
    intro z hz
    have hmem := hcontain hz
    change z ∈ (cartanPositiveRootHull H b).toSubmodule
    rw [cartanPositiveRootHull_carrier]
    change z ∈ (H.toLieSubmodule ⊔
      ⨆ (α : H.root) (_ : b.IsPos α), rootSpace H α.val).toSubmodule at hmem
    simpa only [LieSubmodule.sup_toSubmodule, LieSubmodule.iSup_toSubmodule,
      LieSubalgebra.coe_toLieSubmodule] using hmem
  let _ := cartanPositiveRootHull_isSolvable H b
  have heq : cartanPositiveRootHull H b = S :=
    BorelCenterQuotientMaximality.centerQuotientImage_maximal_solvable I J hJI hI hJ hB
      (cartanPositiveRootHull H b) hSle
  refine ⟨b, heq, fun α => ⟨?_, hb α⟩⟩
  intro hα z hz
  have hpos : z ∈ positiveRootLieSubalgebra H b :=
    (le_iSup₂_of_le α hα le_rfl : rootSpace H α.val ≤
      ⨆ (β : H.root) (_ : b.IsPos β), rootSpace H β.val) hz
  change z ∈ S
  rw [← heq]
  exact (le_sup_right : (positiveRootLieSubalgebra H b).toSubmodule ≤
    H.toSubmodule ⊔ (positiveRootLieSubalgebra H b).toSubmodule) hpos

/-- A Borel subgroup determines a root-system base whose positive roots are exactly the
nonidentity torus-character spaces contained in the tangent of that Borel subgroup. -/
theorem exists_borel_character_positive_base
    (I J : TauCeti.HopfIdeal K B) (hJI : J ≤ I)
    (hI : TauCeti.HopfIdeal.IsMaximalTorus K (CommHopfAlgCat.of K B) I)
    (hJ : TauCeti.HopfIdeal.IsBorel K (CommHopfAlgCat.of K B) J)
    (π : B →ₐc[K] MonoidAlgebra K (Multiplicative (ι →₀ ℤ)))
    (hπ : Function.Surjective π)
    (hker : ∀ a : B, π a = 0 ↔ a ∈ I.toIdeal)
    (hB : TauCeti.reductiveCommHopfAlgProperty K
      (TauCeti.FiniteTypeCommHopfAlgCat.of K B)) :
    letI := finiteTypeAffineGroup_tangent_finite (K := K) (B := B)
    letI := MaximalTorusLieCartan.maximalTorus_coordinateTangent_isCartan I hI π hπ hker hB
    letI := ReductiveTorusRootSystem.tangent_centerQuotient_isKilling hB
    letI := ReductiveTorusRootSystem.coordinateCenterQuotient_isCartan I hI π hπ hker hB
    ∃ b : (rootSystem (centerQuotientCartan (diagonalizableTangentImage π))).Base,
      ∀ α : {α : Multiplicative (ι →₀ ℤ) //
        affineGroupCharacterWeightSpace π α ≠ ⊥ ∧ α ≠ 1},
      b.IsPos (ReductiveCharacterRoots.characterCenterQuotientRootEquiv I hI π hπ hker hB α) ↔
        ∀ d : 𝔤, d ∈ affineGroupCharacterWeightSpace π α.val →
          d ∈ (TauCeti.derivationCompLieHom (B := K)
            (TauCeti.CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B) J).hom).range := by
  let _ := finiteTypeAffineGroup_tangent_finite (K := K) (B := B)
  let _ := MaximalTorusLieCartan.maximalTorus_coordinateTangent_isCartan I hI π hπ hker hB
  let _ := ReductiveTorusRootSystem.tangent_centerQuotient_isKilling hB
  let _ := ReductiveTorusRootSystem.coordinateCenterQuotient_isCartan I hI π hπ hker hB
  let D := (TauCeti.derivationCompLieHom (B := K)
    (TauCeti.CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B) J).hom).range
  have hHD : diagonalizableTangentImage π ≤ D := by
    intro d hd
    apply (tangent_mem_hopfQuotient_iff J d).mpr
    intro a ha
    obtain ⟨t, rfl⟩ := hd
    change t (π a) = 0
    rw [(hker a).2 (hJI ha), map_zero]
  obtain ⟨b, _, hb⟩ := exists_borel_centerQuotient_positiveHull I J hJI hI hJ π hπ hker hB
  refine ⟨b, fun α => ?_⟩
  exact (hb _).trans
    (characterRoot_subalgebra_containment_iff I hI π hπ hker hB D hHD α)

/-- A Borel subgroup determines a root-system base for which a nonzero character-root
additive subgroup is positive exactly when it lies in that Borel subgroup. -/
theorem exists_borel_positive_root_subgroups
    (I J : TauCeti.HopfIdeal K B) (hJI : J ≤ I)
    (hI : TauCeti.HopfIdeal.IsMaximalTorus K (CommHopfAlgCat.of K B) I)
    (hJ : TauCeti.HopfIdeal.IsBorel K (CommHopfAlgCat.of K B) J)
    (π : B →ₐc[K] MonoidAlgebra K (Multiplicative (ι →₀ ℤ)))
    (hπ : Function.Surjective π)
    (hker : ∀ a : B, π a = 0 ↔ a ∈ I.toIdeal)
    (hB : TauCeti.reductiveCommHopfAlgProperty K
      (TauCeti.FiniteTypeCommHopfAlgCat.of K B)) :
    letI := finiteTypeAffineGroup_tangent_finite (K := K) (B := B)
    letI := MaximalTorusLieCartan.maximalTorus_coordinateTangent_isCartan I hI π hπ hker hB
    letI := ReductiveTorusRootSystem.tangent_centerQuotient_isKilling hB
    letI := ReductiveTorusRootSystem.coordinateCenterQuotient_isCartan I hI π hπ hker hB
    ∃ b : (rootSystem (centerQuotientCartan (diagonalizableTangentImage π))).Base,
      ∀ α : {α : Multiplicative (ι →₀ ℤ) //
        affineGroupCharacterWeightSpace π α ≠ ⊥ ∧ α ≠ 1},
      ∀ x : B →ₐc[K] SymmetricAlgebra K K,
      gaAffineGroupTangent x ∈ affineGroupCharacterWeightSpace π α.val →
      gaAffineGroupTangent x ≠ 0 →
      (b.IsPos (ReductiveCharacterRoots.characterCenterQuotientRootEquiv I hI π hπ hker hB α) ↔
        ∀ a ∈ J, x a = 0) := by
  let _ := finiteTypeAffineGroup_tangent_finite (K := K) (B := B)
  let _ := MaximalTorusLieCartan.maximalTorus_coordinateTangent_isCartan I hI π hπ hker hB
  let _ := ReductiveTorusRootSystem.tangent_centerQuotient_isKilling hB
  let _ := ReductiveTorusRootSystem.coordinateCenterQuotient_isCartan I hI π hπ hker hB
  obtain ⟨b, hb⟩ := exists_borel_character_positive_base I J hJI hI hJ π hπ hker hB
  refine ⟨b, fun α x hx hx0 => ?_⟩
  exact (hb α).trans
    (CharacterGa.kills_iff_weightSpace_contained I hI π hπ hker hB
      α.val α.property.2 J x hx hx0).symm

end ReductiveGroups
