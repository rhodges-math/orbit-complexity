import OrbitComplexity.ReductiveGroups.Groups.Characters.AffineGroupCharacterWeights
import OrbitComplexity.ReductiveGroups.Groups.Representations.AdjointRepresentation
import Mathlib.Data.Fintype.EquivFin

/-!
# Character Weight Decomposition

The tangent derivations are spanned by diagonalizable-group character weights. -/

noncomputable section
namespace ReductiveGroups

universe u
variable {K B M : Type u} [Field K] [CommRing B] [HopfAlgebra K B]
  [Algebra.FiniteType K B] [CommGroup M]

/-- The character weight spaces on the original group's tangent derivations span its Lie
algebra.  -/
theorem ISup.affineGroupCharacterWeightSpace_eq_top
    (π : B →ₐc[K] MonoidAlgebra K M) :
    (⨆ α, affineGroupCharacterWeightSpace π α) = ⊤ := by
  classical
  let e := Derivation.cotangentLinearEquiv (R := K) (A := B) (B := K)
  have hweight (α : M) : affineGroupCharacterWeightSpace π α =
      (Derivation.adjointWeightSpace π α).map e.toLinearMap := by
    exact (Submodule.map_equiv_eq_comap_symm e _).symm
  simp_rw [hweight]
  rw [← Submodule.map_iSup]
  rw [(Derivation.isInternal_adjointWeightSpace π).submodule_iSup_eq_top]
  rw [Submodule.map_top]
  exact LinearMap.range_eq_top.mpr e.surjective

end ReductiveGroups

open TauCeti
open scoped TensorProduct
noncomputable section
universe u
namespace ReductiveGroups
variable {K B M : Type u} [Field K] [CommRing B] [HopfAlgebra K B]
  [Algebra.FiniteType K B] [CommGroup M]

/-- Coordinates of the character decomposition of the tangent representation. -/
abbrev adjointWeightIndex (π : B →ₐc[K] MonoidAlgebra K M) :=
  Σ χ : M, Fin (Module.finrank K (Derivation.adjointWeightSpace π χ))

private def rawWeightBasis (π : B →ₐc[K] MonoidAlgebra K M) :
    Module.Basis (adjointWeightIndex π) K (Module.Dual K (Bialgebra.CotangentSpace K B)) := by
  classical
  exact (Derivation.isInternal_adjointWeightSpace π).collectedBasis
    (fun χ => Module.finBasis K (Derivation.adjointWeightSpace π χ))

/-- There are finitely many basis coordinates in the tangent character decomposition. -/
instance instFiniteAdjointWeightIndex (π : B →ₐc[K] MonoidAlgebra K M) :
    Finite (adjointWeightIndex π) :=
  (rawWeightBasis π).linearIndependent.finite

/-- The finite coordinate type of the tangent character decomposition. -/
noncomputable instance instFintypeAdjointWeightIndex (π : B →ₐc[K] MonoidAlgebra K M) :
    Fintype (adjointWeightIndex π) := Fintype.ofFinite _

/-- The number of coordinates in the tangent character decomposition. -/
abbrev adjointWeightRank (π : B →ₐc[K] MonoidAlgebra K M) : ℕ :=
  Fintype.card (adjointWeightIndex π)

/-- A character basis of the counit-valued tangent derivations. -/
def adjointWeightBasis (π : B →ₐc[K] MonoidAlgebra K M) :
    Module.Basis (Fin (adjointWeightRank π)) K
      (Derivation K B (Bialgebra.CounitAlgebra K B K)) :=
  ((rawWeightBasis π).map
    (Derivation.cotangentLinearEquiv (R := K) (A := B) (B := K))).reindex
      (Fintype.equivFin (adjointWeightIndex π))

/-- The character of a coordinate in the tangent character basis. -/
def adjointWeightCharacter (π : B →ₐc[K] MonoidAlgebra K M)
    (i : Fin (adjointWeightRank π)) : M :=
  ((Fintype.equivFin (adjointWeightIndex π)).symm i).1

/-- Every tangent basis vector belongs to its character subspace. -/
theorem adjointWeightBasis_mem (π : B →ₐc[K] MonoidAlgebra K M)
    (i : Fin (adjointWeightRank π)) :
    adjointWeightBasis π i ∈ affineGroupCharacterWeightSpace π (adjointWeightCharacter π i) := by
  classical
  let a := (Fintype.equivFin (adjointWeightIndex π)).symm i
  have ha : rawWeightBasis π a ∈ Derivation.adjointWeightSpace π a.1 :=
    (Derivation.isInternal_adjointWeightSpace π).collectedBasis_mem
      (fun χ => Module.finBasis K (Derivation.adjointWeightSpace π χ)) a
  change (Derivation.cotangentLinearEquiv (R := K) (A := B) (B := K)).symm
    (adjointWeightBasis π i) ∈ Derivation.adjointWeightSpace π a.1
  simpa only [adjointWeightBasis, Module.Basis.reindex_apply, Module.Basis.map_apply,
    LinearEquiv.symm_apply_apply] using ha

/-- Torus points scale the tangent character basis by its characters. -/
theorem adjointWeightBasis_torus (π : B →ₐc[K] MonoidAlgebra K M)
    (z : WithConv (MonoidAlgebra K M →ₐ[K] K)) (i : Fin (adjointWeightRank π)) :
    affineGroupAdjointRepresentation (AlgHom.mapDomain π z) (adjointWeightBasis π i) =
      z.ofConv (MonoidAlgebra.single (adjointWeightCharacter π i) (1 : K)) •
        adjointWeightBasis π i :=
  AffineGroupAdjoint.eq_character_of_mem_weight π (adjointWeightCharacter π i) z _
    (adjointWeightBasis_mem π i)

/-- Restricting the adjoint coaction makes each tangent basis vector a character vector. -/
theorem adjointWeightBasis_coact (π : B →ₐc[K] MonoidAlgebra K M)
    (i : Fin (adjointWeightRank π)) :
    let := affineGroupAdjointComodule (K := K) (B := B)
    TensorProduct.map LinearMap.id π.toCoalgHom.toLinearMap
        (Comodule.coact (R := K) (C := B) (adjointWeightBasis π i)) =
      adjointWeightBasis π i ⊗ₜ[K]
        MonoidAlgebra.single (adjointWeightCharacter π i) (1 : K) := by
  let := Derivation.adjointComodule (R := K) (H := B)
  have hi := Derivation.mem_adjointWeightSpace.mp (adjointWeightBasis_mem π i)
  change TensorProduct.map LinearMap.id π.toCoalgHom.toLinearMap
      (Comodule.coact (R := K) (C := B)
        ((Derivation.cotangentLinearEquiv (R := K) (A := B) (B := K)).symm
          (adjointWeightBasis π i))) =
    (Derivation.cotangentLinearEquiv (R := K) (A := B) (B := K)).symm
      (adjointWeightBasis π i) ⊗ₜ[K]
        MonoidAlgebra.single (adjointWeightCharacter π i) (1 : K) at hi
  have he := congrArg
    (TensorProduct.map
      (Derivation.cotangentLinearEquiv (R := K) (A := B) (B := K)).toLinearMap LinearMap.id) hi
  let := affineGroupAdjointComodule (K := K) (B := B)
  change TensorProduct.map LinearMap.id π.toCoalgHom.toLinearMap
      (TensorProduct.map
        (Derivation.cotangentLinearEquiv (R := K) (A := B) (B := K)).toLinearMap LinearMap.id
        (Comodule.coact (R := K) (C := B)
          ((Derivation.cotangentLinearEquiv (R := K) (A := B) (B := K)).symm
            (adjointWeightBasis π i)))) = _
  simpa only [TensorProduct.map_map, LinearMap.comp_id, LinearMap.id_comp,
    TensorProduct.map_tmul, LinearMap.id_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply] using he

/-- The tangent character basis is a weight basis of the adjoint comodule. -/
theorem adjointWeightBasis_weightSpace (π : B →ₐc[K] MonoidAlgebra K M)
    (i : Fin (adjointWeightRank π)) :
    let := affineGroupAdjointComodule (K := K) (B := B)
    adjointWeightBasis π i ∈ DiagonalizableGroup.weightSpace
      (Derivation K B (Bialgebra.CounitAlgebra K B K)) π.toCoalgHom
        (adjointWeightCharacter π i) := by
  let := affineGroupAdjointComodule (K := K) (B := B)
  exact DiagonalizableGroup.mem_weightSpace.mpr (adjointWeightBasis_coact π i)

end ReductiveGroups
