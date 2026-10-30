import OrbitComplexity.ReductiveGroups.Groups.Tangents.CharacterDifferential
import OrbitComplexity.ReductiveGroups.Groups.Tangents.CharacterDifferentialInjective
import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Weight
import Mathlib.Algebra.Module.Submodule.Union
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable

/-!
# Torus Invariant Subspace Weights

Tangent operators of a split diagonalizable-group comodule,
computed on its algebraic character weight spaces. -/

noncomputable section
namespace ReductiveGroups

open TauCeti
open scoped TensorProduct

variable {K M V : Type*} [Field K] [CommGroup M]
  [AddCommGroup V] [Module K V]
  [Comodule K (MonoidAlgebra K M) V]

/-- Apply a torus tangent derivation to the coaction of a vector,
then identify the scalar tensor factor with the original vector space. -/
def torusTangentOperator
    (h : Derivation K (MonoidAlgebra K M)
      (Bialgebra.CounitAlgebra K (MonoidAlgebra K M) K)) :
    Module.End K V :=
  (TensorProduct.rid K V).toLinearMap ∘ₗ
    (TensorProduct.map LinearMap.id
      ((Bialgebra.CounitAlgebra.algEquivSelf K (MonoidAlgebra K M) K).toLinearMap.comp
        h.toLinearMap)) ∘ₗ
      Comodule.coact (R := K) (C := MonoidAlgebra K M) (M := V)

/-- On the `α`-weight space of a split torus comodule, its
tangent derivation acts by the differentiated character `α`. -/
theorem torusTangentOperator_weight
    (h : Derivation K (MonoidAlgebra K M)
      (Bialgebra.CounitAlgebra K (MonoidAlgebra K M) K))
    (α : M) {v : V} (hv : v ∈ Comodule.weightSpace K M V α) :
    torusTangentOperator h v = characterDifferential α h • v := by
  rw [torusTangentOperator, LinearMap.comp_apply, LinearMap.comp_apply,
    Comodule.mem_weightSpace.mp hv]
  simp only [TensorProduct.map_tmul, LinearMap.id_apply,
    LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    TensorProduct.rid_tmul,
    characterDifferential_apply]
  rfl

/-- A single tangent derivation distinguishes any prescribed finite
set of characters of a free split torus in characteristic zero. -/
theorem exists_torusTangent_separating_finite
    {ι : Type*} [CharZero K] (s : Finset (Multiplicative (ι →₀ ℤ))) :
    ∃ h : Derivation K (MonoidAlgebra K (Multiplicative (ι →₀ ℤ)))
      (Bialgebra.CounitAlgebra K (MonoidAlgebra K (Multiplicative (ι →₀ ℤ))) K),
      Set.InjOn (fun α => characterDifferential α h) s := by
  classical
  let P := (s.product s).filter (fun ab => ab.1 ≠ ab.2)
  let p : P → Submodule K
      (Derivation K (MonoidAlgebra K (Multiplicative (ι →₀ ℤ)))
        (Bialgebra.CounitAlgebra K (MonoidAlgebra K (Multiplicative (ι →₀ ℤ))) K)) :=
    fun ab => LinearMap.ker
      (characterDifferential (K := K) ab.1.1 - characterDifferential ab.1.2)
  have hp (ab : P) : p ab ≠ ⊤ := by
    intro htop
    have hz : characterDifferential (K := K) ab.1.1 -
        characterDifferential ab.1.2 = 0 := by
      apply LinearMap.ker_eq_top.mp
      exact htop
    have heq : characterDifferential (K := K) ab.1.1 =
        characterDifferential ab.1.2 := sub_eq_zero.mp hz
    have hab : ab.1.1 ≠ ab.1.2 := (Finset.mem_filter.mp ab.2).2
    exact hab ((characterDifferential_injective (K := K)) heq)
  have hcard : (Finset.univ : Finset P).card < ENat.card K := by
    rw [ENat.card_eq_top_of_infinite]
    simp
  have hproper := Submodule.iUnion_ssubset_of_forall_ne_top_of_card_lt
    (Finset.univ : Finset P) p hp hcard
  obtain ⟨h, hh⟩ := Set.ssubset_univ_iff_nonempty_compl.mp hproper
  change h ∉ ⋃ ab ∈ (Finset.univ : Finset P), (p ab : Set _) at hh
  refine ⟨h, ?_⟩
  intro α hα β hβ heq
  by_contra hne
  let ab : P := ⟨(α, β), Finset.mem_filter.mpr
    ⟨Finset.mem_product.mpr ⟨hα, hβ⟩, hne⟩⟩
  have habmem : h ∈ p ab := by
    change ((characterDifferential (K := K) α - characterDifferential (K := K) β) :
      Derivation K (MonoidAlgebra K (Multiplicative (ι →₀ ℤ)))
        (Bialgebra.CounitAlgebra K (MonoidAlgebra K (Multiplicative (ι →₀ ℤ))) K) →ₗ[K] K) h = 0
    simpa only [LinearMap.sub_apply, sub_eq_zero] using heq
  exact hh (Set.mem_iUnion.mpr ⟨ab,
    Set.mem_iUnion.mpr ⟨Finset.mem_univ _, habmem⟩⟩)

end ReductiveGroups
