import OrbitComplexity.ReductiveGroups.Groups.RootCoordinates.RootSubsetProduct
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupRootProducts

/-!
# Multiplication coordinates for root-support subgroups

Disjoint closed positive-root supports give an isomorphism from the coordinate
algebra of their union to the tensor product of the two subgroup coordinate algebras.
The isomorphism is the pullback of the restricted group multiplication.
-/

noncomputable section
namespace ReductiveGroups.ReductiveGroupData
open TauCeti
open scoped TensorProduct
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

/-- Multiplication of two disjoint closed root supports is a coordinate algebra isomorphism. -/
def rootSubsetProductEquiv (R R₁ R₂ : Set G.rootIndex)
    (hR : IsPositiveRootClosed G.rootBase R)
    (hR₁ : IsPositiveRootClosed G.rootBase R₁) (hR₂ : IsPositiveRootClosed G.rootBase R₂)
    (hunion : R = R₁ ∪ R₂) (hdisj : Disjoint R₁ R₂) :
    G.rootSubsetAlgebra R hR ≃ₐ[K] G.rootSubsetAlgebra R₁ hR₁ ⊗[K]
      G.rootSubsetAlgebra R₂ hR₂ := by
  let _ := finite_borelRootCharacterIndex G.borelIdeal G.torusSplit G.split_surjective
  let _ : Fintype (G.rootCharacters R₁) := Fintype.ofFinite _
  let _ : Fintype (G.rootCharacters R₂) := Fintype.ofFinite _
  have hchars : G.rootCharacters R = G.rootCharacters R₁ ∪ G.rootCharacters R₂ := by
    ext i
    change _ ∈ R ↔ _ ∈ R₁ ∨ _ ∈ R₂
    rw [hunion]
    rfl
  have hdchars : Disjoint (G.rootCharacters R₁) (G.rootCharacters R₂) := by
    rw [Set.disjoint_left]
    intro i hi₁ hi₂
    exact Set.disjoint_left.mp hdisj hi₁ hi₂
  exact BorelRootSubset.productCoordinateEquiv G.torusIdeal G.borelIdeal G.borel_le_torus
    G.isMaximalTorus G.isBorel G.torusSplit G.split_surjective G.split_eq_zero G.reductive
    G.borelRootMaps G.borelRootBasis G.borelRootBasis_tangent G.borelRootMaps_weight
    (G.rootCharacters R) (G.rootCharacters R₁) (G.rootCharacters R₂)
    (G.rootCharacters_closed R hR) (G.rootCharacters_closed R₁ hR₁)
    (G.rootCharacters_closed R₂ hR₂) hchars hdchars Finset.univ.toList
    (Finset.nodup_toList _) (fun i => Finset.mem_toList.mpr (Finset.mem_univ i))
    Finset.univ.toList (Finset.nodup_toList _)
    (fun i => Finset.mem_toList.mpr (Finset.mem_univ i))

/-- On coordinate classes the root-support product map is the restricted multiplication. -/
theorem rootSubsetProductEquiv_mk (R R₁ R₂ : Set G.rootIndex)
    (hR : IsPositiveRootClosed G.rootBase R)
    (hR₁ : IsPositiveRootClosed G.rootBase R₁) (hR₂ : IsPositiveRootClosed G.rootBase R₂)
    (hunion : R = R₁ ∪ R₂) (hdisj : Disjoint R₁ R₂) (b : G.coordinateAlgebra) :
    G.rootSubsetProductEquiv R R₁ R₂ hR hR₁ hR₂ hunion hdisj (Ideal.Quotient.mk _ b) =
      ((Algebra.TensorProduct.map
        (Ideal.Quotient.mkₐ K (G.rootSubsetIdeal R₁ hR₁).toIdeal)
        (Ideal.Quotient.mkₐ K (G.rootSubsetIdeal R₂ hR₂).toIdeal)).comp
          (Bialgebra.comulAlgHom K G.coordinateAlgebra)) b := by
  unfold rootSubsetProductEquiv
  exact BorelRootSubset.productCoordinateEquiv_mk G.torusIdeal G.borelIdeal G.borel_le_torus
    G.isMaximalTorus G.isBorel G.torusSplit G.split_surjective G.split_eq_zero G.reductive
    G.borelRootMaps G.borelRootBasis G.borelRootBasis_tangent G.borelRootMaps_weight
    (G.rootCharacters R) (G.rootCharacters R₁) (G.rootCharacters R₂)
    (G.rootCharacters_closed R hR) (G.rootCharacters_closed R₁ hR₁)
    (G.rootCharacters_closed R₂ hR₂) _ _ _ _ _ _ _ _ b

end ReductiveGroups.ReductiveGroupData
