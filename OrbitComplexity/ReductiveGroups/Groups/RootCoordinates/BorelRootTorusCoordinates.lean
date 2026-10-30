import OrbitComplexity.ReductiveGroups.Groups.Exponential.BorelRootExponentialConjugation
import OrbitComplexity.ReductiveGroups.Groups.Unipotent.BorelRootUnipotentLieDecomposition
import OrbitComplexity.ReductiveGroups.Groups.Characters.AffineGroupCharacterWeights

/-!
# Borel Root Torus Coordinates

The split torus acts on the Borel Ga-only exponential
coordinates through the original character-weight decomposition. -/

noncomputable section
namespace ReductiveGroups

open TauCeti

universe u
variable {K B ι : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  [CommRing B] [HopfAlgebra K B] [Algebra.FiniteType K B] [Finite ι]

local notation "𝔤" => Derivation K B (Bialgebra.CounitAlgebra K B K)
local notation "M" => Multiplicative (ι →₀ ℤ)

/-- Original split-torus points preserve the tangent of the
Borel's Ga-only subgroup, via its proved nonidentity-character decomposition. -/
theorem borelRootUnipotentTangent_torus_ad_mem
    (I J : HopfIdeal K B) (hJI : J ≤ I)
    (hI : HopfIdeal.IsMaximalTorus K (CommHopfAlgCat.of K B) I)
    (hJ : HopfIdeal.IsBorel K (CommHopfAlgCat.of K B) J)
    (π : B →ₐc[K] MonoidAlgebra K M) (hπ : Function.Surjective π)
    (hker : ∀ a : B, π a = 0 ↔ a ∈ I.toIdeal)
    (hB : reductiveCommHopfAlgProperty K (FiniteTypeCommHopfAlgCat.of K B))
    (t : WithConv (MonoidAlgebra K M →ₐ[K] K))
    (d : (derivationCompLieHom (B := K)
      (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B)
        (borelRootUnipotentHopfIdeal J π hπ)).hom).range) :
    affineGroupAdjointRepresentation (AlgHom.mapDomain π t) d.val ∈
      (derivationCompLieHom (B := K)
        (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B)
          (borelRootUnipotentHopfIdeal J π hπ)).hom).range := by
  let U := (derivationCompLieHom (B := K)
    (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B)
      (borelRootUnipotentHopfIdeal J π hπ)).hom).range
  let S := (derivationCompLieHom (B := K)
    (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B) J).hom).range
  let N : Submodule K 𝔤 := ⨆ (α : M) (_ : α ≠ 1),
    S.toSubmodule ⊓ affineGroupCharacterWeightSpace π α
  have hdecomp : U.toSubmodule = N :=
    BorelRootUnipotentTangent.eq_character_sum I J hJI hI hJ π hπ hker hB
  have hpres : N ≤ U.toSubmodule.comap (affineGroupAdjointRepresentation
      (AlgHom.mapDomain π t)) := by
    refine iSup_le fun α => iSup_le fun hα => ?_
    intro v hv
    have hvU : v ∈ U := by
      have hvN : v ∈ N := (le_iSup₂_of_le α hα le_rfl :
        S.toSubmodule ⊓ affineGroupCharacterWeightSpace π α ≤ N) hv
      change v ∈ U.toSubmodule
      rw [hdecomp]
      exact hvN
    change affineGroupAdjointRepresentation (AlgHom.mapDomain π t) v ∈ U
    rw [AffineGroupAdjoint.eq_character_of_mem_weight π α t v hv.2]
    exact U.smul_mem _ hvU
  exact hpres (hdecomp ▸ d.property)

/-- The torus acts on exponential coordinates by its
original adjoint action. The codomain tangent membership is proved above. -/
theorem BorelRootUnipotentExponential.torus_conjugate
    (I J : HopfIdeal K B) (hJI : J ≤ I)
    (hI : HopfIdeal.IsMaximalTorus K (CommHopfAlgCat.of K B) I)
    (hJ : HopfIdeal.IsBorel K (CommHopfAlgCat.of K B) J)
    (π : B →ₐc[K] MonoidAlgebra K M) (hπ : Function.Surjective π)
    (hker : ∀ a : B, π a = 0 ↔ a ∈ I.toIdeal)
    (hB : reductiveCommHopfAlgProperty K (FiniteTypeCommHopfAlgCat.of K B))
    (t : WithConv (MonoidAlgebra K M →ₐ[K] K))
    (d : (derivationCompLieHom (B := K)
      (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B)
        (borelRootUnipotentHopfIdeal J π hπ)).hom).range) :
    AlgHom.mapDomain π t * borelRootUnipotentExponential J hJ π hπ d *
        (AlgHom.mapDomain π t)⁻¹ =
      borelRootUnipotentExponential J hJ π hπ
        ⟨affineGroupAdjointRepresentation (AlgHom.mapDomain π t) d.val,
          borelRootUnipotentTangent_torus_ad_mem I J hJI hI hJ π hπ hker hB t d⟩ :=
  BorelRootUnipotentExponential.conjugate_of_ad_mem J hJ π hπ
    (AlgHom.mapDomain π t)
    (borelRootUnipotentTangent_torus_ad_mem I J hJI hI hJ π hπ hker hB t) d

/-- The proved exponential bijection is equivariant under each
torus point, including in the inverse direction. -/
theorem BorelRootUnipotentExponentialEquiv.symm_torus_conjugate
    (I J : HopfIdeal K B) (hJI : J ≤ I)
    (hI : HopfIdeal.IsMaximalTorus K (CommHopfAlgCat.of K B) I)
    (hJ : HopfIdeal.IsBorel K (CommHopfAlgCat.of K B) J)
    (π : B →ₐc[K] MonoidAlgebra K M) (hπ : Function.Surjective π)
    (hker : ∀ a : B, π a = 0 ↔ a ∈ I.toIdeal)
    (hB : reductiveCommHopfAlgProperty K (FiniteTypeCommHopfAlgCat.of K B))
    (t : WithConv (MonoidAlgebra K M →ₐ[K] K))
    (u : CommHopfAlgCat.quotientPointsSubgroup (CommHopfAlgCat.of K B)
      (borelRootUnipotentHopfIdeal J π hπ) (CommAlgCat.of K K)) :
    ∃ hu : AlgHom.mapDomain π t * u.val * (AlgHom.mapDomain π t)⁻¹ ∈
        CommHopfAlgCat.quotientPointsSubgroup (CommHopfAlgCat.of K B)
          (borelRootUnipotentHopfIdeal J π hπ) (CommAlgCat.of K K),
      (borelRootUnipotentExponentialEquiv J hJ π hπ).symm
        ⟨AlgHom.mapDomain π t * u.val * (AlgHom.mapDomain π t)⁻¹, hu⟩ =
        ⟨affineGroupAdjointRepresentation (AlgHom.mapDomain π t)
          ((borelRootUnipotentExponentialEquiv J hJ π hπ).symm u).val,
          borelRootUnipotentTangent_torus_ad_mem I J hJI hI hJ π hπ hker hB t
            ((borelRootUnipotentExponentialEquiv J hJ π hπ).symm u)⟩ :=
  BorelRootUnipotentExponentialEquiv.symm_conjugate J hJ π hπ
    (AlgHom.mapDomain π t)
    (borelRootUnipotentTangent_torus_ad_mem I J hJI hI hJ π hπ hker hB t) u

omit [Finite ι] in
/-- On any ordered finite product of character-weight Ga points,
torus conjugation scales each parameter by that character's value and keeps
the order. -/
theorem BorelRootVectorGa.list_product_torus_conjugate
    (J : HopfIdeal K B) (π : B →ₐc[K] MonoidAlgebra K M)
    (hπ : Function.Surjective π)
    (t : WithConv (MonoidAlgebra K M →ₐ[K] K))
    (l : List (borelRootVectorIndex J π × K)) :
    AlgHom.mapDomain π t *
      (l.map (fun rt => gaAffineGroupPoints (borelRootVectorGa J π hπ rt.1)
        (Multiplicative.ofAdd rt.2))).prod * (AlgHom.mapDomain π t)⁻¹ =
      (l.map (fun rt => gaAffineGroupPoints (borelRootVectorGa J π hπ rt.1)
        (Multiplicative.ofAdd
          (t.ofConv (MonoidAlgebra.single rt.1.1 1) * rt.2)))).prod := by
  induction l with
  | nil => simp
  | cons rt l ih =>
      simp only [List.map_cons, List.prod_cons]
      have hconj : AlgHom.mapDomain π t *
          gaAffineGroupPoints (borelRootVectorGa J π hπ rt.1)
            (Multiplicative.ofAdd rt.2) * (AlgHom.mapDomain π t)⁻¹ =
          gaAffineGroupPoints (borelRootVectorGa J π hπ rt.1)
            (Multiplicative.ofAdd
              (t.ofConv (MonoidAlgebra.single rt.1.1 1) * rt.2)) := by
        apply GaAffineGroupPoints.conjugate_of_character_weight π rt.1.1 t
        rw [borelRootVectorGa_tangent]
        exact rt.1.2.property.2.1
      calc
        AlgHom.mapDomain π t *
            (gaAffineGroupPoints (borelRootVectorGa J π hπ rt.1)
              (Multiplicative.ofAdd rt.2) *
              (l.map (fun rt => gaAffineGroupPoints (borelRootVectorGa J π hπ rt.1)
                (Multiplicative.ofAdd rt.2))).prod) * (AlgHom.mapDomain π t)⁻¹ =
          (AlgHom.mapDomain π t *
            gaAffineGroupPoints (borelRootVectorGa J π hπ rt.1)
              (Multiplicative.ofAdd rt.2) * (AlgHom.mapDomain π t)⁻¹) *
          (AlgHom.mapDomain π t *
            (l.map (fun rt => gaAffineGroupPoints (borelRootVectorGa J π hπ rt.1)
              (Multiplicative.ofAdd rt.2))).prod * (AlgHom.mapDomain π t)⁻¹) := by
                group
        _ = _ := by rw [hconj, ih]

end ReductiveGroups
