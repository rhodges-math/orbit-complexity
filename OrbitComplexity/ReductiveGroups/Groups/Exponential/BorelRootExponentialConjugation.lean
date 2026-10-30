import OrbitComplexity.ReductiveGroups.Groups.Exponential.BorelRootExponentialBijection
import OrbitComplexity.ReductiveGroups.Groups.Additive.GaAffineGroupConjugation

/-!
# Borel Root Exponential Conjugation

Conjugation of points in the Borel Ga-only subgroup follows from
the adjoint action on their tangent vectors. -/

noncomputable section
namespace ReductiveGroups

open TauCeti

universe u
variable {K B ι : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  [CommRing B] [HopfAlgebra K B] [Algebra.FiniteType K B]

local notation "M" => Multiplicative (ι →₀ ℤ)

/-- Conjugation is equivariant for the exponential of the Borel's
Ga-only subgroup whenever the original adjoint sends one subgroup tangent
to another.  -/
theorem BorelRootUnipotentExponential.conjugate_of_ad_eq
    (J : HopfIdeal K B) (hJ : HopfIdeal.IsBorel K (CommHopfAlgCat.of K B) J)
    (π : B →ₐc[K] MonoidAlgebra K M) (hπ : Function.Surjective π)
    (g : WithConv (B →ₐ[K] K))
    (d e : (derivationCompLieHom (B := K)
      (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B)
        (borelRootUnipotentHopfIdeal J π hπ)).hom).range)
    (hAd : affineGroupAdjointRepresentation g d.val = e.val) :
    g * borelRootUnipotentExponential J hJ π hπ d * g⁻¹ =
      borelRootUnipotentExponential J hJ π hπ e := by
  have h := GaAffineGroupPoints.conjugate_of_tangent_eq
    (borelRootUnipotentGa J hJ π hπ d.val d.property)
    (borelRootUnipotentGa J hJ π hπ e.val e.property) g 1
    (by simpa only [borelRootUnipotentGa_tangent, one_smul] using hAd) 1
  simpa only [borelRootUnipotentExponential, one_mul] using h

/-- Ad-stability of the subgroup tangent gives pointwise normalization
of the subgroup, using its proved exponential bijection. -/
theorem BorelRootUnipotentExponential.conjugate_of_ad_mem
    (J : HopfIdeal K B) (hJ : HopfIdeal.IsBorel K (CommHopfAlgCat.of K B) J)
    (π : B →ₐc[K] MonoidAlgebra K M) (hπ : Function.Surjective π)
    (g : WithConv (B →ₐ[K] K))
    (hAd : ∀ d : (derivationCompLieHom (B := K)
      (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B)
        (borelRootUnipotentHopfIdeal J π hπ)).hom).range,
      affineGroupAdjointRepresentation g d.val ∈
        (derivationCompLieHom (B := K)
          (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B)
            (borelRootUnipotentHopfIdeal J π hπ)).hom).range)
    (d : (derivationCompLieHom (B := K)
      (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B)
        (borelRootUnipotentHopfIdeal J π hπ)).hom).range) :
    g * borelRootUnipotentExponential J hJ π hπ d * g⁻¹ =
      borelRootUnipotentExponential J hJ π hπ
        ⟨affineGroupAdjointRepresentation g d.val, hAd d⟩ :=
  BorelRootUnipotentExponential.conjugate_of_ad_eq J hJ π hπ g d
    ⟨affineGroupAdjointRepresentation g d.val, hAd d⟩ rfl

/-- The inverse of the tangent-to-point equivalence intertwines
conjugation and the original adjoint action, provided this point preserves
the subgroup tangent. The required membership of the conjugated point is
proved from the equivariance equation itself. -/
theorem BorelRootUnipotentExponentialEquiv.symm_conjugate
    (J : HopfIdeal K B) (hJ : HopfIdeal.IsBorel K (CommHopfAlgCat.of K B) J)
    (π : B →ₐc[K] MonoidAlgebra K M) (hπ : Function.Surjective π)
    (g : WithConv (B →ₐ[K] K))
    (hAd : ∀ d : (derivationCompLieHom (B := K)
      (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B)
        (borelRootUnipotentHopfIdeal J π hπ)).hom).range,
      affineGroupAdjointRepresentation g d.val ∈
        (derivationCompLieHom (B := K)
          (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B)
            (borelRootUnipotentHopfIdeal J π hπ)).hom).range)
    (u : CommHopfAlgCat.quotientPointsSubgroup (CommHopfAlgCat.of K B)
      (borelRootUnipotentHopfIdeal J π hπ) (CommAlgCat.of K K)) :
    ∃ hu : g * u.val * g⁻¹ ∈
        CommHopfAlgCat.quotientPointsSubgroup (CommHopfAlgCat.of K B)
          (borelRootUnipotentHopfIdeal J π hπ) (CommAlgCat.of K K),
      (borelRootUnipotentExponentialEquiv J hJ π hπ).symm
        ⟨g * u.val * g⁻¹, hu⟩ =
        ⟨affineGroupAdjointRepresentation g
          ((borelRootUnipotentExponentialEquiv J hJ π hπ).symm u).val,
          hAd ((borelRootUnipotentExponentialEquiv J hJ π hπ).symm u)⟩ := by
  let d := (borelRootUnipotentExponentialEquiv J hJ π hπ).symm u
  let e : (derivationCompLieHom (B := K)
      (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B)
        (borelRootUnipotentHopfIdeal J π hπ)).hom).range :=
    ⟨affineGroupAdjointRepresentation g d.val, hAd d⟩
  have huval : u.val = borelRootUnipotentExponential J hJ π hπ d := by
    have h := (borelRootUnipotentExponentialEquiv J hJ π hπ).apply_symm_apply u
    exact congrArg Subtype.val h.symm
  have hconj : g * u.val * g⁻¹ = borelRootUnipotentExponential J hJ π hπ e := by
    rw [huval]
    exact BorelRootUnipotentExponential.conjugate_of_ad_mem J hJ π hπ g hAd d
  have hmem : g * u.val * g⁻¹ ∈
      CommHopfAlgCat.quotientPointsSubgroup (CommHopfAlgCat.of K B)
        (borelRootUnipotentHopfIdeal J π hπ) (CommAlgCat.of K K) :=
    hconj ▸ borelRootUnipotentExponential_mem J hJ π hπ e
  refine ⟨hmem, ?_⟩
  have he : (borelRootUnipotentExponentialEquiv J hJ π hπ).symm
      ⟨g * u.val * g⁻¹, hmem⟩ = e := by
    apply (borelRootUnipotentExponentialEquiv J hJ π hπ).injective
    apply Subtype.ext
    rw [Equiv.apply_symm_apply]
    change g * u.val * g⁻¹ = borelRootUnipotentExponential J hJ π hπ e
    exact hconj
  exact he

end ReductiveGroups
