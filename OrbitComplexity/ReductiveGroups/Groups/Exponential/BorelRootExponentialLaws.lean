import OrbitComplexity.ReductiveGroups.Groups.Unipotent.BorelRootUnipotentExponential
import OrbitComplexity.ReductiveGroups.Groups.GaCoordinates.GaUnitPointDeterminesMorphism
import OrbitComplexity.ReductiveGroups.Groups.Additive.GaAffineGroupCommutation

/-!
# Borel Root Exponential Laws

Injectivity and commutation of the exponential points in the
Borel's Ga-only subgroup. -/

noncomputable section
namespace ReductiveGroups

open TauCeti

universe u
variable {K B ι : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  [CommRing B] [HopfAlgebra K B] [Algebra.FiniteType K B]

local notation "M" => Multiplicative (ι →₀ ℤ)

/-- Distinct tangent vectors give distinct original group points. -/
theorem borelRootUnipotentExponential_injective
    (J : HopfIdeal K B) (hJ : HopfIdeal.IsBorel K (CommHopfAlgCat.of K B) J)
    (π : B →ₐc[K] MonoidAlgebra K M) (hπ : Function.Surjective π) :
    Function.Injective (borelRootUnipotentExponential J hJ π hπ) := by
  intro d e h
  apply Subtype.ext
  have ht := gaAffineGroupTangent_eq_of_points_one_eq
    (borelRootUnipotentGa J hJ π hπ d.val d.property)
    (borelRootUnipotentGa J hJ π hπ e.val e.property) h
  simpa only [borelRootUnipotentGa_tangent] using ht

/-- Commuting original tangent vectors give commuting original exponential
points. -/
theorem borelRootUnipotentExponential_commute
    (J : HopfIdeal K B) (hJ : HopfIdeal.IsBorel K (CommHopfAlgCat.of K B) J)
    (π : B →ₐc[K] MonoidAlgebra K M) (hπ : Function.Surjective π)
    (d e : (derivationCompLieHom (B := K)
      (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B)
        (borelRootUnipotentHopfIdeal J π hπ)).hom).range)
    (hde : ⁅d, e⁆ = 0) :
    Commute (borelRootUnipotentExponential J hJ π hπ d)
      (borelRootUnipotentExponential J hJ π hπ e) := by
  apply GaAffineGroupPoints.commute_of_tangent_bracket_zero
  rw [borelRootUnipotentGa_tangent, borelRootUnipotentGa_tangent]
  exact congrArg Subtype.val hde

end ReductiveGroups
