import OrbitComplexity.ReductiveGroups.Groups.RootCoordinates.BorelRootFamilyIndependence
import OrbitComplexity.ReductiveGroups.Groups.RootCoordinates.BorelRootSupportDrop
import OrbitComplexity.ReductiveGroups.Groups.RootCoordinates.BorelRootSubsetTorus
import OrbitComplexity.ReductiveGroups.Roots.Parabolic.LeviRootSpan
import OrbitComplexity.ReductiveGroups.Roots.Inversions.PositiveRootClosedSets

/-!
# Levi Borel Unipotent

The standard Levi subgroup and its unipotent Borel part.

For a set `I` of simple roots of the Borel base, `Z_I = ∩_{α ∈ I} ker α` is the
center of the standard Levi subgroup `L_I`, and `L_I = C_G(Z_I)`. We use this
as the definition of `L_I` on K-points. The points of the original Ga-only
Borel subgroup `U` centralizing `Z_I` are exactly `U_{Φ_I^+}`. -/

noncomputable section
namespace ReductiveGroups

open TauCeti LieAlgebra LieAlgebra.IsKilling LieModule

universe u
variable {K B ι : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  [CommRing B] [HopfAlgebra K B] [Algebra.FiniteType K B] [Finite ι]

local notation "M" => Multiplicative (ι →₀ ℤ)

private abbrev rootTangentSpace (J : HopfIdeal K B)
    (π : B →ₐc[K] MonoidAlgebra K M)
    (hπ : Function.Surjective π) := (derivationCompLieHom (B := K)
  (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B)
    (borelRootUnipotentHopfIdeal J π hπ)).hom).range

section Defs

variable (I J : HopfIdeal K B) (hJI : J ≤ I)
  (hI : HopfIdeal.IsMaximalTorus K (CommHopfAlgCat.of K B) I)
  (hJ : HopfIdeal.IsBorel K (CommHopfAlgCat.of K B) J)
  (π : B →ₐc[K] MonoidAlgebra K (Multiplicative (ι →₀ ℤ))) (hπ : Function.Surjective π)
  (hker : ∀ a : B, π a = 0 ↔ a ∈ I.toIdeal)
  (hB : reductiveCommHopfAlgProperty K (FiniteTypeCommHopfAlgCat.of K B))

/-- The character of a root of the root system. -/
def rootCharacter :
    letI := finiteTypeAffineGroup_tangent_finite (K := K) (B := B)
    letI := MaximalTorusLieCartan.maximalTorus_coordinateTangent_isCartan I hI π hπ hker hB
    letI := ReductiveTorusRootSystem.coordinateCenterQuotient_isCartan I hI π hπ hker hB
    (centerQuotientCartan (diagonalizableTangentImage π)).root → M :=
  fun γ => ((ReductiveCharacterRoots.characterCenterQuotientRootEquiv I hI π hπ hker hB).symm γ).val

/-- The K-points of `Z_I = ∩_{α ∈ I} ker α`, for a set `I` of simple roots of
the Borel base. -/
def leviCenterPoints
    (Isimple : Set (borelRootBase I J hJI hI hJ π hπ hker hB).support) :
    Set (WithConv (B →ₐ[K] K)) :=
  {g | ∃ t : WithConv (MonoidAlgebra K M →ₐ[K] K), g = AlgHom.mapDomain π t ∧
    ∀ j ∈ Isimple, t.ofConv (MonoidAlgebra.single
      (rootCharacter I hI π hπ hker hB j.val) 1) = 1}

/-- The standard Levi subgroup `L_I = C_G(Z_I)` on K-points. -/
def leviSubgroupPoints
    (Isimple : Set (borelRootBase I J hJI hI hJ π hπ hker hB).support) :
    Subgroup (WithConv (B →ₐ[K] K)) :=
  Subgroup.centralizer (leviCenterPoints I J hJI hI hJ π hπ hker hB Isimple)

/-- The Levi–Borel subgroup `B_{L_I} = L_I ∩ B` on K-points. -/
def leviBorelPoints
    (Isimple : Set (borelRootBase I J hJI hI hJ π hπ hker hB).support) :
    Subgroup (WithConv (B →ₐ[K] K)) :=
  leviSubgroupPoints I J hJI hI hJ π hπ hker hB Isimple ⊓
    CommHopfAlgCat.quotientPointsSubgroup (CommHopfAlgCat.of K B) J (CommAlgCat.of K K)

/-- The Borel root characters whose roots lie in `Φ_I^+`. -/
def leviBorelRootSet
    (Isimple : Set (borelRootBase I J hJI hI hJ π hπ hker hB).support) :
    Set (borelRootCharacterIndex J π) :=
  {k | ReductiveCharacterRoots.characterCenterQuotientRootEquiv I hI π hπ hker hB
      (borelRootCharacterOccurring J π k) ∈
    leviPositiveRoots (borelRootBase I J hJI hI hJ π hπ hker hB) Isimple}

end Defs

end ReductiveGroups
