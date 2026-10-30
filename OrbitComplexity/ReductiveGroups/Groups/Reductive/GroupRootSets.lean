import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupRootCount
import OrbitComplexity.ReductiveGroups.Roots.Inversions.ClosedRootTransport
import OrbitComplexity.ReductiveGroups.Roots.Parabolic.LeviRootClosed

/-!
# Closed character supports from reductive root sets

Inversion roots, positive Weyl-translated inversion roots, and parabolic complements
give integrally closed sets of Borel root characters.
-/

noncomputable section
namespace ReductiveGroups.ReductiveGroupData
open TauCeti
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

/-- Borel characters whose corresponding roots belong to a prescribed root set. -/
def rootCharacters (R : Set G.rootIndex) :
    Set (borelRootCharacterIndex G.borelIdeal G.torusSplit) :=
  {i | G.characterRootEquiv (borelRootCharacterOccurring G.borelIdeal G.torusSplit i) ∈ R}

/-- Integral closedness of positive roots implies integral closedness of their characters. -/
theorem rootCharacters_closed (R : Set G.rootIndex) (hR : IsPositiveRootClosed G.rootBase R) :
    IsBorelRootCharacterClosed G.borelIdeal G.torusSplit (G.rootCharacters R) :=
  IsBorelRootCharacterClosed.of_isPositiveRootClosed G.torusIdeal G.borelIdeal
    G.borel_le_torus G.isMaximalTorus G.isBorel G.torusSplit G.split_surjective
    G.split_eq_zero G.reductive R hR

/-- The Borel root characters corresponding to the left inversions of a Weyl element. -/
def inversionCharacters (w : G.weylGroup) :
    Set (borelRootCharacterIndex G.borelIdeal G.torusSplit) :=
  G.rootCharacters (leftRootInversionIndices G.rootBase w)

/-- Inversion characters form an integrally closed root set. -/
theorem inversionCharacters_closed (w : G.weylGroup) :
    IsBorelRootCharacterClosed G.borelIdeal G.torusSplit (G.inversionCharacters w) :=
  G.rootCharacters_closed _ (LeftRootInversionIndices.isPositiveRootClosed G.rootBase w)

end ReductiveGroups.ReductiveGroupData
