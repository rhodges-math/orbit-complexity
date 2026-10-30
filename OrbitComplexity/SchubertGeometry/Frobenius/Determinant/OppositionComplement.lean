import OrbitComplexity.SchubertGeometry.Frobenius.Determinant.OppositionParameters
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupRootTransport
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-!
# The complementary roots in an opposition chart

Inverse simple conjugation preserves the positive noninversion roots.
Following it by longest-Weyl conjugation puts the corresponding subgroup
inside the opposite unipotent group.
-/

open ReductiveGroups TauCeti

namespace SchubertGeometry.DeterminantSection

open private ReductiveGroups.ReductiveGroupData.inverseReflection_transport from
  OrbitComplexity.ReductiveGroups.Groups.Representatives.RootParameters

private theorem conjugate_product {M : Type*} [Group M] (w r u : M) :
    (w * r) * u * (w * r)⁻¹ = w * (r * u * r⁻¹) * w⁻¹ := by group

private theorem simple_noninversion_positive {ι R M N : Type*}
    [CommRing R] [CharZero R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] {P : RootPairing ι R M N}
    [Finite ι] [IsDomain R] [P.IsCrystallographic] [P.IsReduced]
    (b : P.Base) (i : b.support) (r : ι)
    (hr : b.IsPos r ∧ r ∉ leftRootInversionIndices b (RootPairing.weylGroup.ofIdx P i)) :
    b.IsPos (P.reflectionPerm i.val r) := by
  have hne : r ≠ i.val := by
    intro h
    apply hr.2
    rw [leftRootInversionIndices_simple]
    exact h
  exact hr.1.reflectionPerm i.property hne

universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
variable (G : ReductiveGroupData K)

private theorem inverse_simple_unipotent (i : G.rootBase.support) (u : G.points)
    (hu : u ∈ G.rootSubsetPoints
      {r | G.rootBase.IsPos r ∧ r ∉ leftRootInversionIndices G.rootBase
        (RootPairing.weylGroup.ofIdx G.rootSystem i)}
      (PositiveRootClosedSets.isPositiveRootClosed G.rootBase
        (RootPairing.weylGroup.ofIdx G.rootSystem i))) :
    (G.reflectionPoint i.val)⁻¹ * u * ((G.reflectionPoint i.val)⁻¹)⁻¹ ∈
      G.unipotentPoints := by
  apply G.rootSubsetPoints_conj_mem (G.reflectionPoint i.val)⁻¹
    {r | G.rootBase.IsPos r ∧ r ∉ leftRootInversionIndices G.rootBase
      (RootPairing.weylGroup.ofIdx G.rootSystem i)}
    (PositiveRootClosedSets.isPositiveRootClosed G.rootBase
      (RootPairing.weylGroup.ofIdx G.rootSystem i)) G.unipotentIdeal ?_ u hu
  intro r hr
  have htr := ReductiveGroups.ReductiveGroupData.inverseReflection_transport G i.val r
  exact (le_of_eq htr).trans
    (G.rootWeightSpace_le_unipotent _ (simple_noninversion_positive G.rootBase i r hr))

/-- The complementary factor of the translated simple chart lies in the opposite
unipotent group and hence does not change a left opposite-unipotent invariant. -/
theorem oppositionComplement_mem (i : G.rootBase.support) (u : G.points)
    (hu : u ∈ G.rootSubsetPoints
      {r | G.rootBase.IsPos r ∧ r ∉ leftRootInversionIndices G.rootBase
        (RootPairing.weylGroup.ofIdx G.rootSystem i)}
      (PositiveRootClosedSets.isPositiveRootClosed G.rootBase
        (RootPairing.weylGroup.ofIdx G.rootSystem i))) :
    oppositionConjugator G i * u * (oppositionConjugator G i)⁻¹ ∈
      G.oppositeUnipotentPoints := by
  have hu' := inverse_simple_unipotent G i u hu
  have h := (G.conj_mem_oppositeUnipotent
    ((G.reflectionPoint i.val)⁻¹ * u * ((G.reflectionPoint i.val)⁻¹)⁻¹)).mpr hu'
  exact (conjugate_product G.longestPoint (G.reflectionPoint i.val)⁻¹ u).symm ▸ h

end SchubertGeometry.DeterminantSection
