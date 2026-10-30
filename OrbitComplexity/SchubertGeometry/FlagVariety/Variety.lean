import OrbitComplexity.SchubertGeometry.FlagVariety.Quotient
import OrbitComplexity.GroupActions.Varieties.ClosedPoints

/-! # The flag variety

The surjective quotient from the reductive group makes the separated flag scheme finite type.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology

namespace SchubertGeometry
noncomputable section
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroups.ReductiveGroupData K)

private theorem quotientSection_range (p : flagSchemePoints G) :
    p.val (IsLocalRing.closedPoint K) ∈ Set.range (flagQuotient G) := by
  obtain ⟨a, ha⟩ := (flagSchemePointsEquiv G).surjective p
  rw [← ha]
  refine Quotient.inductionOn a (fun g => ?_)
  refine ⟨(GroupActions.reductiveVariety G).pointMap
    (GroupActions.reductivePointsEquiv G g), ?_⟩
  exact congrArg (fun f : Spec (CommRingCat.of K) ⟶ flagScheme G =>
    f (IsLocalRing.closedPoint K)) (flagQuotient_points G g)

/-- The quotient morphism is surjective on the underlying scheme points. -/
instance flagQuotient_surjective : Surjective (flagQuotient G) := by
  have : IsLocallyNoetherian (flagScheme G) :=
    LocallyOfFiniteType.isLocallyNoetherian (flagSchemeToSpec G)
  have : QuasiSeparatedSpace (flagScheme G) :=
    quasiSeparatedSpace_of_quasiSeparated (flagSchemeToSpec G)
  have : JacobsonSpace (flagScheme G) :=
    LocallyOfFiniteType.jacobsonSpace (flagSchemeToSpec G)
  have : LocallyOfFiniteType (flagQuotient G ≫ flagSchemeToSpec G) :=
    (flagQuotient_toSpec G).symm ▸ (GroupActions.reductiveVariety G).locallyOfFiniteType
  have : LocallyOfFiniteType (flagQuotient G) :=
    locallyOfFiniteType_of_comp (flagQuotient G) (flagSchemeToSpec G)
  have hlocal : IsLocallyConstructible (Set.range (flagQuotient G)) := by
    simpa only [Set.image_univ] using (flagQuotient G).isLocallyConstructible_image
      IsLocallyConstructible.univ
  have hconstruct : IsConstructible (Set.range (flagQuotient G)) :=
    hlocal.isConstructible_of_subset_of_isCompact Set.Subset.rfl
      (isCompact_range (flagQuotient G).continuous)
  have he : Set.range (flagQuotient G) = Set.univ := by
    apply GroupActions.constructible_eq hconstruct IsConstructible.univ
    apply Set.Subset.antisymm
    · exact Set.inter_subset_inter_left _ (Set.subset_univ _)
    · intro x hx
      let p := (pointEquivClosedPoint (flagSchemeToSpec G)).symm ⟨x, hx.2⟩
      have hp : p.val (IsLocalRing.closedPoint K) = x :=
        congrArg Subtype.val ((pointEquivClosedPoint (flagSchemeToSpec G)).apply_symm_apply
          ⟨x, hx.2⟩)
      exact ⟨hp ▸ quotientSection_range G p, hx.2⟩
  exact ⟨Set.range_eq_univ.mp he⟩

private theorem flagSchemeCompact : CompactSpace (flagScheme G) :=
  Function.Surjective.compactSpace (flagQuotient G).continuous (flagQuotient G).surjective

/-- The flag scheme is Noetherian over the base field. -/
instance flagScheme_noetherian : IsNoetherian (flagScheme G) where
  toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian (flagSchemeToSpec G)
  toCompactSpace := flagSchemeCompact G

/-- The flag variety is the reduced separated finite-type flag scheme. -/
def flagVariety : GroupActions.Variety K where
  scheme := flagScheme G
  toSpec := flagSchemeToSpec G

/-- The quotient is a variety morphism over the base field. -/
def flagQuotientMorphism :
    (GroupActions.reductiveVariety G).toOver ⟶ (flagVariety G).toOver :=
  Over.homMk (flagQuotient G) (flagQuotient_toSpec G)

/-- The flag variety is integral as a surjective image of the reductive variety. -/
instance flagVarietyIntegral : IsIntegral (flagVariety G).scheme := by
  change IsIntegral (flagScheme G)
  have : IrreducibleSpace (flagScheme G) :=
    Function.Surjective.irreducibleSpace (flagQuotient G).continuous
      (flagQuotient G).surjective
  exact isIntegral_of_irreducibleSpace_of_isReduced _
/-- Borel cosets identify with rational points of the flag variety. -/
def flagVarietyPointsEquiv : flagPoints G ≃ (flagVariety G).points :=
  flagSchemePointsEquiv G

/-- On rational points the variety quotient is the Borel-coset projection. -/
theorem flagQuotientMorphism_points (g : G.points) :
    GroupActions.Variety.mapPoints (flagQuotientMorphism G)
      (GroupActions.reductivePointsEquiv G g) =
      flagVarietyPointsEquiv G (flagProjection G g) := by
  apply Subtype.ext
  exact flagQuotient_points G g

end
end SchubertGeometry