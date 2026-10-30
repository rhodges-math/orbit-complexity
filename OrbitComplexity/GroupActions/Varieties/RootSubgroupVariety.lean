import OrbitComplexity.GroupActions.Varieties.ReductiveIntegral
import OrbitComplexity.GroupActions.Varieties.AffineDimension
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupRootCoordinates
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Varieties of closed root subgroups

Closed positive-root supports define affine group varieties with polynomial coordinates.
-/

open CategoryTheory AlgebraicGeometry

namespace GroupActions
noncomputable section
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroups.ReductiveGroupData K)
  (R : Set G.rootIndex) (hR : ReductiveGroups.IsPositiveRootClosed G.rootBase R)

/-- The affine group variety supported on an integrally closed positive-root subset. -/
def rootSubsetVariety : Variety K := affineVariety K (G.rootSubsetAlgebra R hR)

/-- A closed root subgroup is an integral variety. -/
instance rootSubsetVarietyIntegral : IsIntegral (rootSubsetVariety G R hR).scheme := by
  change IsIntegral (Spec (CommRingCat.of (G.rootSubsetAlgebra R hR)))
  infer_instance

/-- The root-subgroup Hopf algebra defines a group object. -/
instance rootSubsetVarietyGroup : GrpObj (rootSubsetVariety G R hR).toOver := by
  change GrpObj ((Spec (CommRingCat.of (G.rootSubsetAlgebra R hR))).asOver
    (Spec (CommRingCat.of K)))
  infer_instance

/-- The closed root subgroup includes into the reductive group by its coordinate quotient. -/
def rootSubsetInclusion : (rootSubsetVariety G R hR).toOver ⟶ (reductiveVariety G).toOver :=
  ((hopfSpec (CommRingCat.of K)).map
    (TauCeti.CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K G.coordinateAlgebra)
      (G.rootSubsetIdeal R hR)).op).hom.hom

/-- The root-subgroup inclusion is the spectrum map of its coordinate quotient. -/
theorem rootSubsetInclusion_left :
    (rootSubsetInclusion G R hR).left =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (G.rootSubsetIdeal R hR).toIdeal)) := rfl

/-- The root-subgroup inclusion is a closed immersion. -/
instance rootSubsetInclusion_isClosed :
    IsClosedImmersion (rootSubsetInclusion G R hR).left := by
  rw [rootSubsetInclusion_left]
  exact IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

/-- The root-subgroup inclusion preserves multiplication. -/
instance rootSubsetInclusion_isMonHom : IsMonHom (rootSubsetInclusion G R hR) := by
  change IsMonHom (((hopfSpec (CommRingCat.of K)).map
    (TauCeti.CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K G.coordinateAlgebra)
      (G.rootSubsetIdeal R hR)).op).hom.hom)
  infer_instance

/-- Ordered root coordinates identify a closed root subgroup with affine space. -/
def rootSubsetChart :
    (affineSpaceVariety K {r : G.rootIndex // G.rootBase.IsPos r ∧ r ∈ R}).toOver ≅
      (rootSubsetVariety G R hR).toOver :=
  (algSpec (CommRingCat.of K)).mapIso (CommAlgCat.isoMk (G.rootSubsetCoordinateEquiv R hR)).op

/-- A root subgroup has dimension the number of positive roots in its support. -/
theorem rootSubsetVariety_dim :
    (rootSubsetVariety G R hR).dim =
      Nat.card {r : G.rootIndex // G.rootBase.IsPos r ∧ r ∈ R} := by
  rw [← Variety.dim_eq_of_iso _ (rootSubsetChart G R hR), dim_affineSpaceVariety]

end
end GroupActions
