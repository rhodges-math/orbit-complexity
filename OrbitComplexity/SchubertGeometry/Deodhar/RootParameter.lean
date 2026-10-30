import OrbitComplexity.GroupActions.Varieties.RootLine
import OrbitComplexity.SchubertGeometry.Deodhar.CellProjection
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupSimpleRoots
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupRootTangent
import OrbitComplexity.ReductiveGroups.Groups.GaCoordinates.GaConjugateTangent

/-! # A fixed additive parameter on the added root

Conjugating the chosen simple-root map by a Weyl representative gives a nonzero additive
parameter on the new root line of an increasing cell extension.
-/

open CategoryTheory AlgebraicGeometry ReductiveGroups TauCeti
namespace SchubertGeometry
noncomputable section
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K) (w : G.weylGroup) (i : G.rootBase.support)
  (hw : G.rootBase.IsPos (G.rootSystem.weylGroupToPerm w i))

/-- Conjugate the chosen positive simple-root parameter by its preceding Weyl representative. -/
def rankOneGaMap : G.coordinateAlgebra →ₐc[K] SymmetricAlgebra K K :=
  (G.simpleRootMap i).comp (affineGroupConjugationBialgHom (G.weylPoint w))

private theorem rankOneGa_ne_zero : gaAffineGroupTangent (rankOneGaMap G w i) ≠ 0 := by
  intro hz
  rw [rankOneGaMap, gaTangent_comp_conjugation] at hz
  apply G.simpleRootMap_tangent_ne_zero i
  apply (affineGroupAdjointLieEquiv (G.weylPoint w)).injective
  change affineGroupAdjointRepresentation (G.weylPoint w)
    (gaAffineGroupTangent (G.simpleRootMap i)) =
      affineGroupAdjointRepresentation (G.weylPoint w) 0
  rw [map_zero]
  exact hz

private theorem rankOneGa_mem : gaAffineGroupTangent (rankOneGaMap G w i) ∈
    G.rootWeightSpace (G.rootSystem.weylGroupToPerm w i) := by
  rw [rankOneGaMap, gaTangent_comp_conjugation]
  have hm : affineGroupAdjointLieEquiv (G.weylPoint w)
      (gaAffineGroupTangent (G.simpleRootMap i)) ∈ (G.rootWeightSpace i.val).map
        (affineGroupAdjointLieEquiv (G.weylPoint w)).toLinearEquiv.toLinearMap :=
    Submodule.mem_map.mpr ⟨_, G.simpleRootMap_tangent_mem i, rfl⟩
  rwa [G.weylPoint_rootWeightSpace] at hm

private theorem rankOneGa_kills : ∀ b ∈ G.rootSubsetIdeal (rankOneRootSet G w i)
    (rankOneRoot_closed G w i hw), gaAffineGroupTangent (rankOneGaMap G w i) b = 0 := by
  apply (tangent_mem_hopfQuotient_iff _ _).mp
  change gaAffineGroupTangent (rankOneGaMap G w i) ∈
    (hopfTangentImage (G.rootSubsetIdeal (rankOneRootSet G w i)
      (rankOneRoot_closed G w i hw))).toSubmodule
  rw [G.singletonRootTangent _ hw]
  exact rankOneGa_mem G w i

/-- The chosen conjugated root parameter identifies the added coordinate algebra with Ga. -/
def rankOneGaCoordinates :
    G.rootSubsetAlgebra (rankOneRootSet G w i) (rankOneRoot_closed G w i hw) ≃ₐ[K]
      SymmetricAlgebra K K :=
  GroupActions.rootLineCoordinateEquiv G _ hw (rankOneRoot_closed G w i hw)
    (rankOneGaMap G w i) (rankOneGa_kills G w i hw) (rankOneGa_ne_zero G w i)

/-- The fixed additive parameter is an isomorphism onto the added root subgroup. -/
def rankOneGaIso : (GroupActions.additiveVariety K).toOver ≅
    (GroupActions.rootSubsetVariety G (rankOneRootSet G w i)
      (rankOneRoot_closed G w i hw)).toOver :=
  GroupActions.rootLineIso G _ hw (rankOneRoot_closed G w i hw) (rankOneGaMap G w i)
    (rankOneGa_kills G w i hw) (rankOneGa_ne_zero G w i)

/-- The added root-line isomorphism sends t to the conjugated chosen simple-root point. -/
theorem rankOneGaIso_points (t : K) :
    (GroupActions.rootSubsetPointsMulEquiv G _ (rankOneRoot_closed G w i hw)
      (GroupActions.Variety.mapPoints (rankOneGaIso G w i hw).hom
        (GroupActions.additivePointsEquiv K t)) : G.points) =
      G.weylPoint w * gaParameterPoint (G.simpleRootMap i) t * (G.weylPoint w)⁻¹ := by
  rw [rankOneGaIso, GroupActions.rootLineIso_points]
  exact gaPoints_comp_conjugation (G.simpleRootMap i) (G.weylPoint w)
    (Multiplicative.ofAdd t)

end
end SchubertGeometry
