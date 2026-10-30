import OrbitComplexity.GroupActions.Varieties.RootSubgroupPoints
import OrbitComplexity.GroupActions.Varieties.AffineMorphisms
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupRootCoordinatePoints

/-! # Ordered products on closed root subgroups

Every ordering of a closed positive-root support gives polynomial coordinates.
The associated chart multiplies its specified additive root parameters.
-/

open CategoryTheory AlgebraicGeometry ReductiveGroups TauCeti
noncomputable section
namespace GroupActions
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K) (R : Set G.rootIndex)
  (hR : IsPositiveRootClosed G.rootBase R)
  (l : List (G.rootCharacters R)) (hl : l.Nodup) (hall : ∀ i, i ∈ l)

private instance : Finite (borelRootCharacterIndex G.borelIdeal G.torusSplit) :=
  finite_borelRootCharacterIndex G.borelIdeal G.torusSplit G.split_surjective

private def orderedCoordinates :
    G.rootSubsetAlgebra R hR ≃ₐ[K] MvPolynomial (G.rootCharacters R) K :=
  BorelRootSubset.coordinateEquiv G.torusIdeal G.borelIdeal G.borel_le_torus
    G.isMaximalTorus G.isBorel G.torusSplit G.split_surjective G.split_eq_zero G.reductive
    G.borelRootMaps G.borelRootBasis G.borelRootBasis_tangent G.borelRootMaps_weight
    (G.rootCharacters R) (G.rootCharacters_closed R hR) l hl hall

/-- Every ordering of the root support gives an affine-space chart of its subgroup. -/
def rootSubsetProductChart :
    (affineSpaceVariety K (G.rootCharacters R)).toOver ≅
      (rootSubsetVariety G R hR).toOver :=
  (algSpec (CommRingCat.of K)).mapIso
    (CommAlgCat.isoMk (orderedCoordinates G R hR l hl hall)).op

/-- The ordered root chart evaluates to the product of its specified additive parameters. -/
theorem rootSubsetProductChart_points (a : G.rootCharacters R → K) :
    (rootSubsetPointsMulEquiv G R hR
      (Variety.mapPoints (rootSubsetProductChart G R hR l hl hall).hom
        ((affineSpaceVarietyPointsEquiv K _).symm a)) : G.points) =
      (l.map (fun i => gaParameterPoint (G.borelRootMaps i.val) (a i))).prod := by
  let e : (affineVariety K (G.rootSubsetAlgebra R hR)).points ≃*
      G.rootSubsetPoints R hR := rootSubsetPointsMulEquiv G R hR
  change (e
    (Variety.mapPoints (affineMorphism (orderedCoordinates G R hR l hl hall).toAlgHom)
      ((affineVarietyPointsEquiv K _).symm (MvPolynomial.aeval a))) : G.points) = _
  rw [affineMorphism_points]
  apply WithConv.ofConv_injective
  change ((affinePointsEquiv.symm (affinePointsEquiv
    ((MvPolynomial.aeval a).comp (orderedCoordinates G R hR l hl hall).toAlgHom))).comp
      (Ideal.Quotient.mkₐ K (G.rootSubsetIdeal R hR).toIdeal)) = _
  rw [Equiv.symm_apply_apply]
  apply AlgHom.ext
  intro b
  exact DFunLike.congr_fun
    (gaProductCoordinate_eval (fun i : G.rootCharacters R => G.borelRootMaps i.val) l a) b

include hl hall in
/-- In any order, root parameters multiply uniquely to each point of the closed subgroup. -/
theorem rootSubset_ordered_product :
    (∀ a : G.rootCharacters R → K,
      (l.map (fun i => gaParameterPoint (G.borelRootMaps i.val) (a i))).prod ∈
        G.rootSubsetPoints R hR) ∧
    ∀ g : G.points, g ∈ G.rootSubsetPoints R hR →
      ∃! a : G.rootCharacters R → K,
        (l.map (fun i => gaParameterPoint (G.borelRootMaps i.val) (a i))).prod = g := by
  let e : (G.rootCharacters R → K) ≃ G.rootSubsetPoints R hR :=
    (affineSpaceVarietyPointsEquiv K _).symm.trans
      ((Variety.pointsHomeomorph (rootSubsetProductChart G R hR l hl hall)).toEquiv.trans
        (rootSubsetPointsMulEquiv G R hR).toEquiv)
  have he (a : G.rootCharacters R → K) :
      (e a : G.points) =
        (l.map (fun i => gaParameterPoint (G.borelRootMaps i.val) (a i))).prod :=
    rootSubsetProductChart_points G R hR l hl hall a
  refine ⟨fun a => he a ▸ (e a).property, ?_⟩
  intro g hg
  obtain ⟨a, ha⟩ := e.surjective ⟨g, hg⟩
  refine ⟨a, (he a).symm.trans (congrArg Subtype.val ha), ?_⟩
  intro b hb
  apply e.injective
  apply Subtype.ext
  exact (he b).trans (hb.trans (congrArg Subtype.val ha).symm)

end GroupActions
