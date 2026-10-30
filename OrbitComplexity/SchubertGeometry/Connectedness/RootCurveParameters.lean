import Batteries.Tactic.Lint
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupSl2Points
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupSimpleRoots
import OrbitComplexity.ReductiveGroups.Groups.GaCoordinates.GaConjugateTangent
import OrbitComplexity.ReductiveGroups.Groups.GaCoordinates.GaProductCoordinates
import OrbitComplexity.ReductiveGroups.Roots.SupportGraphs.SupportedRootReflectionWord

/-!
# Conjugated root rank-one coordinate maps

A Weyl conjugate of a chosen simple-root SL₂ morphism gives the rank-one morphism for its
root direction. The upper and lower elementary subgroups are retained as specified coordinate
maps. Every positive root is a Weyl translate of a simple root.
-/

noncomputable section

namespace SchubertGeometry

open ReductiveGroups TauCeti

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K)

/-- The upper root coordinate map obtained by Weyl conjugation of a simple-root map. -/
def rootUpperMap (w : G.weylGroup) (i : G.rootBase.support) :
    G.coordinateAlgebra →ₐc[K] SymmetricAlgebra K K :=
  (G.simpleRootMap i).comp (affineGroupConjugationBialgHom (G.weylPoint w))

/-- The lower root coordinate map paired with the conjugated upper root map. -/
def rootLowerMap (w : G.weylGroup) (i : G.rootBase.support) :
    G.coordinateAlgebra →ₐc[K] SymmetricAlgebra K K :=
  (G.negativeSimpleRootMap i).comp (affineGroupConjugationBialgHom (G.weylPoint w))

/-- The specified coordinate SL₂ morphism conjugated into the chosen root direction. -/
def rootSl2Map (w : G.weylGroup) (i : G.rootBase.support) :
    G.coordinateAlgebra →ₐc[K] SpecialLinear.coordinateHopfAlgebra K 2 :=
  (G.simpleSl2Map i).comp (affineGroupConjugationBialgHom (G.weylPoint w))

/-- Restriction of the conjugated SL₂ map to the upper elementary subgroup. -/
theorem rootSl2Map_upper (w : G.weylGroup) (i : G.rootBase.support) :
    (SpecialLinear.rootSubgroupCoordinateMap (R := K)
        (zero_ne_one : (0 : Fin 2) ≠ 1)).hom.comp (rootSl2Map G w i) =
      rootUpperMap G w i := by
  rw [rootSl2Map, rootUpperMap, ← BialgHom.comp_assoc, G.simpleSl2Map_upper]

/-- Restriction of the conjugated SL₂ map to the lower elementary subgroup. -/
theorem rootSl2Map_lower (w : G.weylGroup) (i : G.rootBase.support) :
    (SpecialLinear.rootSubgroupCoordinateMap (R := K)
        (one_ne_zero : (1 : Fin 2) ≠ 0)).hom.comp (rootSl2Map G w i) =
      rootLowerMap G w i := by
  rw [rootSl2Map, rootLowerMap, ← BialgHom.comp_assoc, G.simpleSl2Map_lower]

/-- Upper root parameters are the specified Weyl conjugates of their simple parameters. -/
theorem rootUpperMap_point (w : G.weylGroup) (i : G.rootBase.support) (t : K) :
    gaParameterPoint (rootUpperMap G w i) t =
      G.weylPoint w * gaParameterPoint (G.simpleRootMap i) t * (G.weylPoint w)⁻¹ :=
  gaPoints_comp_conjugation (G.simpleRootMap i) (G.weylPoint w) (Multiplicative.ofAdd t)

/-- Lower root parameters are the specified Weyl conjugates of their simple parameters. -/
theorem rootLowerMap_point (w : G.weylGroup) (i : G.rootBase.support) (t : K) :
    gaParameterPoint (rootLowerMap G w i) t =
      G.weylPoint w * gaParameterPoint (G.negativeSimpleRootMap i) t *
        (G.weylPoint w)⁻¹ :=
  gaPoints_comp_conjugation (G.negativeSimpleRootMap i) (G.weylPoint w)
    (Multiplicative.ofAdd t)

/-- The conjugated upper tangent lies in its specified Weyl-translated root space. -/
theorem rootUpperMap_tangent (w : G.weylGroup) (i : G.rootBase.support) :
    gaAffineGroupTangent (rootUpperMap G w i) ∈
      G.rootWeightSpace (G.rootSystem.weylGroupToPerm w i.val) := by
  rw [rootUpperMap, gaTangent_comp_conjugation]
  have hm : affineGroupAdjointLieEquiv (G.weylPoint w)
      (gaAffineGroupTangent (G.simpleRootMap i)) ∈ (G.rootWeightSpace i.val).map
        (affineGroupAdjointLieEquiv (G.weylPoint w)).toLinearEquiv.toLinearMap :=
    Submodule.mem_map.mpr ⟨_, G.simpleRootMap_tangent_mem i, rfl⟩
  rwa [G.weylPoint_rootWeightSpace] at hm

/-- The conjugated lower tangent lies in the translated negative simple-root space. -/
theorem rootLowerMap_tangent (w : G.weylGroup) (i : G.rootBase.support) :
    gaAffineGroupTangent (rootLowerMap G w i) ∈
      G.rootWeightSpace (G.rootSystem.weylGroupToPerm w (-i.val)) := by
  rw [rootLowerMap, gaTangent_comp_conjugation]
  have hm : affineGroupAdjointLieEquiv (G.weylPoint w)
      (gaAffineGroupTangent (G.negativeSimpleRootMap i)) ∈ (G.rootWeightSpace (-i.val)).map
        (affineGroupAdjointLieEquiv (G.weylPoint w)).toLinearEquiv.toLinearMap :=
    Submodule.mem_map.mpr ⟨_, G.negativeRootMap_tangent_mem i, rfl⟩
  rwa [G.weylPoint_rootWeightSpace] at hm

/-- Every positive root has a simple-root Weyl presentation. -/
theorem rootCurve_simple_presentation (β : G.rootIndex) (hβ : G.rootBase.IsPos β) :
    ∃ (w : G.weylGroup) (i : G.rootBase.support),
      G.rootSystem.weylGroupToPerm w i.val = β := by
  obtain ⟨word, _, i, _, hi⟩ :=
    SupportedRootReflectionWord.positive_root_exists_simple_word G.rootBase
      Set.univ β hβ (Set.subset_univ _)
  exact ⟨simpleWeylWord G.rootBase word, i, hi.symm⟩

/-- Every positive root has a specified coordinate SL₂ morphism with its paired root maps. -/
theorem exists_rootSl2_parameter (β : G.rootIndex) (hβ : G.rootBase.IsPos β) :
    ∃ (w : G.weylGroup) (i : G.rootBase.support),
      G.rootSystem.weylGroupToPerm w i.val = β ∧
      ∃ φ : G.coordinateAlgebra →ₐc[K] SpecialLinear.coordinateHopfAlgebra K 2,
        (SpecialLinear.rootSubgroupCoordinateMap (R := K)
            (zero_ne_one : (0 : Fin 2) ≠ 1)).hom.comp φ = rootUpperMap G w i ∧
        (SpecialLinear.rootSubgroupCoordinateMap (R := K)
            (one_ne_zero : (1 : Fin 2) ≠ 0)).hom.comp φ = rootLowerMap G w i := by
  obtain ⟨w, i, hi⟩ := rootCurve_simple_presentation G β hβ
  exact ⟨w, i, hi, rootSl2Map G w i, rootSl2Map_upper G w i, rootSl2Map_lower G w i⟩

end SchubertGeometry
