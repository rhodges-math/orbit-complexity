import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupSimpleRoots
import OrbitComplexity.ReductiveGroups.Groups.GaCoordinates.GaConjugateTangent
import OrbitComplexity.GroupActions.Tori.WeightedAction
import OrbitComplexity.GroupActions.Varieties.TorusPoints

/-! # Additive root parameters and torus multiplication

Choose each root as a Weyl translate of a simple root, and conjugate the fixed
simple-root parameter by its Weyl representative. Torus multiplication scales
that specified parameter by the corresponding root character.
-/

open CategoryTheory AlgebraicGeometry ReductiveGroups GroupActions TauCeti
noncomputable section
namespace SchubertGeometry
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

private theorem root_exists_simple (r : G.rootIndex) :
    ∃ w : G.weylGroup, ∃ i : G.rootBase.support,
      G.rootSystem.weylGroupToPerm w i.val = r := by
  apply G.rootBase.induction_reflect r
  · intro r hr
    obtain ⟨w, i, hi⟩ := hr
    refine ⟨RootPairing.weylGroup.ofIdx G.rootSystem r * w, i, ?_⟩
    change G.rootSystem.reflectionPerm r (G.rootSystem.weylGroupToPerm w i.val) = _
    rw [hi]
  · intro r hr
    exact ⟨1, ⟨r, hr⟩, rfl⟩
  · intro r j hr _
    obtain ⟨w, i, hi⟩ := hr
    refine ⟨RootPairing.weylGroup.ofIdx G.rootSystem j * w, i, ?_⟩
    change G.rootSystem.reflectionPerm j (G.rootSystem.weylGroupToPerm w i.val) = _
    rw [hi]

private def rootChoice (r : G.rootIndex) : G.weylGroup × G.rootBase.support :=
  ⟨Classical.choose (root_exists_simple G r),
    Classical.choose (Classical.choose_spec (root_exists_simple G r))⟩

private theorem rootChoice_eq (r : G.rootIndex) :
    G.rootSystem.weylGroupToPerm (rootChoice G r).1 (rootChoice G r).2.val = r :=
  Classical.choose_spec (Classical.choose_spec (root_exists_simple G r))

/-- The additive parameter for a root, conjugated from a fixed simple-root map. -/
def rootParameterMap (r : G.rootIndex) :
    G.coordinateAlgebra →ₐc[K] SymmetricAlgebra K K :=
  (G.simpleRootMap (rootChoice G r).2).comp
    (affineGroupConjugationBialgHom (G.weylPoint (rootChoice G r).1))

/-- The root parameter has tangent in its root weight space. -/
theorem rootParameterMap_tangent_mem (r : G.rootIndex) :
    gaAffineGroupTangent (rootParameterMap G r) ∈ G.rootWeightSpace r := by
  rw [rootParameterMap, gaTangent_comp_conjugation]
  have hmem : affineGroupAdjointLieEquiv (G.weylPoint (rootChoice G r).1)
      (gaAffineGroupTangent (G.simpleRootMap (rootChoice G r).2)) ∈
      (G.rootWeightSpace (rootChoice G r).2.val).map
        ((affineGroupAdjointLieEquiv (G.weylPoint (rootChoice G r).1)).toLinearEquiv :
          G.tangent →ₗ[K] G.tangent) :=
    Submodule.mem_map.mpr ⟨_, G.simpleRootMap_tangent_mem _, rfl⟩
  rw [G.weylPoint_rootWeightSpace, rootChoice_eq] at hmem
  exact hmem

/-- The root parameter has nonzero tangent. -/
theorem rootParameterMap_tangent_ne_zero (r : G.rootIndex) :
    gaAffineGroupTangent (rootParameterMap G r) ≠ 0 := by
  intro h
  rw [rootParameterMap, gaTangent_comp_conjugation] at h
  let e : G.tangent ≃ₗ[K] G.tangent :=
    (affineGroupAdjointLieEquiv (G.weylPoint (rootChoice G r).1)).toLinearEquiv
  have he : e (gaAffineGroupTangent (G.simpleRootMap (rootChoice G r).2)) = 0 := h
  apply G.simpleRootMap_tangent_ne_zero (rootChoice G r).2
  exact e.injective (by simpa only [map_zero] using he)

omit [IsAlgClosed K] [CharZero K] in
private theorem torusReduced : IsReduced G.torusAlgebra := by
  have : Algebra.Smooth K G.torusAlgebra := G.torus_smooth
  exact TauCeti.isReduced_of_smooth K G.torusAlgebra

attribute [local instance] torusReduced

omit [IsAlgClosed K] [CharZero K] in
private theorem torus_split (t : (torusVariety G).points) :
    (torusPointsMulEquiv G t : G.points) =
      AlgHom.mapDomain G.torusSplit (WithConv.toConv
        ((affinePointsEquiv.symm t).comp (torusCoordinateEquiv G).symm.toAlgHom)) := by
  rw [torusPointsMulEquiv_coe]
  apply WithConv.ofConv_injective
  apply AlgHom.ext
  intro a
  change affinePointsEquiv.symm t (Ideal.Quotient.mk G.torusIdeal.toIdeal a) =
    affinePointsEquiv.symm t ((torusCoordinateEquiv G).symm (G.torusSplit a))
  rw [← torusCoordinateEquiv_mk]
  exact congrArg (affinePointsEquiv.symm t) ((torusCoordinateEquiv G).symm_apply_apply _).symm

/-- Torus multiplication scales the chosen root parameter by its root character. -/
theorem rootParameter_torus_mul (r : G.rootIndex) (t : (torusVariety G).points) (a : K) :
    (torusPointsMulEquiv G t : G.points) * gaParameterPoint (rootParameterMap G r) a =
      gaParameterPoint (rootParameterMap G r)
        (torusWeightCharacter G (G.rootCharacter r).toAdd t * a) *
          (torusPointsMulEquiv G t : G.points) := by
  have h := GaAffineGroupPoints.conjugate_of_character_weight G.torusSplit
    (G.rootCharacter r) (WithConv.toConv
      ((affinePointsEquiv.symm t).comp (torusCoordinateEquiv G).symm.toAlgHom))
        (rootParameterMap G r) (rootParameterMap_tangent_mem G r) a
  rw [← torus_split G t] at h
  exact (mul_inv_eq_iff_eq_mul).mp h

end SchubertGeometry
