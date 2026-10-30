import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupRootCoordinates
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupOppositePoints
import OrbitComplexity.ReductiveGroups.Groups.GaCoordinates.GaConjugateTangent

/-!
# Conjugation of closed root-support subgroups

Inverse Weyl representatives send root-support groups into closed subgroups
whose tangents contain the transformed root spaces. Inversion supports land in
the opposite unipotent subgroup, and positive noninversion supports land in the
unipotent subgroup.
-/

set_option maxHeartbeats 400000
noncomputable section
namespace ReductiveGroups.ReductiveGroupData
open TauCeti
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

private theorem weylPoint_inv_rootWeightSpace (w : G.weylGroup) (r : G.rootIndex) :
    (G.rootWeightSpace r).map
      ((affineGroupAdjointLieEquiv (G.weylPoint w)⁻¹).toLinearEquiv.toLinearMap) =
      G.rootWeightSpace (G.rootSystem.weylGroupToPerm w⁻¹ r) := by
  have hcomp :
      ((affineGroupAdjointLieEquiv (G.weylPoint w)⁻¹ ).toLinearEquiv.toLinearMap).comp
        ((affineGroupAdjointLieEquiv (G.weylPoint w)).toLinearEquiv.toLinearMap) =
      LinearMap.id := by
    apply LinearMap.ext
    intro d
    change affineGroupAdjointRepresentation (G.weylPoint w)⁻¹
      (affineGroupAdjointRepresentation (G.weylPoint w) d) = d
    rw [← Module.End.mul_apply, ← map_mul]
    simp
  have h := congrArg (fun S : Submodule K G.tangent => S.map
    ((affineGroupAdjointLieEquiv (G.weylPoint w)⁻¹ ).toLinearEquiv.toLinearMap))
      (G.weylPoint_rootWeightSpace w (G.rootSystem.weylGroupToPerm w⁻¹ r))
  simp only [← Submodule.map_comp, hcomp, Submodule.map_id] at h
  simpa only [map_inv, Equiv.Perm.coe_inv, Equiv.apply_symm_apply] using h.symm

private theorem rootSubsetPoints_conj_mem (w : G.weylGroup) (R : Set G.rootIndex)
    (hR : IsPositiveRootClosed G.rootBase R)
    (I : HopfIdeal K G.coordinateAlgebra)
    (hI : ∀ r ∈ R, G.rootWeightSpace (G.rootSystem.weylGroupToPerm w⁻¹ r) ≤
      (hopfTangentImage I).toSubmodule)
    (g : G.points) (hg : g ∈ G.rootSubsetPoints R hR) :
    (G.weylPoint w)⁻¹ * g * G.weylPoint w ∈ CommHopfAlgCat.quotientPointsSubgroup
      (CommHopfAlgCat.of K G.coordinateAlgebra) I (CommAlgCat.of K K) := by
  classical
  have hmap := (congrArg (fun H : Subgroup G.points => g ∈ H)
    (G.rootSubsetPoints_eq R hR)).mp hg
  obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hmap
  let _ := finite_borelRootCharacterIndex G.borelIdeal G.torusSplit G.split_surjective
  let _ : Fintype (G.rootCharacters R) := Fintype.ofFinite _
  let l : List (G.rootCharacters R) := Finset.univ.toList
  have hl : l.Nodup := Finset.nodup_toList _
  have hall : ∀ i, i ∈ l := by intro i; exact Finset.mem_toList.mpr (Finset.mem_univ i)
  have hxU (i) : gaAffineGroupTangent (G.borelRootMaps i) ∈ G.unipotentTangent :=
    G.borelRootBasis_tangent i ▸ (G.borelRootBasis i).property
  obtain ⟨a, ha⟩ := borelRootSubsetProduct_surjective G.torusIdeal G.borelIdeal
    G.borel_le_torus G.isMaximalTorus G.isBorel G.torusSplit G.split_surjective
    G.split_eq_zero G.reductive G.borelRootMaps G.borelRootBasis G.borelRootBasis_tangent
    G.borelRootMaps_weight hxU (G.rootCharacters_closed R hR) l hl hall u hu
  have hval : (l.map (fun i => gaParameterPoint (G.borelRootMaps i.val) (a i))).prod =
      u.val := congrArg Subtype.val ha
  let H := (CommHopfAlgCat.quotientPointsSubgroup
    (CommHopfAlgCat.of K G.coordinateAlgebra) I (CommAlgCat.of K K)).comap
      (MulAut.conj (G.weylPoint w)⁻¹).toMonoidHom
  have hprod : (l.map (fun i => gaParameterPoint (G.borelRootMaps i.val) (a i))).prod ∈ H := by
    apply Subgroup.list_prod_mem
    intro p hp
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hp
    let r := G.characterRootEquiv
      (borelRootCharacterOccurring G.borelIdeal G.torusSplit i.val)
    have hchar : G.rootCharacter r = i.val.val := by
      change (G.characterRootEquiv.symm (G.characterRootEquiv _)).val = i.val.val
      rw [Equiv.symm_apply_apply]
      rfl
    have hweight : gaAffineGroupTangent (G.borelRootMaps i.val) ∈ G.rootWeightSpace r := by
      change _ ∈ affineGroupCharacterWeightSpace G.torusSplit (G.rootCharacter r)
      rw [hchar]
      exact G.borelRootMaps_weight i.val
    have had : affineGroupAdjointLieEquiv (G.weylPoint w)⁻¹
        (gaAffineGroupTangent (G.borelRootMaps i.val)) ∈ hopfTangentImage I := by
      have hw : affineGroupAdjointLieEquiv (G.weylPoint w)⁻¹
          (gaAffineGroupTangent (G.borelRootMaps i.val)) ∈
          (G.rootWeightSpace r).map
            (affineGroupAdjointLieEquiv (G.weylPoint w)⁻¹).toLinearEquiv.toLinearMap :=
        Submodule.mem_map.mpr ⟨_, hweight, rfl⟩
      rw [G.weylPoint_inv_rootWeightSpace w r] at hw
      exact hI r i.property hw
    have hpoint := GaParameterPoint.mem_of_tangent_mem_quotient
      ((G.borelRootMaps i.val).comp (affineGroupConjugationBialgHom (G.weylPoint w)⁻¹))
      I (by rwa [gaTangent_comp_conjugation]) (a i)
    have hc := gaPoints_comp_conjugation (G.borelRootMaps i.val) (G.weylPoint w)⁻¹
      (Multiplicative.ofAdd (a i))
    change gaParameterPoint _ (a i) =
      (G.weylPoint w)⁻¹ * gaParameterPoint (G.borelRootMaps i.val) (a i) *
        ((G.weylPoint w)⁻¹)⁻¹ at hc
    change (G.weylPoint w)⁻¹ * gaParameterPoint (G.borelRootMaps i.val) (a i) *
      ((G.weylPoint w)⁻¹)⁻¹ ∈ CommHopfAlgCat.quotientPointsSubgroup
      (CommHopfAlgCat.of K G.coordinateAlgebra) I (CommAlgCat.of K K)
    rw [← hc]
    exact hpoint
  rw [hval] at hprod
  change (G.weylPoint w)⁻¹ * u.val * ((G.weylPoint w)⁻¹)⁻¹ ∈
    CommHopfAlgCat.quotientPointsSubgroup (CommHopfAlgCat.of K G.coordinateAlgebra) I
      (CommAlgCat.of K K) at hprod
  change (G.weylPoint w)⁻¹ * u.val * G.weylPoint w ∈ CommHopfAlgCat.quotientPointsSubgroup
      (CommHopfAlgCat.of K G.coordinateAlgebra) I (CommAlgCat.of K K)
  simpa only [inv_inv] using hprod

/-- A Weyl representative carries negative-transformed root supports into the opposite group. -/
theorem rootSubsetPoints_conj_opposite (w : G.weylGroup) (R : Set G.rootIndex)
    (hR : IsPositiveRootClosed G.rootBase R)
    (hneg : ∀ r ∈ R, ¬ G.rootBase.IsPos (G.rootSystem.weylGroupToPerm w⁻¹ r))
    (g : G.points) (hg : g ∈ G.rootSubsetPoints R hR) :
    (G.weylPoint w)⁻¹ * g * G.weylPoint w ∈ G.oppositeUnipotentPoints := by
  apply G.rootSubsetPoints_conj_mem w R hR G.oppositeUnipotentIdeal ?_ g hg
  intro r hr
  change _ ≤ G.oppositeUnipotentTangent.toSubmodule
  rw [G.oppositeUnipotentTangent_eq_sum]
  exact le_iSup₂_of_le (G.rootSystem.weylGroupToPerm w⁻¹ r) (hneg r hr) le_rfl

/-- A Weyl representative carries positive-transformed root supports into the unipotent group. -/
theorem rootSubsetPoints_conj_unipotent (w : G.weylGroup) (R : Set G.rootIndex)
    (hR : IsPositiveRootClosed G.rootBase R)
    (hpos : ∀ r ∈ R, G.rootBase.IsPos (G.rootSystem.weylGroupToPerm w⁻¹ r))
    (g : G.points) (hg : g ∈ G.rootSubsetPoints R hR) :
    (G.weylPoint w)⁻¹ * g * G.weylPoint w ∈ G.unipotentPoints :=
  G.rootSubsetPoints_conj_mem w R hR G.unipotentIdeal
    (fun r hr => G.rootWeightSpace_le_unipotent _ (hpos r hr)) g hg

/-- Inversion-root points conjugate into the opposite unipotent subgroup. -/
theorem inversionPoints_conj_opposite (w : G.weylGroup) (g : G.points)
    (hg : g ∈ G.rootSubsetPoints (leftRootInversionIndices G.rootBase w)
      (LeftRootInversionIndices.isPositiveRootClosed G.rootBase w)) :
    (G.weylPoint w)⁻¹ * g * G.weylPoint w ∈ G.oppositeUnipotentPoints :=
  G.rootSubsetPoints_conj_opposite w _
    (LeftRootInversionIndices.isPositiveRootClosed G.rootBase w)
    (fun r hr => (mem_leftRootInversionIndices G.rootBase w r).mp hr |>.2) g hg

/-- Positive noninversion-root points conjugate into the unipotent subgroup. -/
theorem noninversionPoints_conj_unipotent (w : G.weylGroup) (g : G.points)
    (hg : g ∈ G.rootSubsetPoints
      {r | G.rootBase.IsPos r ∧ r ∉ leftRootInversionIndices G.rootBase w}
      (PositiveRootClosedSets.isPositiveRootClosed G.rootBase w)) :
    (G.weylPoint w)⁻¹ * g * G.weylPoint w ∈ G.unipotentPoints := by
  apply G.rootSubsetPoints_conj_unipotent w _
    (PositiveRootClosedSets.isPositiveRootClosed G.rootBase w) ?_ g hg
  intro r hr
  by_contra hneg
  exact hr.2 ((mem_leftRootInversionIndices G.rootBase w r).mpr ⟨hr.1, hneg⟩)

end ReductiveGroups.ReductiveGroupData
