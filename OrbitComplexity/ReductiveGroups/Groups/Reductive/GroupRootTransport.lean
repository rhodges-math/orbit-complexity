import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupRootSupport
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupRoots
import OrbitComplexity.ReductiveGroups.Groups.GaCoordinates.GaConjugateTangent

/-!
# Weyl transport of closed positive-root groups

Adjoint transport of the generating root spaces gives conjugation containment
for closed root-support groups. If the Weyl image is positive, the corresponding
closed root-support groups are conjugate.
-/

set_option maxHeartbeats 400000
noncomputable section
namespace ReductiveGroups.ReductiveGroupData
open TauCeti
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

/-- Adjoint root-space containment gives conjugation into the target closed subgroup. -/
theorem rootSubsetPoints_conj_mem (g₀ : G.points) (R : Set G.rootIndex)
    (hR : IsPositiveRootClosed G.rootBase R)
    (I : HopfIdeal K G.coordinateAlgebra)
    (hI : ∀ r ∈ R, (G.rootWeightSpace r).map
      (affineGroupAdjointLieEquiv g₀).toLinearEquiv.toLinearMap ≤
      (hopfTangentImage I).toSubmodule)
    (g : G.points) (hg : g ∈ G.rootSubsetPoints R hR) :
    g₀ * g * g₀⁻¹ ∈ CommHopfAlgCat.quotientPointsSubgroup
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
      (MulAut.conj g₀).toMonoidHom
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
    have had : affineGroupAdjointLieEquiv g₀
        (gaAffineGroupTangent (G.borelRootMaps i.val)) ∈ hopfTangentImage I := by
      have hw : affineGroupAdjointLieEquiv g₀
          (gaAffineGroupTangent (G.borelRootMaps i.val)) ∈
          (G.rootWeightSpace r).map
            (affineGroupAdjointLieEquiv g₀).toLinearEquiv.toLinearMap :=
        Submodule.mem_map.mpr ⟨_, hweight, rfl⟩
      exact hI r i.property hw
    have hpoint := GaParameterPoint.mem_of_tangent_mem_quotient
      ((G.borelRootMaps i.val).comp (affineGroupConjugationBialgHom g₀))
      I (by rwa [gaTangent_comp_conjugation]) (a i)
    have hc := gaPoints_comp_conjugation (G.borelRootMaps i.val) g₀
      (Multiplicative.ofAdd (a i))
    change gaParameterPoint _ (a i) =
      g₀ * gaParameterPoint (G.borelRootMaps i.val) (a i) *
        (g₀)⁻¹ at hc
    change g₀ * gaParameterPoint (G.borelRootMaps i.val) (a i) *
      (g₀)⁻¹ ∈ CommHopfAlgCat.quotientPointsSubgroup
      (CommHopfAlgCat.of K G.coordinateAlgebra) I (CommAlgCat.of K K)
    rw [← hc]
    exact hpoint
  rw [hval] at hprod
  change g₀ * u.val * (g₀)⁻¹ ∈
    CommHopfAlgCat.quotientPointsSubgroup (CommHopfAlgCat.of K G.coordinateAlgebra) I
      (CommAlgCat.of K K) at hprod
  change g₀ * u.val * g₀⁻¹ ∈ CommHopfAlgCat.quotientPointsSubgroup
      (CommHopfAlgCat.of K G.coordinateAlgebra) I (CommAlgCat.of K K)
  exact hprod

/-- A Weyl representative conjugates a closed support into its positive root image. -/
theorem rootSubsetPoints_weyl_conj (w : G.weylGroup) (R S : Set G.rootIndex)
    (hR : IsPositiveRootClosed G.rootBase R) (hS : IsPositiveRootClosed G.rootBase S)
    (hmap : ∀ r ∈ R, G.rootBase.IsPos (G.rootSystem.weylGroupToPerm w r) ∧
      G.rootSystem.weylGroupToPerm w r ∈ S)
    (g : G.points) (hg : g ∈ G.rootSubsetPoints R hR) :
    G.weylPoint w * g * (G.weylPoint w)⁻¹ ∈ G.rootSubsetPoints S hS := by
  apply G.rootSubsetPoints_conj_mem (G.weylPoint w) R hR (G.rootSubsetIdeal S hS) ?_ g hg
  intro r hr
  rw [G.weylPoint_rootWeightSpace]
  exact G.rootWeightSpace_le_rootSubset S hS _ (hmap r hr).1 (hmap r hr).2

/-- Positive Weyl transport identifies the corresponding closed root-support point subgroups. -/
theorem rootSubsetPoints_weyl_eq (w : G.weylGroup) (R S : Set G.rootIndex)
    (hR : IsPositiveRootClosed G.rootBase R) (hS : IsPositiveRootClosed G.rootBase S)
    (hposR : ∀ r ∈ R, G.rootBase.IsPos r) (hposS : ∀ s ∈ S, G.rootBase.IsPos s)
    (himage : S = G.rootSystem.weylGroupToPerm w '' R) :
    (G.rootSubsetPoints R hR).map (MulAut.conj (G.weylPoint w)).toMonoidHom =
      G.rootSubsetPoints S hS := by
  apply le_antisymm
  · intro g hg
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hg
    apply G.rootSubsetPoints_weyl_conj w R S hR hS ?_ u hu
    intro r hr
    have hs : G.rootSystem.weylGroupToPerm w r ∈ S := by rw [himage]; exact ⟨r, hr, rfl⟩
    exact ⟨hposS _ hs, hs⟩
  · intro g hg
    have hcomp :
        (affineGroupAdjointLieEquiv (G.weylPoint w)⁻¹).toLinearEquiv.toLinearMap.comp
          (affineGroupAdjointLieEquiv (G.weylPoint w)).toLinearEquiv.toLinearMap =
        LinearMap.id := by
      apply LinearMap.ext
      intro d
      change affineGroupAdjointRepresentation (G.weylPoint w)⁻¹
        (affineGroupAdjointRepresentation (G.weylPoint w) d) = d
      rw [← Module.End.mul_apply, ← map_mul]
      simp
    have hrev : (G.weylPoint w)⁻¹ * g * G.weylPoint w ∈ G.rootSubsetPoints R hR := by
      have h := G.rootSubsetPoints_conj_mem (G.weylPoint w)⁻¹ S hS
        (G.rootSubsetIdeal R hR) ?_ g hg
      · change (G.weylPoint w)⁻¹ * g * ((G.weylPoint w)⁻¹)⁻¹ ∈
          G.rootSubsetPoints R hR at h
        simpa only [inv_inv] using h
      intro s hs
      rw [himage] at hs
      obtain ⟨r, hr, rfl⟩ := hs
      rw [← G.weylPoint_rootWeightSpace w r, ← Submodule.map_comp, hcomp, Submodule.map_id]
      exact G.rootWeightSpace_le_rootSubset R hR r (hposR r hr) hr
    refine Subgroup.mem_map.mpr ⟨(G.weylPoint w)⁻¹ * g * G.weylPoint w, hrev, ?_⟩
    change G.weylPoint w * ((G.weylPoint w)⁻¹ * g * G.weylPoint w) *
      (G.weylPoint w)⁻¹ = g
    group

end ReductiveGroups.ReductiveGroupData
