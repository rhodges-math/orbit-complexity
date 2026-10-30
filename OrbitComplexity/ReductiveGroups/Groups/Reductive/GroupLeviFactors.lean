import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupLeviPoints
import OrbitComplexity.ReductiveGroups.Groups.RootCoordinates.BorelRootCoordinateWeights
import OrbitComplexity.ReductiveGroups.Groups.Borel.BorelTorusUnipotent
import Batteries.Tactic.Lint

/-!
# Unipotent factors of standard Levi subgroups

The root logarithm coordinates outside the selected Levi support vanish for
a centralizing point. The Borel torus--unipotent factorization then restricts.
-/

noncomputable section
namespace ReductiveGroups.ReductiveGroupData
open TauCeti
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

omit [IsAlgClosed K] [CharZero K] in
private theorem eq_zero_of_twice {c : K} (h : c = 2 * c) : c = 0 := by
  have h' : c + 0 = c + c := by simpa only [two_mul, add_zero] using h
  exact (add_left_cancel h').symm

/-- A unipotent point fixed by conjugation by the maximal torus is identity. -/
theorem unipotent_eq_one_of_torus_conj (u : G.points)
    (hu : u ∈ G.unipotentPoints)
    (hf : ∀ t ∈ G.torusPoints, t * u * t⁻¹ = u) : u = 1 := by
  let d : G.unipotentTangent :=
    (@borelRootUnipotentExponentialEquiv K G.coordinateAlgebra G.torusIndex
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
      G.borelIdeal G.isBorel G.torusSplit G.split_surjective).symm ⟨u, hu⟩
  have he (i : borelRootCharacterIndex G.borelIdeal G.torusSplit) :
      (G.borelRootBasis i).val ∈ affineGroupCharacterWeightSpace G.torusSplit i.val := by
    rw [G.borelRootBasis_tangent]
    exact G.borelRootMaps_weight i
  have hcoord (i : borelRootCharacterIndex G.borelIdeal G.torusSplit) :
      G.borelRootBasis.coord i d = 0 := by
    obtain ⟨t, ht⟩ := @exists_torusPoint_character_value K G.torusIndex
      inferInstance inferInstance i.val i.property.1 (2 : K) (by norm_num)
    have htmem := @mapDomain_mem_torusPoints K G.coordinateAlgebra G.torusIndex
      inferInstance inferInstance inferInstance G.torusIdeal G.torusSplit
      G.split_surjective G.split_eq_zero t
    obtain ⟨huz, hlog⟩ :=
      @BorelRootUnipotentExponentialEquiv.symm_torus_conjugate
        K G.coordinateAlgebra G.torusIndex
        inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
        G.finiteIndex G.torusIdeal G.borelIdeal G.borel_le_torus
        G.isMaximalTorus G.isBorel G.torusSplit G.split_surjective G.split_eq_zero
        G.reductive t ⟨u, hu⟩
    have hp : (⟨AlgHom.mapDomain G.torusSplit t * u *
        (AlgHom.mapDomain G.torusSplit t)⁻¹, huz⟩ : G.unipotentPoints) = ⟨u, hu⟩ :=
      Subtype.ext (hf _ htmem)
    have hlogc := congrArg (G.borelRootBasis.coord i)
      ((congrArg (@borelRootUnipotentExponentialEquiv K G.coordinateAlgebra G.torusIndex
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
      G.borelIdeal G.isBorel G.torusSplit G.split_surjective).symm hp).symm.trans hlog)
    have hc := @borelRootCoordinateBasis_coord_torus_ad
      K G.coordinateAlgebra G.torusIndex
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
      G.finiteIndex G.torusIdeal G.borelIdeal G.borel_le_torus
      G.isMaximalTorus G.isBorel G.torusSplit G.split_surjective G.split_eq_zero
      G.reductive G.borelRootBasis he t i d
    rw [ht] at hc
    exact eq_zero_of_twice (hlogc.trans hc)
  have hd : d = 0 := G.borelRootBasis.forall_coord_eq_zero_iff.mp hcoord
  have hexp := (@borelRootUnipotentExponentialEquiv K G.coordinateAlgebra G.torusIndex
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
      G.borelIdeal G.isBorel G.torusSplit G.split_surjective).apply_symm_apply
        (⟨u, hu⟩ : G.unipotentPoints)
  have hval := congrArg Subtype.val hexp
  change borelRootUnipotentExponential G.borelIdeal G.isBorel G.torusSplit
    G.split_surjective d = u at hval
  rw [hd] at hval
  exact hval.symm.trans
    (@borelRootUnipotentExponential_zero K G.coordinateAlgebra G.torusIndex
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
      G.borelIdeal G.isBorel G.torusSplit G.split_surjective)

/-- The unipotent part of the standard Levi consists of its positive-root subgroup. -/
theorem levi_unipotent_eq (I : Set G.rootBase.support) :
    G.leviPoints I ⊓ G.unipotentPoints =
      G.rootSubsetPoints (leviPositiveRoots G.rootBase I)
        (LeviRootSpan.isPositiveRootClosed G.rootBase I) := by
  apply le_antisymm
  · intro u hu
    have hL : u ∈ G.leviPoints I := hu.1
    have hU : u ∈ G.unipotentPoints := hu.2
    rw [G.rootSubsetPoints_eq]
    apply Subgroup.mem_map.mpr
    refine ⟨⟨u, hU⟩, ?_, rfl⟩
    intro i hi
    obtain ⟨z, hz, hzi⟩ := exists_leviCenter_character_two G.torusIdeal G.borelIdeal
      G.borel_le_torus G.isMaximalTorus G.isBorel G.torusSplit G.split_surjective
      G.split_eq_zero G.reductive I i hi
    have hc := hL (AlgHom.mapDomain G.torusSplit z) ⟨z, rfl, hz⟩
    have hraw : AlgHom.mapDomain G.torusSplit z * u *
        (AlgHom.mapDomain G.torusSplit z)⁻¹ = u :=
      (mul_inv_eq_iff_eq_mul).mpr hc
    obtain ⟨huz, hlog⟩ := BorelRootUnipotentExponentialEquiv.symm_torus_conjugate
      G.torusIdeal G.borelIdeal G.borel_le_torus G.isMaximalTorus G.isBorel G.torusSplit
      G.split_surjective G.split_eq_zero G.reductive z ⟨u, hU⟩
    have heq : (⟨AlgHom.mapDomain G.torusSplit z * u *
        (AlgHom.mapDomain G.torusSplit z)⁻¹, huz⟩ : G.unipotentPoints) = ⟨u, hU⟩ :=
      Subtype.ext hraw
    have hlog' := (congrArg
      (borelRootUnipotentExponentialEquiv G.borelIdeal G.isBorel G.torusSplit
        G.split_surjective).symm heq).symm.trans hlog
    have hcoord := (congrArg (G.borelRootBasis.coord i) hlog').trans
      (borelRootCoordinateBasis_coord_torus_ad G.torusIdeal G.borelIdeal
      G.borel_le_torus G.isMaximalTorus G.isBorel G.torusSplit G.split_surjective
      G.split_eq_zero G.reductive G.borelRootBasis
      (fun j => G.borelRootBasis_tangent j ▸ G.borelRootMaps_weight j) z i _)
    rw [hzi] at hcoord
    exact eq_zero_of_twice hcoord
  · exact le_inf
      (G.rootSubsetPoints_le_leviPoints I _ _ (Set.Subset.refl _))
      (G.rootSubsetPoints_le_unipotent _ _)

/-- Every Levi--Borel point factors as a torus point and a positive Levi-root point. -/
theorem leviBorel_exists_torus_mul (I : Set G.rootBase.support)
    (b : G.points) (hb : b ∈ G.leviBorelPoints I) :
    ∃ t ∈ G.torusPoints, ∃ u ∈ G.rootSubsetPoints (leviPositiveRoots G.rootBase I)
      (LeviRootSpan.isPositiveRootClosed G.rootBase I), t * u = b := by
  obtain ⟨t, ht, u, hu, htu⟩ := BorelPoint.exists_torus_mul_borelRootUnipotent
    G.torusIdeal G.borelIdeal G.borel_le_torus G.isMaximalTorus G.isBorel G.torusSplit
    G.split_surjective G.split_eq_zero G.reductive b hb.2
  refine ⟨t, ht, u, ?_, htu⟩
  rw [← G.levi_unipotent_eq I]
  refine ⟨?_, hu⟩
  have htuL := (G.leviPoints I).mul_mem ((G.leviPoints I).inv_mem
    (G.torus_le_leviPoints I ht)) hb.1
  rwa [← htu, inv_mul_cancel_left] at htuL

end ReductiveGroups.ReductiveGroupData
