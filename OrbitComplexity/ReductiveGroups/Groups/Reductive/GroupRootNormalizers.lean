import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupRootSupport
import OrbitComplexity.ReductiveGroups.Groups.RootCoordinates.BorelRootCommutatorFormula

/-! # Normalization of closed root-support groups

Ordered root products reduce subgroup containment to the root maps. The commutator formula
then proves normalization whenever all commutator roots stay in the prescribed support.
-/

noncomputable section
namespace ReductiveGroups.ReductiveGroupData
open TauCeti
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

/-- A subgroup containing every supported root map contains the whole root-support group. -/
theorem rootSubsetPoints_le_of_maps (R : Set G.rootIndex)
    (hR : IsPositiveRootClosed G.rootBase R) (H : Subgroup G.points)
    (hmaps : ∀ (i : G.rootCharacters R) (a : K),
      gaParameterPoint (G.borelRootMaps i.val) a ∈ H) : G.rootSubsetPoints R hR ≤ H := by
  classical
  intro g hg
  have hmap := (congrArg (fun J : Subgroup G.points => g ∈ J)
    (G.rootSubsetPoints_eq R hR)).mp hg
  obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hmap
  let _ := finite_borelRootCharacterIndex G.borelIdeal G.torusSplit G.split_surjective
  let _ : Fintype (G.rootCharacters R) := Fintype.ofFinite _
  let l : List (G.rootCharacters R) := Finset.univ.toList
  have hl : l.Nodup := Finset.nodup_toList _
  have hall : ∀ i, i ∈ l := fun i => Finset.mem_toList.mpr (Finset.mem_univ i)
  have hxU (i) : gaAffineGroupTangent (G.borelRootMaps i) ∈ G.unipotentTangent :=
    G.borelRootBasis_tangent i ▸ (G.borelRootBasis i).property
  obtain ⟨a, ha⟩ := borelRootSubsetProduct_surjective G.torusIdeal G.borelIdeal
    G.borel_le_torus G.isMaximalTorus G.isBorel G.torusSplit G.split_surjective
    G.split_eq_zero G.reductive G.borelRootMaps G.borelRootBasis G.borelRootBasis_tangent
    G.borelRootMaps_weight hxU (G.rootCharacters_closed R hR) l hl hall v hv
  have he := congrArg Subtype.val ha
  change (l.map (fun i => gaParameterPoint (G.borelRootMaps i.val) (a i))).prod = v.val at he
  change v.val ∈ H
  rw [← he]
  apply H.list_prod_mem
  intro x hx
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
  exact hmaps i (a i)

private theorem root_conjugate_mem (R : Set G.rootIndex)
    (hR : IsPositiveRootClosed G.rootBase R)
    (τ : borelRootCharacterIndex G.borelIdeal G.torusSplit)
    (hcomm : ∀ β : G.rootCharacters R,
      commutatorRootSet τ β.val ⊆ G.rootCharacters R) (a : K)
    (g : G.points) (hg : g ∈ G.rootSubsetPoints R hR) :
    gaParameterPoint (G.borelRootMaps τ) a * g *
      (gaParameterPoint (G.borelRootMaps τ) a)⁻¹ ∈ G.rootSubsetPoints R hR := by
  classical
  let H := (G.rootSubsetPoints R hR).comap
    (MulAut.conj (gaParameterPoint (G.borelRootMaps τ) a)).toMonoidHom
  apply G.rootSubsetPoints_le_of_maps R hR H ?_ hg
  intro β b
  change gaParameterPoint (G.borelRootMaps τ) a *
      gaParameterPoint (G.borelRootMaps β.val) b *
      (gaParameterPoint (G.borelRootMaps τ) a)⁻¹ ∈ G.rootSubsetPoints R hR
  by_cases hτβ : τ = β.val
  · rw [hτβ]
    have hc : gaParameterPoint (G.borelRootMaps β.val) a *
        gaParameterPoint (G.borelRootMaps β.val) b =
      gaParameterPoint (G.borelRootMaps β.val) b *
        gaParameterPoint (G.borelRootMaps β.val) a := by
      simp only [gaParameterPoint, ← map_mul, mul_comm]
    rw [hc, mul_assoc, mul_inv_cancel, mul_one]
    exact G.rootMapPoint_mem_rootSubset R hR β b
  · let _ := finite_borelRootCharacterIndex G.borelIdeal G.torusSplit G.split_surjective
    let _ : Fintype (commutatorRootSet τ β.val) := Fintype.ofFinite _
    let l : List (commutatorRootSet τ β.val) := Finset.univ.toList
    obtain ⟨i, j, c, _, hformula⟩ := borelRoot_commutator_formula G.torusIdeal G.borelIdeal
      G.borel_le_torus G.isMaximalTorus G.isBorel G.torusSplit G.split_surjective
      G.split_eq_zero G.reductive G.borelRootMaps G.borelRootBasis
      G.borelRootBasis_tangent G.borelRootMaps_weight hτβ l (Finset.nodup_toList _)
      (fun k => Finset.mem_toList.mpr (Finset.mem_univ k))
    rw [hformula a b, mul_assoc, mul_inv_cancel, mul_one]
    apply (G.rootSubsetPoints R hR).mul_mem ?_ (G.rootMapPoint_mem_rootSubset R hR β b)
    apply Subgroup.list_prod_mem
    intro x hx
    obtain ⟨γ, _, rfl⟩ := List.mem_map.mp hx
    exact G.rootMapPoint_mem_rootSubset R hR ⟨γ.val, hcomm β γ.property⟩ _

/-- Root maps normalize a closed support containing all their mixed commutator roots. -/
theorem rootMap_mem_rootNormalizer (R : Set G.rootIndex)
    (hR : IsPositiveRootClosed G.rootBase R)
    (τ : borelRootCharacterIndex G.borelIdeal G.torusSplit)
    (hcomm : ∀ β : G.rootCharacters R,
      commutatorRootSet τ β.val ⊆ G.rootCharacters R) (a : K) :
    gaParameterPoint (G.borelRootMaps τ) a ∈
      Subgroup.normalizer (G.rootSubsetPoints R hR : Set G.points) := by
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · exact root_conjugate_mem G R hR τ hcomm a g
  · intro hg
    have hback := root_conjugate_mem G R hR τ hcomm (-a)
      (gaParameterPoint (G.borelRootMaps τ) a * g *
        (gaParameterPoint (G.borelRootMaps τ) a)⁻¹) hg
    have hi : gaParameterPoint (G.borelRootMaps τ) (-a) =
        (gaParameterPoint (G.borelRootMaps τ) a)⁻¹ := by
      simp only [gaParameterPoint, ofAdd_neg, map_inv]
    rw [hi] at hback
    simpa only [inv_inv, mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using hback

end ReductiveGroups.ReductiveGroupData
