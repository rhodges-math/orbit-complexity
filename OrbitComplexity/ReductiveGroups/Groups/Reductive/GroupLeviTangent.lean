import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupLeviInclusions
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupBorelTangent
import OrbitComplexity.ReductiveGroups.Groups.Representations.ConjugateSubgroupTangent
import OrbitComplexity.ReductiveGroups.Groups.Characters.AffineGroupCharacterWeights
import OrbitComplexity.ReductiveGroups.Groups.RootCoordinates.BorelRootFamilyIndependence
import OrbitComplexity.ReductiveGroups.Groups.Tori.TorusPointCharacterValues

/-!
# Root support of Levi tangent spaces

The tangent space of the centralizer is fixed by every point of the selected
simple-character common kernel. A root outside the selected simple-root span
has a character value different from one on that kernel, so its intersection
with the Levi tangent space is zero.
-/

noncomputable section
namespace ReductiveGroups.ReductiveGroupData
open TauCeti WithConv
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

/-- Every tangent vector to the Levi centralizer is fixed by each point of its center. -/
theorem leviTangent_fixed (I : Set G.rootBase.support) (d : G.tangent)
    (hd : d ∈ G.subgroupTangent (G.leviIdeal I))
    (z : G.points) (hz : z ∈ G.leviCenterPoints I) :
    affineGroupAdjointRepresentation z d = d := by
  have heq : derivationComp (B := K) (affineGroupConjugationBialgHom z) d = d := by
    ext a
    change d (affineGroupConjugationAlgHom z a) = d a
    apply sub_eq_zero.mp
    rw [← map_sub]
    apply (tangent_mem_hopfQuotient_iff (G.leviIdeal I) d).mp hd
    change affineGroupConjugationAlgHom z a - a ∈ HopfIdeal.vanishingIdeal (G.leviPoints I)
    apply (HopfIdeal.mem_vanishingIdeal _ _).mpr
    intro x
    have hp := affineGroupConjugationAlgHom_point z x.val
    change toConv (x.val.ofConv.comp (affineGroupConjugationAlgHom z)) =
      z * x.val * z⁻¹ at hp
    have hc : z * x.val * z⁻¹ = x.val := by
      rw [x.property z hz]
      group
    rw [hc] at hp
    have hv := congrArg (fun p : G.points => p.ofConv a) hp
    change x.val.ofConv (affineGroupConjugationAlgHom z a) = x.val.ofConv a at hv
    simpa only [map_sub, sub_eq_zero] using hv
  simpa only [DerivationComp.conjugation, affineGroupAdjointRepresentation_apply] using heq

/-- A Levi tangent character vector vanishes if a central point has a nontrivial
value on its character. -/
theorem leviTangent_eq_zero_of_weight (I : Set G.rootBase.support)
    (α : G.characters) (t : WithConv (MonoidAlgebra K G.characters →ₐ[K] K))
    (ht : AlgHom.mapDomain G.torusSplit t ∈ G.leviCenterPoints I)
    (hα : t.ofConv (MonoidAlgebra.single α 1) ≠ 1)
    (d : G.tangent) (hd : d ∈ G.subgroupTangent (G.leviIdeal I))
    (hw : d ∈ affineGroupCharacterWeightSpace G.torusSplit α) : d = 0 := by
  have hf := leviTangent_fixed G I d hd (AlgHom.mapDomain G.torusSplit t) ht
  have he := AffineGroupAdjoint.eq_character_of_mem_weight G.torusSplit α t d hw
  have hs : (t.ofConv (MonoidAlgebra.single α 1) - 1) • d = 0 := by
    calc
      _ = t.ofConv (MonoidAlgebra.single α 1) • d - (1 : K) • d :=
        sub_smul _ _ _
      _ = 0 := by rw [one_smul]; exact sub_eq_zero.mpr (he.symm.trans hf)
  exact (smul_eq_zero.mp hs).resolve_left (sub_ne_zero.mpr hα)


/-- A root outside the selected simple-root span has character value two at a Levi center point. -/
theorem exists_leviCenter_root_two (I : Set G.rootBase.support) (r : G.rootIndex)
    (hr : G.rootSystem.root r ∉ Submodule.span K (G.rootBase.toWeightBasis '' I)) :
    ∃ t : WithConv (MonoidAlgebra K G.characters →ₐ[K] K),
      AlgHom.mapDomain G.torusSplit t ∈ G.leviCenterPoints I ∧
      t.ofConv (MonoidAlgebra.single (G.rootCharacter r) 1) = 2 := by
  classical
  let α : Option I → {α : G.characters //
      affineGroupCharacterWeightSpace G.torusSplit α ≠ ⊥ ∧ α ≠ 1} := fun o =>
    Option.casesOn' o (G.characterRootEquiv.symm r)
      (fun j => G.characterRootEquiv.symm j.val.val)
  have hroots : (fun o => G.rootSystem.root (G.characterRootEquiv (α o))) =
      (fun o : Option I => Option.casesOn' o (G.rootSystem.root r)
        (fun j : I => G.rootSystem.root j.val.val)) := by
    funext o
    cases o with
    | none => simp [α]
    | some j => simp [α]
  have hind : LinearIndependent K (fun o => G.rootSystem.root (G.characterRootEquiv (α o))) := by
    rw [hroots]
    apply LinearIndependent.option
    · have h := G.rootBase.toWeightBasis.linearIndependent.comp (fun j : I => j.val)
        Subtype.val_injective
      simpa [Function.comp_def, RootPairing.Base.toWeightBasis_apply] using h
    · have he : Set.range (fun j : I => G.rootSystem.root j.val.val) =
          G.rootBase.toWeightBasis '' I := by
        ext v
        simp [RootPairing.Base.toWeightBasis_apply]
      exact he ▸ hr
  have hlin := OccurringCharacter.family_linearIndependent G.torusIdeal G.isMaximalTorus
    G.torusSplit G.split_surjective G.split_eq_zero G.reductive α hind
  obtain ⟨t, ht⟩ := exists_torusPoint_character_values (K := K) (fun o => (α o).val) hlin
    (fun o => Option.casesOn' o (Units.mk0 (2 : K) two_ne_zero) (fun _ => 1))
  refine ⟨t, ?_, ?_⟩
  · refine ⟨t, rfl, ?_⟩
    intro j hj
    have h := ht (some ⟨j, hj⟩)
    simp only [Option.casesOn', Units.val_one] at h
    exact h
  · have h := ht none
    simp only [Option.casesOn', Units.val_mk0] at h
    exact h

/-- No nonzero Levi tangent vector has a root weight outside the selected simple-root span. -/
theorem leviTangent_eq_zero_of_root (I : Set G.rootBase.support) (r : G.rootIndex)
    (hr : G.rootSystem.root r ∉ Submodule.span K (G.rootBase.toWeightBasis '' I))
    (d : G.tangent) (hd : d ∈ G.subgroupTangent (G.leviIdeal I))
    (hw : d ∈ G.rootWeightSpace r) : d = 0 := by
  obtain ⟨t, ht, he⟩ := exists_leviCenter_root_two G I r hr
  apply leviTangent_eq_zero_of_weight G I (G.rootCharacter r) t ht _ d hd hw
  rw [he]
  norm_num

end ReductiveGroups.ReductiveGroupData
