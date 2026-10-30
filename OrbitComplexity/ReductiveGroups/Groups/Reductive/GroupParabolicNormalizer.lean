import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupRootNormalizers
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupRootTransport
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupRootTorus
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupRootIntersection
import OrbitComplexity.ReductiveGroups.Groups.Reductive.CharacterRelations
import OrbitComplexity.ReductiveGroups.Groups.Borel.BorelTorusUnipotent
import OrbitComplexity.ReductiveGroups.Roots.Parabolic.LeviComplement

/-! # Normalizers of parabolic root complements

Positive mixed-root sums show that the Borel normalizes the outside-subsystem root group.
Parabolic Weyl transport gives the same normalization by the selected Weyl representatives.
-/

noncomputable section
namespace ReductiveGroups.ReductiveGroupData
open TauCeti
attribute [local irreducible] rootCharacterMap
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

private abbrev borelRoot (c : borelRootCharacterIndex G.borelIdeal G.torusSplit) :
    G.rootIndex := (G.borelCharacterRootEquiv c).val

private theorem borelRoot_char (c : borelRootCharacterIndex G.borelIdeal G.torusSplit) :
    G.rootCharacter (borelRoot G c) = c.val := by
  change (G.characterRootEquiv.symm (G.characterRootEquiv _)).val = c.val
  rw [Equiv.symm_apply_apply]
  rfl

private theorem commutator_radical (I : Set G.rootBase.support)
    (τ : borelRootCharacterIndex G.borelIdeal G.torusSplit)
    (β : G.rootCharacters (parabolicRadicalRoots G.rootBase I)) :
    commutatorRootSet τ β.val ⊆ G.rootCharacters (parabolicRadicalRoots G.rootBase I) := by
  intro γ hγ
  obtain ⟨n, m, _, hm, hrel⟩ := hγ
  have he : G.rootSystem.rootSpanMem ℤ (borelRoot G γ) =
      n • G.rootSystem.rootSpanMem ℤ (borelRoot G τ) +
        m • G.rootSystem.rootSpanMem ℤ (borelRoot G β.val) := by
    have hc (c : borelRootCharacterIndex G.borelIdeal G.torusSplit) :
        G.rootCharacterMap (G.rootSystem.rootSpanMem ℤ (borelRoot G c)) =
          c.val.toAdd :=
      (G.rootCharacterMap_root (borelRoot G c)).trans
        (congrArg Multiplicative.toAdd (borelRoot_char G c))
    have hn := (map_nsmul G.rootCharacterMap n
      (G.rootSystem.rootSpanMem ℤ (borelRoot G τ))).trans
        (congrArg (fun x : G.torusIndex →₀ ℤ => n • x) (hc τ))
    have hm' := (map_nsmul G.rootCharacterMap m
      (G.rootSystem.rootSpanMem ℤ (borelRoot G β.val))).trans
        (congrArg (fun x : G.torusIndex →₀ ℤ => m • x) (hc β.val))
    have hright := (G.rootCharacterMap.map_add
      (n • G.rootSystem.rootSpanMem ℤ (borelRoot G τ))
      (m • G.rootSystem.rootSpanMem ℤ (borelRoot G β.val))).trans
        (congrArg₂ (fun x y : G.torusIndex →₀ ℤ => x + y) hn hm')
    have hleft : γ.val.toAdd = n • τ.val.toAdd + m • β.val.val.toAdd := by
      have h := congrArg Multiplicative.toAdd hrel
      simpa only [toAdd_mul, toAdd_pow] using h
    exact G.rootCharacterMap_injective ((hc γ).trans (hleft.trans hright.symm))
  have hsum := congrArg
    (fun x : G.rootSystem.rootSpan ℤ => (x : Module.Dual K G.cartan)) he
  change G.rootSystem.root (borelRoot G γ) =
    n • G.rootSystem.root (borelRoot G τ) +
      m • G.rootSystem.root (borelRoot G β.val) at hsum
  exact parabolicRadicalRoots_mixed G.rootBase I
    (borelRoot G τ) (borelRoot G β.val) (borelRoot G γ)
    (G.borelCharacterRootEquiv τ).property β.property
    (G.borelCharacterRootEquiv γ).property n m hm hsum

/-- The Borel normalizes the positive-root group outside a Levi subsystem. -/
theorem borel_le_parabolicNormalizer (I : Set G.rootBase.support) :
    G.borelPoints ≤ Subgroup.normalizer (G.rootSubsetPoints
      (parabolicRadicalRoots G.rootBase I) (parabolicRadicalRoots_closed G.rootBase I) :
        Set G.points) := by
  let R := parabolicRadicalRoots G.rootBase I
  let hR := parabolicRadicalRoots_closed G.rootBase I
  let H := Subgroup.normalizer (G.rootSubsetPoints R hR : Set G.points)
  have hU : G.unipotentPoints ≤ H := by
    rw [← G.fullRootPoints_eq_unipotent]
    apply G.rootSubsetPoints_le_of_maps _ _ H
    intro i a
    exact G.rootMap_mem_rootNormalizer R hR i.val (commutator_radical G I i.val) a
  have hT : G.torusPoints ≤ H := G.torusPoints_le_rootNormalizer R hR
  intro b hb
  obtain ⟨t, ht, u, hu, he⟩ := BorelPoint.exists_torus_mul_borelRootUnipotent
    G.torusIdeal G.borelIdeal G.borel_le_torus G.isMaximalTorus G.isBorel
    G.torusSplit G.split_surjective G.split_eq_zero G.reductive b hb
  rw [← he]
  exact H.mul_mem (hT ht) (hU hu)

/-- Parabolic Weyl representatives normalize the positive-root complement of the Levi roots. -/
theorem weyl_mem_parabolicNormalizer (I : Set G.rootBase.support)
    (w : G.weylGroup) (hw : w ∈ standardParabolicSubgroup G.rootBase I) :
    G.weylPoint w ∈ Subgroup.normalizer (G.rootSubsetPoints
      (parabolicRadicalRoots G.rootBase I) (parabolicRadicalRoots_closed G.rootBase I) :
        Set G.points) := by
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
  exact G.rootSubsetPoints_weyl_eq w _ _ _ _ (fun _ hr => hr.1) (fun _ hr => hr.1)
    (parabolicRadicalRoots_weyl G.rootBase I w hw).symm

end ReductiveGroups.ReductiveGroupData
