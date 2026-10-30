import Batteries.Tactic.Lint
import OrbitComplexity.BruhatIntervals.Order.Covers
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupRootData
import OrbitComplexity.ReductiveGroups.Roots.Coxeter.PresentationWordPropertyLength
import TauCeti.LinearAlgebra.RootSystem.Weyl.Group

/-!
# Positive roots of intrinsic Bruhat covers

-/

noncomputable section

namespace SchubertGeometry

open ReductiveGroups

section RootPairing

variable {ι R M N : Type*} [CommRing R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing ι R M N} [Finite ι] [IsDomain R]
    [P.IsCrystallographic] [P.IsReduced]

private theorem positiveRoot_exchange (b : P.Base) (l : List b.support)
    (i : ι) (hi : b.IsPos i)
    (hneg : ¬ b.IsPos (P.weylGroupToPerm (simpleWeylWord b l) i)) :
    ∃ m : List b.support,
      simpleWeylWord b m = simpleWeylWord b l * RootPairing.weylGroup.ofIdx P i ∧
      m.length + 1 = l.length := by
  induction l with
  | nil => exact (hneg (by simpa [simpleWeylWord] using hi)).elim
  | cons j l ih =>
    by_cases hpos : b.IsPos (P.weylGroupToPerm (simpleWeylWord b l) i)
    · have he : P.weylGroupToPerm (simpleWeylWord b l) i = (j : ι) := by
        by_contra hne
        have hp := hpos.reflectionPerm j.property hne
        apply hneg
        simpa only [simpleWeylWord, map_mul, Equiv.Perm.mul_apply,
          weylGroupToPerm_simple] using hp
      refine ⟨l, ?_, by simp⟩
      have hintertwine := simpleWeylWord_mul_reflection b l i
      rw [he] at hintertwine
      have hcalc : simpleWeylWord b (j :: l) * RootPairing.weylGroup.ofIdx P i =
          simpleWeylWord b l := by
        simpa only [simpleWeylWord, mul_assoc, weylGroup_ofIdx_mul_cancel_left] using
          congrArg (fun w => RootPairing.weylGroup.ofIdx P j * w) hintertwine
      exact hcalc.symm
    · obtain ⟨m, hm, hlen⟩ := ih hpos
      refine ⟨j :: m, ?_, by simp only [List.length_cons]; omega⟩
      simp only [simpleWeylWord, hm, mul_assoc]

private theorem negative_reflection_length (b : P.Base) (w : P.weylGroup)
    (i : ι) (hi : b.IsPos i) (hneg : ¬ b.IsPos (P.weylGroupToPerm w i)) :
    (weylCoxeterSystem b).length (w * RootPairing.weylGroup.ofIdx P i) <
      (weylCoxeterSystem b).length w := by
  obtain ⟨l, hl, hlen⟩ := InversionLength.exists_of_inversionCount_length b w
  obtain ⟨m, hm, hml⟩ := positiveRoot_exchange b l i hi (by rw [hl]; exact hneg)
  have hle := (weylCoxeterSystem b).length_wordProd_le m
  rw [weylCoxeterSystem_wordProd, hm, hl] at hle
  have hlen' : l.length = (weylCoxeterSystem b).length w :=
    hlen.trans (weylCoxeterSystem_length b w).symm
  omega

private theorem positive_reflection (b : P.Base) {t : P.weylGroup}
    (ht : (weylCoxeterSystem b).IsReflection t) :
    ∃ β : ι, b.IsPos β ∧ t = RootPairing.weylGroup.ofIdx P β := by
  classical
  obtain ⟨w, i, ht⟩ := ht
  have hRoot : t = RootPairing.weylGroup.ofIdx P (P.weylGroupToPerm w i.val) := by
    rw [ht, weylCoxeterSystem_simple]
    exact (RootPairing.weylGroup.ofIdx_weylGroupToPerm_eq_conj P w i.val).symm
  by_cases hpos : b.IsPos (P.weylGroupToPerm w i.val)
  · exact ⟨P.weylGroupToPerm w i.val, hpos, hRoot⟩
  · refine ⟨P.reflectionPerm (P.weylGroupToPerm w i.val)
      (P.weylGroupToPerm w i.val), (isPos_neg_index_iff b _).mpr hpos, ?_⟩
    exact hRoot.trans (weylGroup_ofIdx_neg_index _).symm

private theorem cover_root (b : P.Base) (x y : P.weylGroup) :
    let : PartialOrder P.weylGroup := (weylCoxeterSystem b).bruhatPartialOrder
    x ⋖ y → ∃ β : ι, b.IsPos β ∧ y = RootPairing.weylGroup.ofIdx P β * x ∧
      b.IsPos (P.weylGroupToPerm x⁻¹ β) := by
  classical
  let : PartialOrder P.weylGroup := (weylCoxeterSystem b).bruhatPartialOrder
  dsimp only
  intro hCover
  obtain ⟨t, ht, hxy, hlt⟩ := BruhatIntervals.bruhat_covBy_step
    (weylCoxeterSystem b) hCover
  obtain ⟨β, hβ, htβ⟩ := positive_reflection b ht
  have hy : y = RootPairing.weylGroup.ofIdx P β * x := by
    rw [htβ] at hxy
    exact hxy
  refine ⟨β, hβ, hy, ?_⟩
  by_contra hneg
  have hdrop := negative_reflection_length b x⁻¹ β hβ hneg
  have he : x⁻¹ * RootPairing.weylGroup.ofIdx P β = y⁻¹ := by
    rw [hy, mul_inv_rev, RootPairing.weylGroup.ofIdx_inv_eq]
  rw [he, (weylCoxeterSystem b).length_inv, (weylCoxeterSystem b).length_inv] at hdrop
  exact (Nat.lt_asymm hlt hdrop)

end RootPairing

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroups.ReductiveGroupData K)

/-- An intrinsic Bruhat cover is left multiplication by a positive root
reflection whose root remains positive after applying the lower endpoint's inverse. -/
theorem bruhatCover_root (x y : G.weylGroup) :
    let : PartialOrder G.weylGroup := (ReductiveGroups.weylCoxeterSystem
      G.rootBase).bruhatPartialOrder
    x ⋖ y → ∃ β : G.rootIndex, G.rootBase.IsPos β ∧
      y = RootPairing.weylGroup.ofIdx G.rootSystem β * x ∧
      G.rootBase.IsPos (G.rootSystem.weylGroupToPerm x⁻¹ β) :=
  cover_root G.rootBase x y

end SchubertGeometry
