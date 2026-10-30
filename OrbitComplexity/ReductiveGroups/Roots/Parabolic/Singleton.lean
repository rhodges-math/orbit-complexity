import OrbitComplexity.ReductiveGroups.Roots.Parabolic.LeviRootClosed
import Mathlib.LinearAlgebra.RootSystem.Reduced

/-! # Positive roots of a singleton Levi subsystem -/

namespace ReductiveGroups
variable {ι K M N : Type*} [Field K] [CharZero K]
  [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
  {P : RootPairing ι K M N} [P.IsRootSystem] [P.IsReduced]

/-- A singleton simple subsystem has precisely its selected simple positive root. -/
theorem leviPositiveRoots_singleton (b : P.Base) (i : b.support) :
    leviPositiveRoots b {i} = {i.val} := by
  classical
  let := P.indexNeg
  ext r
  constructor
  · intro hr
    have hp := hr.1
    rw [leviPositiveRoots_eq_span] at hr
    have he : Set.range (fun j : ({i} : Set b.support) => P.root j.val.val) =
        {P.root i.val} := by
      ext x
      simp
    rw [he] at hr
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hr.2
    have hd : ¬ LinearIndependent K ![P.root r, P.root i.val] := by
      simp_rw [LinearIndependent.pair_iff, not_forall]
      exact ⟨1, -a, by simp [← ha], by simp⟩
    rcases RootPairing.IsReduced.eq_or_eq_neg r i.val hd with h | h
    · exact Set.mem_singleton_iff.mpr (P.root.injective h)
    · have hn : r = -i.val := P.root.injective (by simpa using h)
      rw [hn] at hp
      exact False.elim ((RootPairing.Base.IsPos.neg_iff_not b i.val).mp hp
        (b.isPos_of_mem_support i.property))
  · intro hr
    have hri := Set.mem_singleton_iff.mp hr
    subst r
    refine ⟨b.isPos_of_mem_support i.property, AddSubmonoid.subset_closure ?_⟩
    exact ⟨i.val, ⟨i, Set.mem_singleton i, rfl⟩, rfl⟩

end ReductiveGroups
