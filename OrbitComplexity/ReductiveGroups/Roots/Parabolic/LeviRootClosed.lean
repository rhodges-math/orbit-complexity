import OrbitComplexity.ReductiveGroups.Roots.Inversions.ClosedRootTransport
import OrbitComplexity.ReductiveGroups.Roots.Parabolic.LeviRootSpan

/-!
# Integral closure of parabolic positive roots

The positive roots of a parabolic subsystem are precisely the positive roots in
the span of its simple roots. This characterization proves integral root closure.
-/

noncomputable section
namespace ReductiveGroups
variable {ι K M N : Type*} [Field K] [CharZero K]
  [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
  {P : RootPairing ι K M N} [P.IsRootSystem]

/-- Parabolic positive roots are exactly the positive roots in the simple-root span. -/
theorem leviPositiveRoots_eq_span (b : P.Base) (I : Set b.support) :
    leviPositiveRoots b I = {γ | b.IsPos γ ∧ P.root γ ∈
      Submodule.span K (Set.range fun j : I => P.root j.val.val)} := by
  ext γ
  constructor
  · rintro ⟨hpos, hcone⟩
    refine ⟨hpos, ?_⟩
    apply (AddSubmonoid.closure_le.mpr ?_ :
      AddSubmonoid.closure (P.root '' (Subtype.val '' I)) ≤
        (Submodule.span K (Set.range fun j : I => P.root j.val.val)).toAddSubmonoid) hcone
    rintro v ⟨j, ⟨i, hi, rfl⟩, rfl⟩
    exact Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩
  · rintro ⟨hpos, hspan⟩
    by_contra hn
    exact LeviRootSpan.notMem_span_of_notMem_leviPositiveRoots b I hpos hn hspan

/-- Parabolic positive roots form an integrally closed positive-root set. -/
theorem LeviRootSpan.isPositiveRootClosed (b : P.Base) (I : Set b.support) :
    IsPositiveRootClosed b (leviPositiveRoots b I) := by
  rw [leviPositiveRoots_eq_span]
  exact isPositiveRootClosed_submodule b _

end ReductiveGroups
