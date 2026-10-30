import Mathlib.LinearAlgebra.RootSystem.BaseExists

/-!
# Closed Root Functional Base

Constructing a root-system base from a rational functional that is
positive on a prescribed set of roots. -/

noncomputable section
namespace ReductiveGroups

open RootPairing Set IsAddIndecomposable

universe u v w₁ w₂
variable {ι : Type u} {R : Type v} {M : Type w₁} {N : Type w₂}
  [Finite ι] [AddCommGroup M] [AddCommGroup N]
  [Field R] [CharZero R] [Module R M] [Module R N]
  (P : RootPairing ι R M N) [P.IsRootSystem] [P.IsCrystallographic] [P.IsReduced]

/-- A regular rational form that is positive on a chosen root subset
constructs a base whose positive cone contains that subset. -/
theorem ClosedRootFunctionalBase.exists_roots_of_regular_positive_form
    (s : Set ι) (f : M →+ ℚ)
    (hf : ∀ i, f (P.root i) ≠ 0)
    (hs : ∀ i ∈ s, 0 < f (P.root i)) :
    ∃ b : P.Base, ∀ i ∈ s,
      P.root i ∈ AddSubmonoid.closure (P.root '' (b.support : Set ι)) := by
  let _i := P.indexNeg
  let t := IsAddIndecomposable.baseOf P.root f
  let b : P.Base := RootPairing.Base.mk' P t (P.linearIndepOn_root_baseOf f hf)
    (fun i => mem_or_neg_mem_closure_baseOf P.root f i (hf i) (by simp))
  refine ⟨b, ?_⟩
  intro i hi
  have himem : P.root i ∈ AddSubmonoid.closure (P.root '' {j | 0 < f (P.root j)}) :=
    AddSubmonoid.subset_closure (⟨i, hs i hi, rfl⟩)
  have hclosure : AddSubmonoid.closure (P.root '' t) =
      AddSubmonoid.closure (P.root '' {j | 0 < f (P.root j)}) := by
    exact AddSubmonoid.closure_image_isAddIndecomposable_baseOf P.root f
  have hsupp : (b.support : Set ι) = t := by
    simp [b, RootPairing.Base.mk', t]
  rw [hsupp]
  rw [hclosure]
  exact himem

end ReductiveGroups
