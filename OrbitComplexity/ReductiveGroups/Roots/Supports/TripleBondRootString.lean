import OrbitComplexity.ReductiveGroups.Roots.Supports.TripleBondPositiveRoots

/-!
# Triple Bond Root String

Positive root indices along the short-simple-root string
through the long simple root of a triple bond. -/

noncomputable section
namespace ReductiveGroups

variable {ι R M N : Type*} [CommRing R] [CharZero R] [IsDomain R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [Finite ι] [P.IsCrystallographic] [P.IsReduced]

/-- The equality is

```lean
∃ γ₁ γ₂ γ₃ : ι,
      b.IsPos γ₁ ∧ b.IsPos γ₂ ∧ b.IsPos γ₃ ∧
      P.root γ₁ = P.root (p : ι) + P.root (q : ι) ∧
      P.root γ₂ = P.root γ₁ + P.root (q : ι) ∧
      P.root γ₃ = P.root γ₂ + P.root (q : ι) ∧
      P.root γ₃ = P.root (p : ι) + (3 : ℤ) • P.root (q : ι)
```
-/
theorem tripleBond_positive_root_string (b : P.Base) (p q : b.support)
    (hpq : P.pairingIn ℤ (p : ι) (q : ι) = -3)
    (hqp : P.pairingIn ℤ (q : ι) (p : ι) = -1) :
    ∃ γ₁ γ₂ γ₃ : ι,
      b.IsPos γ₁ ∧ b.IsPos γ₂ ∧ b.IsPos γ₃ ∧
      P.root γ₁ = P.root (p : ι) + P.root (q : ι) ∧
      P.root γ₂ = P.root γ₁ + P.root (q : ι) ∧
      P.root γ₃ = P.root γ₂ + P.root (q : ι) ∧
      P.root γ₃ = P.root (p : ι) + (3 : ℤ) • P.root (q : ι) := by
  have hpqne : (p : ι) ≠ (q : ι) := by
    intro h
    rw [h, P.pairingIn_same] at hpq
    omega
  let γ₁ : ι := P.reflectionPerm (p : ι) (q : ι)
  let γ₂ : ι := P.reflectionPerm (q : ι) γ₁
  let γ₃ : ι := P.reflectionPerm (q : ι) (p : ι)
  have hγ₁ : P.root γ₁ = P.root (p : ι) + P.root (q : ι) := by
    dsimp [γ₁]
    rw [P.root_reflectionPerm, P.reflection_apply_root' ℤ, hqp]
    simp [add_comm]
  have h₁pos : b.IsPos γ₁ :=
    (b.isPos_of_mem_support q.property).reflectionPerm p.property hpqne.symm
  have hpair : P.pairingIn ℤ γ₁ (q : ι) = -1 := by
    have hspan : P.rootSpanMem ℤ γ₁ =
        P.rootSpanMem ℤ (p : ι) + P.rootSpanMem ℤ (q : ι) := by
      apply Subtype.ext
      exact hγ₁
    have hh := congrArg (P.coroot'In ℤ (q : ι)) hspan
    simp only [map_add, RootPairing.coroot'In_rootSpanMem_eq_pairingIn,
      hpq, P.pairingIn_same] at hh
    exact hh
  have hγ₂ : P.root γ₂ = P.root γ₁ + P.root (q : ι) := by
    dsimp [γ₂]
    rw [P.root_reflectionPerm, P.reflection_apply_root' ℤ, hpair]
    simp
  have h₂pos : b.IsPos γ₂ := h₁pos.add (b.isPos_of_mem_support q.property) hγ₂
  have hγ₃ : P.root γ₃ = P.root (p : ι) + (3 : ℤ) • P.root (q : ι) := by
    dsimp [γ₃]
    rw [P.root_reflectionPerm, P.reflection_apply_root' ℤ, hpq]
    simp
  have h₃pos : b.IsPos γ₃ :=
    (b.isPos_of_mem_support p.property).reflectionPerm q.property hpqne
  refine ⟨γ₁, γ₂, γ₃, h₁pos, h₂pos, h₃pos, hγ₁, hγ₂, ?_, hγ₃⟩
  rw [hγ₃, hγ₂, hγ₁]
  module

end ReductiveGroups
