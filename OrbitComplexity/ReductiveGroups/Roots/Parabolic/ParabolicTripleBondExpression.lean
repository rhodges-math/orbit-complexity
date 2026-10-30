import OrbitComplexity.ReductiveGroups.Roots.Supports.TripleBondExpression
import OrbitComplexity.ReductiveGroups.Roots.Supports.TripleBondRootString
import OrbitComplexity.ReductiveGroups.Roots.Parabolic.ParabolicAuxiliaryRoots

/-!
# Parabolic Triple Bond Expression

The parabolic auxiliary-root specialization of the G2 expression. -/

noncomputable section
namespace ReductiveGroups
attribute [local instance] Classical.decEq

variable {ι R M N : Type*} [CommRing R] [CharZero R] [IsDomain R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [Finite ι] [P.IsCrystallographic] [P.IsReduced]

private theorem tripleBond_positive_root_at (b : P.Base) (p q : b.support)
    (hpq : P.pairingIn ℤ (p : ι) (q : ι) = -3)
    (hqp : P.pairingIn ℤ (q : ι) (p : ι) = -1)
    (k : ℕ) (hk : k ≤ 3) :
    ∃ γ : ι, b.IsPos γ ∧
      P.root γ = P.root (p : ι) + (k : ℤ) • P.root (q : ι) := by
  obtain ⟨γ₁, γ₂, γ₃, h₁pos, h₂pos, h₃pos,
    h₁, h₂, h₃, h₃root⟩ := tripleBond_positive_root_string b p q hpq hqp
  have hcases : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
  rcases hcases with h | h | h | h
  · subst k
    exact ⟨(p : ι), b.isPos_of_mem_support p.property, by simp⟩
  · subst k
    refine ⟨γ₁, h₁pos, ?_⟩
    simpa using h₁
  · subst k
    refine ⟨γ₂, h₂pos, ?_⟩
    rw [h₂, h₁]
    module
  · subst k
    exact ⟨γ₃, h₃pos, by simpa using h₃root⟩

/-- For the original parabolic auxiliary set and a minimal left
representative, an admissible G2 expression has one auxiliary root and
one to three copies of the short distinguished inversion. Every
intermediate point of its root string is a positive root index.
This is the root-index statement preceding any Lie-bracket argument. -/
theorem ParabolicTripleBondExpression.root_expression_shape
    (b : P.Base) (J : Set b.support) (a : P.weylGroup)
    (ha : a ∈ standardParabolicSubgroup b J)
    (word : List b.support) (hword : word.Nodup)
    (hd : IsMinimalLeftParabolic b J (simpleWeylWord b word))
    (D : Set ι)
    (hD : D ⊆ leftRootInversionIndices b (simpleWeylWord b word))
    (β : ι)
    (hβ : β ∈ leftRootInversionIndices b (simpleWeylWord b word))
    (hβD : β ∉ D)
    (p q : b.support)
    (hp : p ∈ simpleRootSupportInt b β)
    (hq : q ∈ simpleRootSupportInt b β)
    (hpq : P.pairingIn ℤ (p : ι) (q : ι) = -3)
    (hqp : P.pairingIn ℤ (q : ι) (p : ι) = -1)
    (hbad : ¬ ∀ k : b.support,
      simpleRootCoeffInt b β k = 0 ∨ simpleRootCoeffInt b β k = 1)
    (s : Multiset ι)
    (hs : RootExpression P (parabolicAuxiliaryRootIndices b J a) D β s) :
    ∃ (τ : ι) (m : ℕ),
      τ ∈ parabolicAuxiliaryRootIndices b J a ∧
      (q : ι) ∈ D ∧ 1 ≤ m ∧ m ≤ 3 ∧
      s = {τ} + Multiset.replicate m (q : ι) ∧
      simpleRootCoeffInt b τ p = 1 ∧
      simpleRootCoeffInt b τ q = 3 - m ∧
      P.root β = P.root τ + (m : ℤ) • P.root (q : ι) ∧
      (∀ j : ℕ, j ≤ m → ∃ γ : ι, b.IsPos γ ∧
        P.root γ = P.root τ + (j : ℤ) • P.root (q : ι)) := by
  have hApos : ∀ γ ∈ parabolicAuxiliaryRootIndices b J a, b.IsPos γ :=
    fun γ hγ => parabolicAuxiliaryRootIndices_positive b J a hγ
  have hAD := ParabolicAuxiliaryRootIndices.disjoint_inversions
    b J a (simpleWeylWord b word) ha hd
  obtain ⟨τ, m, hτA, hqD, hmpos, hmle, hsform, hτp, hτq⟩ :=
    tripleBond_rootExpression_shape b word hword β hβ p q hp hq hpq hqp
      hbad (parabolicAuxiliaryRootIndices b J a) D hAD hApos hD hβD s hs
  have hβsum : P.root β = P.root τ + (m : ℤ) • P.root (q : ι) := by
    have hsum := hs.2
    rw [hsform] at hsum
    simp only [Multiset.map_add, Multiset.sum_add, Multiset.map_singleton,
      Multiset.sum_singleton, Multiset.map_replicate,
      Multiset.sum_replicate] at hsum
    simpa only [natCast_zsmul] using hsum.symm
  have hβroot :=
    (leftRootInversion_triple_bond_shape b word hword β
      ⟨β, hβ, rfl⟩ p q hp hq hpq hqp hbad).2
  have hbalance : P.root τ + (m : ℤ) • P.root (q : ι) =
      P.root (p : ι) + (3 : ℤ) • P.root (q : ι) :=
    hβsum.symm.trans hβroot
  have hτroot : P.root τ = P.root (p : ι) +
      ((3 : ℤ) - (m : ℤ)) • P.root (q : ι) := by
    calc
      P.root τ = (P.root τ + (m : ℤ) • P.root (q : ι)) -
          (m : ℤ) • P.root (q : ι) := by abel
      _ = (P.root (p : ι) + (3 : ℤ) • P.root (q : ι)) -
          (m : ℤ) • P.root (q : ι) := congrArg
            (fun x => x - (m : ℤ) • P.root (q : ι)) hbalance
      _ = P.root (p : ι) + ((3 : ℤ) - (m : ℤ)) • P.root (q : ι) := by
        rw [sub_smul]
        abel
  refine ⟨τ, m, hτA, hqD, hmpos, hmle, hsform, hτp, hτq,
    hβsum, ?_⟩
  intro j hj
  let k : ℕ := 3 - m + j
  have hk : k ≤ 3 := by dsimp [k]; omega
  have hkcast : (k : ℤ) = (3 : ℤ) - (m : ℤ) + (j : ℤ) := by
    dsimp [k]
    omega
  obtain ⟨γ, hγpos, hγroot⟩ := tripleBond_positive_root_at b p q hpq hqp k hk
  refine ⟨γ, hγpos, ?_⟩
  rw [hγroot, hτroot, hkcast]
  module

end ReductiveGroups
