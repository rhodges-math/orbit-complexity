import OrbitComplexity.BruhatIntervals.Order.Basic
import Mathlib.GroupTheory.Perm.Sign

/-!
# Adjacent permutation generators

Adjacent transpositions satisfy the type-A Coxeter relations and generate the full permutation
group. They therefore give a surjective homomorphism from the presented type-A Coxeter group.

## Main definitions

* `TypeA.simpleReflection`: an adjacent coordinate transposition.
* `TypeA.permutationLift`: the homomorphism from the type-A Coxeter presentation.

## Main results

* `TypeA.simpleReflection_relation`: the adjacent transpositions satisfy the presentation.
* `TypeA.permutationLift_surjective`: every permutation is in the image of the presentation.

## References

* A. Björner and F. Brenti, *Combinatorics of Coxeter Groups*, Springer GTM 231 (2005),
  Section 1.5.
-/

namespace BruhatIntervals.TypeA

/-- The simple reflection of type A is the adjacent coordinate transposition. -/
def simpleReflection (n : ℕ) (i : Fin n) : Equiv.Perm (Fin (n + 1)) :=
  Equiv.swap i.castSucc i.succ

private theorem swap_cube {α : Type*} [DecidableEq α] (a b c : α)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    ((Equiv.swap a b) * Equiv.swap b c) ^ 3 = 1 := by
  ext k
  by_cases hka : k = a
  · subst k
    simp_all [pow_succ, Equiv.Perm.mul_apply, Equiv.swap_apply_def, eq_comm]
  by_cases hkb : k = b
  · subst k
    simp_all [pow_succ, Equiv.Perm.mul_apply, Equiv.swap_apply_def, eq_comm]
  by_cases hkc : k = c
  · subst k
    simp_all [pow_succ, Equiv.Perm.mul_apply, Equiv.swap_apply_def, eq_comm]
  simp_all [pow_succ, Equiv.Perm.mul_apply, Equiv.swap_apply_def, eq_comm]

private theorem swap_square {α : Type*} [DecidableEq α] (a b c d : α)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    ((Equiv.swap a b) * Equiv.swap c d) ^ 2 = 1 := by
  ext k
  by_cases hka : k = a
  · subst k
    simp_all [pow_succ, Equiv.Perm.mul_apply, Equiv.swap_apply_def]
  by_cases hkb : k = b
  · subst k
    simp_all [pow_succ, Equiv.Perm.mul_apply, Equiv.swap_apply_def, eq_comm]
  by_cases hkc : k = c
  · subst k
    simp_all [pow_succ, Equiv.Perm.mul_apply, Equiv.swap_apply_def, eq_comm]
  by_cases hkd : k = d
  · subst k
    simp_all [pow_succ, Equiv.Perm.mul_apply, Equiv.swap_apply_def, eq_comm]
  simp_all [pow_succ, Equiv.Perm.mul_apply, Equiv.swap_apply_def, eq_comm]

/-- Adjacent coordinate transpositions satisfy every type-A Coxeter relation. -/
theorem simpleReflection_relation (n : ℕ) :
    (CoxeterMatrix.A n).IsLiftable (simpleReflection n) := by
  intro i j
  change (simpleReflection n i * simpleReflection n j) ^
    (if i = j then 1 else if j.val + 1 = i.val ∨ i.val + 1 = j.val then 3 else 2) = 1
  by_cases heq : i = j
  · subst j
    simp only [↓reduceIte, pow_one, simpleReflection, Equiv.swap_mul_self]
  rw [ite_eq_right heq]
  by_cases hadj : j.val + 1 = i.val ∨ i.val + 1 = j.val
  · rw [ite_eq_left hadj]
    rcases hadj with hji | hij
    · have hshared : j.succ = i.castSucc := Fin.ext hji
      change ((Equiv.swap i.castSucc i.succ) * Equiv.swap j.castSucc j.succ) ^ 3 = 1
      rw [← hshared, Equiv.swap_comm j.succ i.succ, Equiv.swap_comm j.castSucc j.succ]
      apply swap_cube
      all_goals
        intro h
        have hval := congrArg Fin.val h
        simp only [Fin.val_succ, Fin.val_castSucc] at hval
        omega
    · have hshared : i.succ = j.castSucc := Fin.ext hij
      change ((Equiv.swap i.castSucc i.succ) * Equiv.swap j.castSucc j.succ) ^ 3 = 1
      rw [← hshared]
      apply swap_cube
      all_goals
        intro h
        have hval := congrArg Fin.val h
        simp only [Fin.val_succ, Fin.val_castSucc] at hval
        omega
  · rw [ite_eq_right hadj]
    have hne : i.val ≠ j.val := fun h => heq (Fin.ext h)
    have hji : j.val + 1 ≠ i.val := fun h => hadj (Or.inl h)
    have hij : i.val + 1 ≠ j.val := fun h => hadj (Or.inr h)
    change ((Equiv.swap i.castSucc i.succ) * Equiv.swap j.castSucc j.succ) ^ 2 = 1
    apply swap_square
    all_goals
      intro h
      have hval := congrArg Fin.val h
      simp only [Fin.val_succ, Fin.val_castSucc] at hval
      omega

/-- The adjacent generators induce a homomorphism from the type-A Coxeter presentation. -/
noncomputable def permutationLift (n : ℕ) :
    (CoxeterMatrix.A n).Group →* Equiv.Perm (Fin (n + 1)) :=
  (CoxeterMatrix.A n).toCoxeterSystem.lift ⟨simpleReflection n, simpleReflection_relation n⟩

/-- The presentation homomorphism sends each simple generator to its adjacent transposition. -/
theorem permutationLift_simple (n : ℕ) (i : Fin n) :
    permutationLift n ((CoxeterMatrix.A n).toCoxeterSystem.simple i) = simpleReflection n i :=
  (CoxeterMatrix.A n).toCoxeterSystem.lift_apply_simple (simpleReflection_relation n) i

/-- Adjacent transpositions generate every permutation, so the presentation map is surjective. -/
theorem permutationLift_surjective (n : ℕ) : Function.Surjective (permutationLift n) := by
  apply MonoidHom.range_eq_top.mp
  have hclosure : Subgroup.closure (Set.range (simpleReflection n)) = ⊤ :=
    Subgroup.closure_eq_top_of_mclosure_eq_top (Equiv.Perm.mclosure_swap_castSucc_succ n)
  apply top_unique
  rw [← hclosure]
  apply (Subgroup.closure_le _).mpr
  rintro σ ⟨i, rfl⟩
  exact ⟨(CoxeterMatrix.A n).toCoxeterSystem.simple i, permutationLift_simple n i⟩

end BruhatIntervals.TypeA
