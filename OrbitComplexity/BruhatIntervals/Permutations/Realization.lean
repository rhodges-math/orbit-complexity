import OrbitComplexity.BruhatIntervals.Permutations.Roots
import OrbitComplexity.BruhatIntervals.Permutations.Generators
import OrbitComplexity.BruhatIntervals.Realizations.Sign

/-!
# The permutation Coxeter system and its coordinate realization

Coordinate permutation realizes the type-A presentation with consecutive coordinate differences
and half the dot product. Faithfulness of the geometric realization proves that the presentation
map to permutations is injective. Together with adjacent-swap generation this constructs the
Coxeter system on the permutation group itself.

## Main definitions

* `TypeA.coordinateAction`: the linear permutation action on real coordinates.
* `TypeA.coxeterSystem`: the type-A Coxeter system on permutations.
* `TypeA.realization`: its realization by consecutive coordinate differences.

## References

* A. Björner and F. Brenti, *Combinatorics of Coxeter Groups*, Springer GTM 231 (2005),
  Sections 1.5 and 4.4.
-/

namespace BruhatIntervals.TypeA

/-- A coordinate permutation acts linearly by pulling back along its inverse. -/
noncomputable def coordinateAction (n : ℕ) :
    Equiv.Perm (Fin (n + 1)) →*
      ((Fin (n + 1) → ℝ) ≃ₗ[ℝ] (Fin (n + 1) → ℝ)) where
  toFun σ :=
    { toFun := fun vector i => vector (σ⁻¹ i)
      invFun := fun vector i => vector (σ i)
      left_inv := by intro vector; ext i; simp
      right_inv := by intro vector; ext i; simp
      map_add' := by intro x y; rfl
      map_smul' := by intro scalar x; rfl }
  map_one' := by ext vector i; rfl
  map_mul' σ τ := by ext vector i; rfl

/-- Coordinate permutation is evaluation at the inverse-permuted index. -/
theorem coordinateAction_apply (n : ℕ) (σ : Equiv.Perm (Fin (n + 1)))
    (vector : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    coordinateAction n σ vector i = vector (σ⁻¹ i) := rfl

/-- An adjacent coordinate swap is reflection in its consecutive coordinate difference. -/
theorem coordinateAction_simple (n : ℕ) (i : Fin n) (vector : Fin (n + 1) → ℝ) :
    coordinateAction n (simpleReflection n i) vector =
      vector - (2 * form n (simpleRoot n i) vector) • simpleRoot n i := by
  have hne : i.castSucc ≠ i.succ := by
    intro h
    have hval := congrArg Fin.val h
    simp only [Fin.val_castSucc, Fin.val_succ] at hval
    omega
  have hscalar : 2 * ((1 / 2 : ℝ) * (vector i.castSucc - vector i.succ)) =
      vector i.castSucc - vector i.succ := by ring
  ext k
  rw [coordinateAction_apply, form_simpleRoot_left, hscalar]
  change vector ((Equiv.swap i.castSucc i.succ)⁻¹ k) =
    vector k - (vector i.castSucc - vector i.succ) * simpleRoot n i k
  rw [Equiv.swap_inv]
  by_cases hkfirst : k = i.castSucc
  · subst k
    simp only [Equiv.swap_apply_left, simpleRoot, Pi.sub_apply,
      Pi.single_eq_same, Pi.single_eq_of_ne hne, sub_zero]
    ring
  by_cases hklast : k = i.succ
  · subst k
    simp only [Equiv.swap_apply_right, simpleRoot, Pi.sub_apply,
      Pi.single_eq_same, Pi.single_eq_of_ne hne.symm, zero_sub]
    ring
  · rw [Equiv.swap_apply_of_ne_of_ne hkfirst hklast]
    simp only [simpleRoot, Pi.sub_apply, Pi.single_eq_of_ne hkfirst,
      Pi.single_eq_of_ne hklast, sub_self, mul_zero, sub_zero]

/-- Half the dot product has the cosine Gram entries of the type-A Coxeter matrix. -/
theorem form_simpleRoot (n : ℕ) (i j : Fin n) :
    form n (simpleRoot n i) (simpleRoot n j) =
      -Real.cos (Real.pi / ((CoxeterMatrix.A n) i j : ℝ)) := by
  rw [form_simpleRoot_left]
  simp only [simpleRoot, Pi.sub_apply, Pi.single_apply, Fin.ext_iff,
    Fin.val_castSucc, Fin.val_succ, CoxeterMatrix.A, Matrix.of_apply]
  split_ifs <;> norm_num [Real.cos_pi, Real.cos_pi_div_two, Real.cos_pi_div_three] at *
  all_goals omega

private noncomputable def presentationRealization (n : ℕ) :
    Realization (CoxeterMatrix.A n).toCoxeterSystem (V := Fin (n + 1) → ℝ) where
  simpleRoot := simpleRoot n
  root_independent := simpleRoot_linearIndependent n
  form := form n
  form_isSymm := form_isSymm n
  form_root := form_simpleRoot n
  action := (coordinateAction n).comp (permutationLift n)
  action_simple := by
    intro i vector
    change coordinateAction n (permutationLift n
      ((CoxeterMatrix.A n).toCoxeterSystem.simple i)) vector = _
    rw [permutationLift_simple]
    exact coordinateAction_simple n i vector

/-- The type-A presentation map to permutations is injective by geometric faithfulness. -/
theorem permutationLift_injective (n : ℕ) : Function.Injective (permutationLift n) := by
  intro x y heq
  apply (presentationRealization n).action_injective
  change coordinateAction n (permutationLift n x) = coordinateAction n (permutationLift n y)
  rw [heq]

/-- Adjacent transpositions give the permutation group its type-A Coxeter system. -/
noncomputable def coxeterSystem (n : ℕ) :
    CoxeterSystem (CoxeterMatrix.A n) (Equiv.Perm (Fin (n + 1))) :=
  (CoxeterMatrix.A n).toCoxeterSystem.map (MulEquiv.ofBijective (permutationLift n)
    ⟨permutationLift_injective n, permutationLift_surjective n⟩)

/-- The simple generators of the permutation Coxeter system are its adjacent transpositions. -/
theorem coxeterSystem_simple (n : ℕ) (i : Fin n) :
    (coxeterSystem n).simple i = simpleReflection n i := by
  rw [coxeterSystem, CoxeterSystem.map_simple]
  exact permutationLift_simple n i

/-- The permutation Coxeter system has consecutive coordinate differences as its unit roots. -/
noncomputable def realization (n : ℕ) :
    Realization (coxeterSystem n) (V := Fin (n + 1) → ℝ) where
  simpleRoot := simpleRoot n
  root_independent := simpleRoot_linearIndependent n
  form := form n
  form_isSymm := form_isSymm n
  form_root := form_simpleRoot n
  action := coordinateAction n
  action_simple := by
    intro i vector
    rw [coxeterSystem_simple]
    exact coordinateAction_simple n i vector

end BruhatIntervals.TypeA
