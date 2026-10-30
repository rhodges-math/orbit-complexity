import OrbitComplexity.BruhatIntervals.Realizations.Form
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Pi
import Mathlib.Order.Interval.Finset.Fin

/-!
# Simple roots for permutations

The consecutive coordinate differences in real coordinate space form an independent family.
Prefix sums give their dual coordinates. Half the dot product makes these simple roots unit
vectors with the type-A Gram matrix.

## Main definitions

* `TypeA.simpleRoot`: a consecutive coordinate difference.
* `TypeA.rootCoordinates`: the prefix-sum coordinate map.
* `TypeA.form`: half the coordinate dot product.

## References

* A. Björner and F. Brenti, *Combinatorics of Coxeter Groups*, Springer GTM 231 (2005),
  Sections 1.5 and 4.4.
-/

namespace BruhatIntervals.TypeA

/-- The consecutive coordinate difference indexed by a simple type-A root. -/
def simpleRoot (n : ℕ) (i : Fin n) : Fin (n + 1) → ℝ :=
  Pi.single i.castSucc 1 - Pi.single i.succ 1

/-- Prefix sums give the coordinates dual to the consecutive coordinate differences. -/
noncomputable def rootCoordinates (n : ℕ) : (Fin (n + 1) → ℝ) →ₗ[ℝ] (Fin n → ℝ) where
  toFun vector i := ∑ j ∈ Finset.Iic i.castSucc, vector j
  map_add' x y := by
    ext i
    simp only [Pi.add_apply, Finset.sum_add_distrib]
  map_smul' scalar x := by
    ext i
    simp only [Pi.smul_apply, Finset.smul_sum, RingHom.id_apply]

/-- Prefix coordinates send each consecutive difference to its coordinate unit vector. -/
theorem rootCoordinates_simpleRoot (n : ℕ) (j : Fin n) :
    rootCoordinates n (simpleRoot n j) = Pi.single j 1 := by
  ext i
  change (∑ k ∈ Finset.Iic i.castSucc, simpleRoot n j k) =
    (Pi.single j 1 : Fin n → ℝ) i
  simp only [simpleRoot, Pi.sub_apply, Finset.sum_sub_distrib,
    Finset.sum_pi_single', Finset.mem_Iic]
  by_cases hji : j = i
  · subst j
    simp
  · have hval : j.val ≠ i.val := fun h => hji (Fin.ext h)
    by_cases hjlt : j.val < i.val
    · have hcast : j.castSucc ≤ i.castSucc := by simpa using Nat.le_of_lt hjlt
      have hsucc : j.succ ≤ i.castSucc := by simpa using hjlt
      simp only [ite_eq_left hcast, ite_eq_left hsucc, sub_self,
        Pi.single_eq_of_ne (Ne.symm hji)]
    · have hcast : ¬j.castSucc ≤ i.castSucc := by simpa using (by omega : ¬j.val ≤ i.val)
      have hsucc : ¬j.succ ≤ i.castSucc := by simpa using (by omega : ¬j.val + 1 ≤ i.val)
      simp only [ite_eq_right hcast, ite_eq_right hsucc, sub_self,
        Pi.single_eq_of_ne (Ne.symm hji)]

/-- Consecutive coordinate differences are linearly independent. -/
theorem simpleRoot_linearIndependent (n : ℕ) : LinearIndependent ℝ (simpleRoot n) := by
  apply LinearIndependent.of_comp (rootCoordinates n)
  have hfun : rootCoordinates n ∘ simpleRoot n = (Pi.basisFun ℝ (Fin n) : Fin n → _) := by
    funext i
    rw [Function.comp_apply, rootCoordinates_simpleRoot, Pi.basisFun_apply]
  rw [hfun]
  exact (Pi.basisFun ℝ (Fin n)).linearIndependent

/-- Half the standard coordinate dot product gives unit simple roots of type A. -/
noncomputable def form (n : ℕ) : LinearMap.BilinForm ℝ (Fin (n + 1) → ℝ) :=
  (1 / 2 : ℝ) • Matrix.toBilin' (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)

/-- The type-A form is half the coordinate dot product. -/
theorem form_apply (n : ℕ) (x y : Fin (n + 1) → ℝ) :
    form n x y = (1 / 2 : ℝ) * ∑ i, x i * y i := by
  change (1 / 2 : ℝ) * Matrix.toBilin' (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) x y = _
  rw [Matrix.toBilin'_apply', Matrix.one_mulVec]
  rfl

/-- The type-A form is symmetric. -/
theorem form_isSymm (n : ℕ) : (form n).IsSymm := by
  constructor
  intro x y
  rw [form_apply, form_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

/-- Pairing a simple root with a vector takes half its adjacent coordinate difference. -/
theorem form_simpleRoot_left (n : ℕ) (i : Fin n) (x : Fin (n + 1) → ℝ) :
    form n (simpleRoot n i) x = (1 / 2 : ℝ) * (x i.castSucc - x i.succ) := by
  rw [form_apply]
  change (1 / 2 : ℝ) * ((Pi.single i.castSucc 1 - Pi.single i.succ 1) ⬝ᵥ x) = _
  rw [sub_dotProduct, single_dotProduct, single_dotProduct, one_mul, one_mul]

end BruhatIntervals.TypeA
