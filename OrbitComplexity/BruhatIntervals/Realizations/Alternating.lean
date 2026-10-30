import OrbitComplexity.BruhatIntervals.Realizations.Roots

/-!
# Alternating words acting on simple roots

The action of an alternating word on a simple root is expressed using rescaled Chebyshev
polynomials. Below the finite Coxeter exponent, and for every length at infinite exponent, the
coefficients of both simple roots are nonnegative.

## Main results

* `Realization.alternatingRoot_even`: the coefficients for an alternating word of even length.
* `Realization.alternatingRoot_odd`: the coefficients for an alternating word of odd length.
* `Realization.alternatingRoot_nonneg`: both coefficients are nonnegative below the exponent.

## Implementation notes

Finite exponents use the sine evaluation of the Chebyshev polynomials, including the boundary
where a coefficient vanishes. Exponent zero uses their evaluation at two.

## References

* A. Björner and F. Brenti, *Combinatorics of Coxeter Groups*, Springer GTM 231 (2005),
  Lemma 4.2.4.
-/

namespace BruhatIntervals

open Polynomial.Chebyshev

private theorem chebyshev_s_nonneg (m : ℕ) (k : ℤ) (hm : 3 ≤ m)
    (hk : 0 ≤ k + 1) (hkm : 2 * (k + 1) ≤ (m : ℤ)) :
    0 ≤ (S ℝ k).eval (2 * Real.cos (2 * Real.pi / (m : ℝ))) := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hm3 : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hθpos : 0 < 2 * Real.pi / (m : ℝ) := div_pos (by positivity) hmpos
  have hθlt : 2 * Real.pi / (m : ℝ) < Real.pi := by
    apply (div_lt_iff₀ hmpos).mpr
    nlinarith [Real.pi_pos]
  have hsinpos := Real.sin_pos_of_pos_of_lt_pi hθpos hθlt
  have hkreal : (0 : ℝ) ≤ (k : ℝ) + 1 := by exact_mod_cast hk
  have hkmreal : 2 * ((k : ℝ) + 1) ≤ (m : ℝ) := by exact_mod_cast hkm
  have hangle0 : 0 ≤ ((k : ℝ) + 1) * (2 * Real.pi / (m : ℝ)) := by positivity
  have hanglepi : ((k : ℝ) + 1) * (2 * Real.pi / (m : ℝ)) ≤ Real.pi := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hmpos).mpr
    nlinarith [Real.pi_pos]
  have heval := S_two_mul_real_cos (2 * Real.pi / (m : ℝ)) k
  have hsin := Real.sin_nonneg_of_nonneg_of_le_pi hangle0 hanglepi
  exact nonneg_of_mul_nonneg_left (heval ▸ hsin) hsinpos

private theorem chebyshev_sum_sin (m r : ℕ) :
    ((S ℝ (r : ℤ)).eval (2 * Real.cos (2 * Real.pi / (m : ℝ))) +
      (S ℝ ((r : ℤ) - 1)).eval (2 * Real.cos (2 * Real.pi / (m : ℝ)))) *
        Real.sin (2 * Real.pi / (m : ℝ)) =
      2 * Real.sin ((2 * r + 1) * (Real.pi / (m : ℝ))) *
        Real.cos (Real.pi / (m : ℝ)) := by
  rw [add_mul, S_two_mul_real_cos, S_two_mul_real_cos, Real.sin_add_sin]
  have ha : (((r : ℤ) : ℝ) + 1) * (2 * Real.pi / (m : ℝ)) +
      ((((r : ℤ) - 1 : ℤ) : ℝ) + 1) * (2 * Real.pi / (m : ℝ)) =
      2 * ((2 * r + 1) * (Real.pi / (m : ℝ))) := by push_cast; ring
  have hb : (((r : ℤ) : ℝ) + 1) * (2 * Real.pi / (m : ℝ)) -
      ((((r : ℤ) - 1 : ℤ) : ℝ) + 1) * (2 * Real.pi / (m : ℝ)) =
      2 * (Real.pi / (m : ℝ)) := by push_cast; ring
  rw [ha, hb]
  ring_nf

private theorem chebyshev_sum_nonneg (m r : ℕ) (hm : 3 ≤ m) (hr : 2 * r + 1 ≤ m) :
    0 ≤ (S ℝ (r : ℤ)).eval (2 * Real.cos (2 * Real.pi / (m : ℝ))) +
      (S ℝ ((r : ℤ) - 1)).eval (2 * Real.cos (2 * Real.pi / (m : ℝ))) := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hm3 : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hθpos : 0 < 2 * Real.pi / (m : ℝ) := div_pos (by positivity) hmpos
  have hθlt : 2 * Real.pi / (m : ℝ) < Real.pi := by
    apply (div_lt_iff₀ hmpos).mpr
    nlinarith [Real.pi_pos]
  have hsinpos := Real.sin_pos_of_pos_of_lt_pi hθpos hθlt
  have hcos : 0 ≤ Real.cos (Real.pi / (m : ℝ)) := by
    apply Real.cos_nonneg_of_neg_pi_div_two_le_of_le
    · have : 0 ≤ Real.pi / (m : ℝ) := le_of_lt (div_pos Real.pi_pos hmpos)
      linarith [Real.pi_pos]
    · apply (div_le_iff₀ hmpos).mpr
      nlinarith [Real.pi_pos]
  have hrreal : 2 * (r : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast hr
  have hangle0 : 0 ≤ (2 * (r : ℝ) + 1) * (Real.pi / (m : ℝ)) := by positivity
  have hanglepi : (2 * (r : ℝ) + 1) * (Real.pi / (m : ℝ)) ≤ Real.pi := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hmpos).mpr
    nlinarith [Real.pi_pos]
  have hsin := Real.sin_nonneg_of_nonneg_of_le_pi hangle0 hanglepi
  apply nonneg_of_mul_nonneg_left _ hsinpos
  rw [chebyshev_sum_sin]
  positivity

private theorem chebyshev_s_nonneg_all (m : ℕ) (k : ℤ)
    (hk : 0 ≤ k + 1) (hkm : m = 0 ∨ 2 * (k + 1) ≤ (m : ℤ)) :
    0 ≤ (S ℝ k).eval (2 * Real.cos (2 * Real.pi / (m : ℝ))) := by
  by_cases hz : m = 0
  · subst m
    simp only [Nat.cast_zero, div_zero, Real.cos_zero, mul_one, S_eval_two]
    exact_mod_cast hk
  have hkm' : 2 * (k + 1) ≤ (m : ℤ) := hkm.resolve_left hz
  by_cases hm3 : 3 ≤ m
  · exact chebyshev_s_nonneg m k hm3 hk hkm'
  have hkcases : k = -1 ∨ k = 0 := by omega
  rcases hkcases with rfl | rfl <;> simp only [S_neg_one, S_zero, Polynomial.eval_zero,
    Polynomial.eval_one, le_refl, zero_le_one]

private theorem chebyshev_sum_nonneg_all (m r : ℕ) (hr : m = 0 ∨ 2 * r < m) :
    0 ≤ (S ℝ (r : ℤ)).eval (2 * Real.cos (2 * Real.pi / (m : ℝ))) +
      (S ℝ ((r : ℤ) - 1)).eval (2 * Real.cos (2 * Real.pi / (m : ℝ))) := by
  by_cases hz : m = 0
  · subst m
    simp only [Nat.cast_zero, div_zero, Real.cos_zero, mul_one, S_eval_two]
    push_cast
    have hr0 : (0 : ℝ) ≤ r := by positivity
    linarith
  have hr' : 2 * r < m := hr.resolve_left hz
  by_cases hm3 : 3 ≤ m
  · exact chebyshev_sum_nonneg m r hm3 (by omega)
  have hrzero : r = 0 := by omega
  subst r
  simp only [Nat.cast_zero, zero_sub, S_zero, S_neg_one, Polynomial.eval_one,
    Polynomial.eval_zero, add_zero, zero_le_one]

private theorem cos_pi_div_nonneg (m : ℕ) (hm : m = 0 ∨ 2 ≤ m) :
    0 ≤ Real.cos (Real.pi / (m : ℝ)) := by
  rcases hm with rfl | hm
  · simp only [Nat.cast_zero, div_zero, Real.cos_zero, zero_le_one]
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
  apply Real.cos_nonneg_of_neg_pi_div_two_le_of_le
  · have : 0 ≤ Real.pi / (m : ℝ) := le_of_lt (div_pos Real.pi_pos hmpos)
    linarith [Real.pi_pos]
  · apply (div_le_iff₀ hmpos).mpr
    nlinarith [Real.pi_pos]

variable {Index W V : Type*} [Group W] {matrix : CoxeterMatrix Index}
  {cs : CoxeterSystem matrix W} [AddCommGroup V] [Module ℝ V]

namespace Realization

variable (realization : Realization cs (V := V))

private def simpleCoroot (i : Index) : Module.Dual ℝ V :=
  (2 : ℝ) • realization.form (realization.simpleRoot i)

private theorem simpleCoroot_self (i : Index) :
    simpleCoroot realization i (realization.simpleRoot i) = 2 := by
  simp only [simpleCoroot, LinearMap.smul_apply, smul_eq_mul, realization.form_root_self,
    mul_one]

private theorem simpleCoroot_root (i j : Index) :
    simpleCoroot realization i (realization.simpleRoot j) =
      -(2 * Real.cos (Real.pi / (matrix i j : ℝ))) := by
  simp only [simpleCoroot, LinearMap.smul_apply, smul_eq_mul, realization.form_root]
  ring

private theorem action_simple_reflection (i : Index) :
    realization.action (cs.simple i) = Module.reflection (simpleCoroot_self realization i) := by
  apply LinearEquiv.ext
  intro x
  rw [realization.action_simple, Module.reflection_apply]
  rfl

private theorem simpleCoroot_product (i j : Index) :
    simpleCoroot realization i (realization.simpleRoot j) *
        simpleCoroot realization j (realization.simpleRoot i) - 2 =
      2 * Real.cos (2 * Real.pi / (matrix i j : ℝ)) := by
  rw [simpleCoroot_root, simpleCoroot_root, matrix.symmetric j i]
  rw [show 2 * Real.pi / (matrix i j : ℝ) =
    2 * (Real.pi / (matrix i j : ℝ)) by ring, Real.cos_two_mul]
  ring

/-- The even alternating-word action has Chebyshev coefficients in the two simple roots. -/
theorem alternatingRoot_even (i j : Index) (r : ℕ) :
    realization.action (cs.wordProd (CoxeterSystem.alternatingWord i j (2 * r)))
      (realization.simpleRoot i) =
    ((S ℝ (r : ℤ)).eval (2 * Real.cos (2 * Real.pi / (matrix i j : ℝ))) +
      (S ℝ ((r : ℤ) - 1)).eval (2 * Real.cos (2 * Real.pi / (matrix i j : ℝ)))) •
        realization.simpleRoot i +
    ((S ℝ ((r : ℤ) - 1)).eval (2 * Real.cos (2 * Real.pi / (matrix i j : ℝ))) *
      (2 * Real.cos (Real.pi / (matrix i j : ℝ)))) • realization.simpleRoot j := by
  have hji : -simpleCoroot realization j (realization.simpleRoot i) =
      2 * Real.cos (Real.pi / (matrix i j : ℝ)) := by
    rw [simpleCoroot_root realization j i, matrix.symmetric j i, neg_neg]
  rw [cs.prod_alternatingWord_eq_mul_pow, ite_eq_left (even_two_mul r), one_mul,
    show 2 * r / 2 = r by omega, map_pow, map_mul,
    action_simple_reflection, action_simple_reflection]
  rw [Module.reflection_mul_reflection_pow_apply_self (simpleCoroot_self realization i)
    (simpleCoroot_self realization j) r
    (2 * Real.cos (2 * Real.pi / (matrix i j : ℝ)))
    (simpleCoroot_product realization i j).symm, hji]

/-- The odd alternating-word action has Chebyshev coefficients in the two simple roots. -/
theorem alternatingRoot_odd (i j : Index) (r : ℕ) :
    realization.action (cs.wordProd (CoxeterSystem.alternatingWord i j (2 * r + 1)))
      (realization.simpleRoot i) =
    ((S ℝ (r : ℤ)).eval (2 * Real.cos (2 * Real.pi / (matrix i j : ℝ))) +
      (S ℝ ((r : ℤ) - 1)).eval (2 * Real.cos (2 * Real.pi / (matrix i j : ℝ)))) •
        realization.simpleRoot i +
    ((S ℝ (r : ℤ)).eval (2 * Real.cos (2 * Real.pi / (matrix i j : ℝ))) *
      (2 * Real.cos (Real.pi / (matrix i j : ℝ)))) • realization.simpleRoot j := by
  have hodd : ¬ Even (2 * r + 1) := Nat.not_even_iff_odd.mpr ⟨r, by omega⟩
  have hji : -simpleCoroot realization j (realization.simpleRoot i) =
      2 * Real.cos (Real.pi / (matrix i j : ℝ)) := by
    rw [simpleCoroot_root realization j i, matrix.symmetric j i, neg_neg]
  rw [cs.prod_alternatingWord_eq_mul_pow, ite_eq_right hodd,
    show (2 * r + 1) / 2 = r by omega, map_mul, map_pow, map_mul,
    action_simple_reflection, action_simple_reflection]
  rw [Module.reflection_mul_reflection_mul_reflection_pow_apply_self
    (simpleCoroot_self realization i) (simpleCoroot_self realization j) r
    (2 * Real.cos (2 * Real.pi / (matrix i j : ℝ)))
    (simpleCoroot_product realization i j).symm, hji]

/-- Below the Coxeter exponent the alternating-root coefficients are nonnegative;
at infinite exponent the same holds for every length. -/
theorem alternatingRoot_nonneg (i j : Index) (n : ℕ)
    (hbound : matrix i j = 0 ∨ n < matrix i j) :
    ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧
      realization.action (cs.wordProd (CoxeterSystem.alternatingWord i j n))
        (realization.simpleRoot i) =
          a • realization.simpleRoot i + b • realization.simpleRoot j := by
  by_cases hone : matrix i j = 1
  · have hn : n = 0 := by rcases hbound with hz | hlt <;> omega
    subst n
    refine ⟨1, 0, zero_le_one, le_refl 0, ?_⟩
    simp only [CoxeterSystem.alternatingWord, cs.wordProd_nil, map_one, one_smul,
      zero_smul, add_zero]
    rfl
  have hcos : 0 ≤ 2 * Real.cos (Real.pi / (matrix i j : ℝ)) := by
    apply mul_nonneg (by norm_num)
    apply cos_pi_div_nonneg
    omega
  obtain ⟨r, hr | hr⟩ := Nat.even_or_odd' n
  · subst n
    refine ⟨_, _, chebyshev_sum_nonneg_all (matrix i j) r hbound,
      mul_nonneg (chebyshev_s_nonneg_all (matrix i j) ((r : ℤ) - 1) (by omega) ?_) hcos,
      realization.alternatingRoot_even i j r⟩
    rcases hbound with hz | hlt
    · exact Or.inl hz
    · exact Or.inr (by omega)
  · subst n
    refine ⟨_, _, chebyshev_sum_nonneg_all (matrix i j) r ?_,
      mul_nonneg (chebyshev_s_nonneg_all (matrix i j) (r : ℤ) (by omega) ?_) hcos,
      realization.alternatingRoot_odd i j r⟩
    · rcases hbound with hz | hlt
      · exact Or.inl hz
      · exact Or.inr (by omega)
    · rcases hbound with hz | hlt
      · exact Or.inl hz
      · exact Or.inr (by omega)


end Realization

end BruhatIntervals
