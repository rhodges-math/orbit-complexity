import OrbitComplexity.GroupActions.Tori.MonomialMaps
import OrbitComplexity.GroupActions.MomentMaps.RationalSeparation
import OrbitComplexity.GroupActions.MomentMaps.FiniteHulls
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Batteries.Tactic.Lint

/-! # Exposed supports of homogeneous binomial solutions

A nonzero solution of the homogeneous lattice binomials has support on an exposed
face of the convex hull of its integral weights. The supported indices are exactly
the preimage of that face. No saturation assumption on the weight semigroup is required.
-/

open Multiplicative Matrix Set
noncomputable section
namespace GroupActions
universe u v
variable {I M : Type u} [Fintype I] [AddCommGroup M]

/-- An integral relation cannot have only nonnegative coefficients away from the support
of a solution of all equal-weight binomial equations, unless those coefficients vanish. -/
private theorem binomial_support_relation (w : I → M) (z : I → ℂ)
    (hbin : ∀ d e : I → ℕ, weightMonoidHom w (ofAdd d) = weightMonoidHom w (ofAdd e) →
      ∏ i, z i ^ d i = ∏ i, z i ^ e i)
    (n : I → ℤ) (hn : ∑ i, n i • w i = 0)
    (hpos : ∀ i, z i = 0 → 0 ≤ n i) : ∀ i, z i = 0 → n i = 0 := by
  classical
  let d : I → ℕ := fun i ↦ (n i).toNat
  let e : I → ℕ := fun i ↦ (-n i).toNat
  have hsplit (i : I) : (d i : ℤ) - (e i : ℤ) = n i := by dsimp [d, e]; omega
  have hsum : ∑ i, d i • w i = ∑ i, e i • w i := by
    apply sub_eq_zero.mp
    rw [← Finset.sum_sub_distrib]
    calc
      ∑ i, (d i • w i - e i • w i) = ∑ i, n i • w i := by
        apply Finset.sum_congr rfl
        intro i _
        calc
          d i • w i - e i • w i = ((d i : ℤ) - (e i : ℤ)) • w i := by
            simpa only [sub_eq_add_neg] using
              (natCast_sub_natCast_zsmul (w i) (d i) (e i)).symm
          _ = n i • w i := congrArg (fun r : ℤ ↦ r • w i) (hsplit i)
      _ = 0 := hn
  have heq := hbin d e (by
    change ofAdd (Fintype.linearCombination ℕ w d) =
      ofAdd (Fintype.linearCombination ℕ w e)
    simpa only [Fintype.linearCombination_apply] using congrArg ofAdd hsum)
  have hright : ∏ i, z i ^ e i ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    by_cases hi : z i = 0
    · have he : e i = 0 := by dsimp [e]; have := hpos i hi; omega
      simp [he]
    · exact pow_ne_zero _ hi
  intro i hi
  by_contra hni
  have hd : d i ≠ 0 := by dsimp [d]; have := hpos i hi; omega
  have hleft : ∏ j, z j ^ d j = 0 := by
    apply Finset.prod_eq_zero_iff.mpr
    exact ⟨i, Finset.mem_univ _, by rw [hi, zero_pow hd]⟩
  exact hright (heq.symm.trans hleft)

/-- The support restriction for integral binomial relations also holds for real relations. -/
private theorem binomial_support_real {J : Type u} [Fintype J] (w : I → M)
    (e : M →+ (J → ℤ)) (he : Function.Injective e) (z : I → ℂ)
    (hbin : ∀ d e : I → ℕ, weightMonoidHom w (ofAdd d) = weightMonoidHom w (ofAdd e) →
      ∏ i, z i ^ d i = ∏ i, z i ^ e i)
    (a : I → ℝ) (ha : ∑ i, a i • (fun j ↦ (e (w i) j : ℝ)) = 0)
    (hpos : ∀ i, z i = 0 → 0 ≤ a i) : ∀ i, z i = 0 → a i = 0 := by
  classical
  let A : Matrix J I ℚ := fun j i ↦ (e (w i) j : ℚ)
  have haA : A.map (algebraMap ℚ ℝ) *ᵥ a = 0 := by
    ext j
    have hj := congrFun ha j
    change (∑ i, ((e (w i) j : ℚ) : ℝ) * a i) = 0
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
      Rat.cast_intCast, mul_comm] using hj
  obtain ⟨q, hq, hqzero, hqpos, _⟩ := exists_rat_kernel_sign A a haA
  obtain ⟨c, hc, n, hn⟩ := exists_pos_integer_multiple q
  have hqsum (j : J) : ∑ i, q i * (e (w i) j : ℚ) = 0 := by
    simpa [A, Matrix.mulVec, dotProduct, mul_comm] using congrFun hq j
  have hnrel : ∑ i, n i • w i = 0 := by
    apply he
    simp only [map_sum, map_zsmul, map_zero]
    ext j
    have ht : ∑ i, (n i : ℚ) * (e (w i) j : ℚ) = 0 := by
      simp_rw [hn, mul_assoc]
      rw [← Finset.mul_sum, hqsum, mul_zero]
    have htZ : ∑ i, n i * e (w i) j = 0 := by exact_mod_cast ht
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using htZ
  have hnpos (i : I) (hi : z i = 0) : 0 ≤ n i := by
    have hqa : 0 ≤ q i := by
      by_cases hai : a i = 0
      · rw [hqzero i hai]
      · exact (hqpos i (lt_of_le_of_ne (hpos i hi) (Ne.symm hai))).le
    have ht : (0 : ℚ) ≤ n i := by rw [hn]; positivity
    exact_mod_cast ht
  have hnzero := binomial_support_relation w z hbin n hnrel hnpos
  intro i hi
  by_contra hai
  have hqp : 0 < q i := hqpos i (lt_of_le_of_ne (hpos i hi) (Ne.symm hai))
  have hnp : (0 : ℚ) < n i := by rw [hn]; positivity
  rw [hnzero i hi, Int.cast_zero] at hnp
  exact (lt_irrefl _ hnp)



section IntegralWeights

variable {J : Type u} [Fintype J]

omit [Fintype I] [Fintype J] in
/-- The convex hull of the weights supported by a nonzero vector is nonempty. -/
theorem binomial_support_nonempty (χ : I → J →₀ ℤ) (z : I → ℂ) (hz : z ≠ 0) :
    (convexHull ℝ ((fun i j ↦ (χ i j : ℝ)) '' Function.support z)).Nonempty := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hz
  exact ⟨fun j ↦ (χ i j : ℝ), subset_convexHull ℝ _ ⟨i, hi, rfl⟩⟩

/-- The support of a nonzero solution of the equal-degree, equal-weight binomial equations
spans a nonempty exposed face and contains every index whose weight belongs to that face. -/
theorem binomial_support_face (χ : I → J →₀ ℤ) (z : I → ℂ) (hz : z ≠ 0)
    (hbin : ∀ d e : I → ℕ,
      weightMonoidHom (fun i ↦ ((1 : ℤ), χ i)) (ofAdd d) =
        weightMonoidHom (fun i ↦ ((1 : ℤ), χ i)) (ofAdd e) →
      ∏ i, z i ^ d i = ∏ i, z i ^ e i) :
    (convexHull ℝ ((fun i j ↦ (χ i j : ℝ)) '' Function.support z)).Nonempty ∧
      IsExposed ℝ (convexHull ℝ (Set.range (fun i j ↦ (χ i j : ℝ))))
        (convexHull ℝ ((fun i j ↦ (χ i j : ℝ)) '' Function.support z)) ∧
      ∀ i, (fun j ↦ (χ i j : ℝ)) ∈
        convexHull ℝ ((fun k j ↦ (χ k j : ℝ)) '' Function.support z) ↔ z i ≠ 0 := by
  classical
  let eZ : (ℤ × (J →₀ ℤ)) ≃ₗ[ℤ] (Option J → ℤ) :=
    ((LinearEquiv.refl ℤ ℤ).prodCongr (Finsupp.linearEquivFunOnFinite ℤ ℤ J)).trans
      (LinearEquiv.piOptionEquivProd ℤ (M := fun _ : Option J ↦ ℤ)).symm
  obtain ⟨f, hfzero, hfneg⟩ := exists_exposing_form
    (fun i j ↦ (eZ (1, χ i) j : ℝ)) (Function.support z)
    (fun a ha hpos i hi ↦ binomial_support_real (fun i ↦ ((1 : ℤ), χ i))
      eZ.toAddEquiv.toAddMonoidHom eZ.injective z hbin a ha
      (fun k hk ↦ hpos k (by simp [Function.mem_support, hk])) i (not_not.mp hi))
  let eR : (ℝ × (J → ℝ)) ≃ₗ[ℝ] (Option J → ℝ) :=
    (LinearEquiv.piOptionEquivProd ℝ (M := fun _ : Option J ↦ ℝ)).symm
  let g : (J → ℝ) →ₗ[ℝ] (Option J → ℝ) :=
    eR.toLinearMap.comp (LinearMap.inr ℝ ℝ (J → ℝ))
  let l : StrongDual ℝ (J → ℝ) := f.comp g.toContinuousLinearMap
  let c : ℝ := -f (eR (1, 0))
  have hsplit (i : I) : f (fun j ↦ (eZ (1, χ i) j : ℝ)) =
      f (eR (1, 0)) + l (fun j ↦ (χ i j : ℝ)) := by
    have hv : (fun j ↦ (eZ (1, χ i) j : ℝ)) =
        eR (1, (fun j ↦ (χ i j : ℝ))) := by
      ext j
      cases j with
      | none => change ((1 : ℤ) : ℝ) = 1; exact Int.cast_one
      | some j => rfl
    rw [hv]
    change f (eR (1, (fun j ↦ (χ i j : ℝ)))) =
      f (eR (1, 0)) + f (eR (0, (fun j ↦ (χ i j : ℝ))))
    rw [← map_add, ← map_add]
    congr 2
    simp
  have hvalue (i : I) (hi : i ∈ Function.support z) : l (fun j ↦ (χ i j : ℝ)) = c := by
    have ht := hfzero i hi
    rw [hsplit] at ht
    dsimp only [c]
    linarith
  have hstrict (i : I) (hi : i ∉ Function.support z) : l (fun j ↦ (χ i j : ℝ)) < c := by
    have ht := hfneg i hi
    rw [hsplit] at ht
    dsimp only [c]
    linarith
  refine ⟨binomial_support_nonempty χ z hz, ?_, ?_⟩
  · have hbound (i : I) : l (fun j ↦ (χ i j : ℝ)) ≤ c := by
      by_cases hi : i ∈ Function.support z
      · exact (hvalue i hi).le
      · exact (hstrict i hi).le
    rw [convexHull_eq_toExposed (fun i j ↦ (χ i j : ℝ)) (Function.support z)
      (Function.support_nonempty_iff.mpr hz) l c hbound hvalue hstrict]
    exact ContinuousLinearMap.toExposed.isExposed
  · intro i
    constructor
    · intro hi
      by_contra hzi
      have hlevel : convexHull ℝ ((fun k j ↦ (χ k j : ℝ)) '' Function.support z) ⊆
          {x | l x = c} := convexHull_min
        (by rintro _ ⟨k, hk, rfl⟩; exact hvalue k hk)
        (convex_hyperplane l.toLinearMap.isLinear c)
      have hlt := hstrict i (by simp [Function.mem_support, hzi])
      rw [hlevel hi] at hlt
      exact lt_irrefl _ hlt
    · intro hi
      exact subset_convexHull ℝ _ ⟨i, hi, rfl⟩

end IntegralWeights
end GroupActions
