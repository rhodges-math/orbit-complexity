import OrbitComplexity.GroupActions.Rosenlicht.TensorPoints

/-!
# Integral scalar extensions and rational evaluation

An integral affine algebra of finite type over an algebraically closed field remains
integral after tensoring with any integral algebra. Tensor point evaluations also
detect a rational equation from the points at which a specified denominator is nonzero.

## Main results

* `isDomain_tensorProduct`: integral scalar extension of an integral affine algebra.
* `tensor_eq_zero_of_eval_on_domain`: pointwise vanishing away from a denominator detects zero.
-/

namespace GroupActions

noncomputable section

open scoped TensorProduct

universe u v w

variable {K : Type u} [Field K] [IsAlgClosed K]
variable {A : Type v} [CommRing A] [Algebra K A] [Algebra.FiniteType K A] [IsDomain A]
variable {B : Type w} [CommRing B] [Algebra K B] [IsDomain B]

omit [IsAlgClosed K] [Algebra.FiniteType K A] [IsDomain A] [IsDomain B] in
private lemma component_tensorPointEval (φ : Module.Dual K B) (t : A ⊗[K] B)
    (g : A →ₐ[K] K) :
    g (LinearMap.tensorComponent φ t) = φ (tensorPointEval g t) := by
  induction t using TensorProduct.inductionOn with
  | add s t hs ht => simp [hs, ht]
  | tmul a b => simp [tensorPointEval_tmul, mul_comm]

/-- An integral finite-type algebra over an algebraically closed field remains integral
after tensoring with any integral algebra over that field. -/
theorem isDomain_tensorProduct : IsDomain (A ⊗[K] B) := by
  classical
  have hzero : ∀ x y : A ⊗[K] B, x * y = 0 → x = 0 ∨ y = 0 := by
    intro x y hxy
    by_cases hx : x = 0
    · exact Or.inl hx
    right
    have hφ : ∃ φ : Module.Dual K B, LinearMap.tensorComponent φ x ≠ 0 := by
      by_contra! h
      apply hx
      apply TensorProduct.tensor_eq_of_forall_tensorComponent_eq
      intro φ
      simpa using h φ
    obtain ⟨φ, hφ⟩ := hφ
    apply TensorProduct.tensor_eq_of_forall_tensorComponent_eq
    intro ψ
    simp only [map_zero]
    have hcomp : LinearMap.tensorComponent φ x * LinearMap.tensorComponent ψ y = 0 := by
      apply TauCeti.eq_of_forall_algHom_apply_eq (k := K) (K := K)
      intro g
      rw [map_mul, map_zero, component_tensorPointEval, component_tensorPointEval]
      have hg : tensorPointEval g x * tensorPointEval g y = 0 := by
        rw [← map_mul, hxy, map_zero]
      rcases mul_eq_zero.mp hg with hxg | hyg
      · simp [hxg]
      · simp [hyg]
    exact (mul_eq_zero.mp hcomp).resolve_left hφ
  have : NoZeroDivisors (A ⊗[K] B) := ⟨fun {x y} h ↦ hzero x y h⟩
  obtain ⟨g, _⟩ := TauCeti.exists_algHom_apply_ne_zero_of_not_isNilpotent
    (k := K) (K := K) (x := (1 : A)) (by simp)
  have : Nontrivial (A ⊗[K] B) := ⟨⟨0, 1, fun h ↦ by
    have h' := congrArg (tensorPointEval (B := B) g) h
    exact zero_ne_one (by simpa only [map_zero, map_one] using h')⟩⟩
  exact { toIsCancelMulZero := inferInstance, toNontrivial := inferInstance }

/-- A tensor equation holding at all base-valued evaluations where a nonzero
denominator is defined holds identically. -/
theorem tensor_eq_zero_of_eval_on_domain (r s : A ⊗[K] B) (hs : s ≠ 0)
    (h : ∀ g : A →ₐ[K] K, tensorPointEval g s ≠ 0 → tensorPointEval g r = 0) :
    r = 0 := by
  have : IsDomain (A ⊗[K] B) := isDomain_tensorProduct
  have hrs : r * s = 0 := by
    apply tensorPointEval_jointlyInjective (t := 0)
    intro g
    rw [map_zero, map_mul]
    by_cases hsg : tensorPointEval g s = 0
    · rw [hsg, mul_zero]
    · rw [h g hsg, zero_mul]
  exact (mul_eq_zero.mp hrs).resolve_right hs

end

end GroupActions
