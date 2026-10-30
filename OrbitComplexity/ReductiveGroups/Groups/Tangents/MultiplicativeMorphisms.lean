import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupCoroots
import OrbitComplexity.ReductiveGroups.Groups.Tangents.TangentConvolutionPowers
import Mathlib.LinearAlgebra.Vandermonde

/-! # Multiplicative-group coordinate maps and their tangents -/

noncomputable section
namespace ReductiveGroups
open TauCeti WithConv
open scoped TensorProduct
universe u v
variable {K : Type u} [Field K] {ι : Type v}

private theorem finsupp_eq_zero_of_moments
    (a : ι → K) (ha : Function.Injective a) (f : ι →₀ K)
    (h : ∀ n : ℕ, f.sum (fun q b => b * a q ^ n) = 0) : f = 0 := by
  classical
  let I := {q : ι // q ∈ f.support}
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  let v : Fin (Fintype.card I) → K := fun j => f (e j).val
  let w : Fin (Fintype.card I) → K := fun j => a (e j).val
  have hw : Function.Injective w := by
    intro j k hjk
    apply e.injective
    apply Subtype.ext
    exact ha hjk
  have hv : v = 0 := by
    apply Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hw
    intro n
    change (∑ j : Fin (Fintype.card I), f (e j).val * a (e j).val ^ (n : ℕ)) = 0
    calc
      _ = ∑ q : I, f q.val * a q.val ^ (n : ℕ) := e.sum_comp _
      _ = 0 := by
        exact (Finset.sum_coe_sort_eq_attach f.support
          (fun q => f q.val * a q.val ^ (n : ℕ))).trans
          ((Finset.sum_attach f.support (fun q => f q * a q ^ (n : ℕ))).trans (h (n : ℕ)))
  ext q
  by_cases hq : q ∈ f.support
  · have hj := congrFun hv (e.symm ⟨q, hq⟩)
    simpa only [v, Equiv.apply_symm_apply, Pi.zero_apply, Finsupp.zero_apply] using hj
  · exact Finsupp.notMem_support_iff.mp hq


private theorem gm_tangent_value (m : Multiplicative ℤ) :
    (Bialgebra.CounitAlgebra.algEquivSelf K (MonoidAlgebra K (Multiplicative ℤ)) K)
      (Coroot.multiplicativeTangent (MonoidAlgebra.single m 1)) = (m.toAdd : K) := by
  change characterDifferential m (Coroot.multiplicativeTangent (K := K)) = _
  unfold Coroot.multiplicativeTangent
  rw [CharacterDifferential.of_additive_tangent]
  rfl

private theorem gm_power_basis (n : ℕ) (m : Multiplicative ℤ) :
    tangentConvolutionPower (Coroot.multiplicativeTangent (K := K)) n
      (MonoidAlgebra.single m 1) = (m.toAdd : K) ^ n := by
  induction n with
  | zero => simp only [tangentConvolutionPower_zero, MonoidAlgebra.counit_single,
      CommSemiring.counit_apply, pow_zero]
  | succ n ih =>
      unfold tangentConvolutionPower
      rw [pow_succ, LinearMap.convMul_apply, MonoidAlgebra.comul_single]
      simp only [CommSemiring.comul_apply, TensorProduct.map_tmul,
        LinearMap.mul'_apply]
      rw [map_mul]
      change tangentConvolutionPower (Coroot.multiplicativeTangent (K := K)) n
        (MonoidAlgebra.single m 1) *
        (Bialgebra.CounitAlgebra.algEquivSelf K (MonoidAlgebra K (Multiplicative ℤ)) K)
          (Coroot.multiplicativeTangent (MonoidAlgebra.single m 1)) = _
      rw [ih, gm_tangent_value, pow_succ]

private theorem gm_power_sum (n : ℕ) (f : MonoidAlgebra K (Multiplicative ℤ)) :
    tangentConvolutionPower (Coroot.multiplicativeTangent (K := K)) n f =
      f.coeff.sum (fun m a => a * (m.toAdd : K) ^ n) := by
  classical
  conv_lhs => rw [← f.sum_coeff_single]
  simp only [tangentConvolutionPower, Finsupp.sum, map_sum]
  apply Finset.sum_congr rfl
  intro m hm
  have hs : MonoidAlgebra.single m (f.coeff m) =
      (f.coeff m) • MonoidAlgebra.single m (1 : K) := by simp
  rw [hs, map_smul, map_smul]
  change f.coeff m * tangentConvolutionPower (Coroot.multiplicativeTangent (K := K)) n
    (MonoidAlgebra.single m 1) = _
  rw [gm_power_basis]

variable [CharZero K] {A : Type v} [CommRing A] [HopfAlgebra K A]

/-- In characteristic zero, the unit tangent determines a multiplicative-group morphism. -/
theorem gmMorphism_ext_of_tangent_eq
    (φ ψ : A →ₐc[K] MonoidAlgebra K (Multiplicative ℤ))
    (h : derivationComp (B := K) φ (Coroot.multiplicativeTangent (K := K)) =
      derivationComp (B := K) ψ (Coroot.multiplicativeTangent (K := K))) : φ = ψ := by
  apply DFunLike.ext
  intro a
  apply sub_eq_zero.mp
  apply (MonoidAlgebra.coeffLinearEquiv K).injective
  change (φ a - ψ a).coeff = 0
  apply finsupp_eq_zero_of_moments (fun m : Multiplicative ℤ => (m.toAdd : K))
    (by intro m n hmn; exact Multiplicative.toAdd.injective (Int.cast_injective hmn))
  intro n
  rw [← gm_power_sum]
  have hp := congrArg (fun d => tangentConvolutionPower d n a) h
  rw [tangentConvolutionPower_comp, tangentConvolutionPower_comp] at hp
  simpa only [tangentConvolutionPower, map_sub] using sub_eq_zero.mpr hp

end ReductiveGroups
