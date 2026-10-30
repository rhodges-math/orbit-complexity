import OrbitComplexity.FrobeniusSplitting.Modules.Polynomial
import OrbitComplexity.FrobeniusSplitting.Splittings.CartierCoordinates
import OrbitComplexity.FrobeniusSplitting.Splittings.Perfect
import OrbitComplexity.FrobeniusSplitting.Splittings.OperatorTransport

/-! # The polynomial trace pairing -/

open Polynomial
noncomputable section
namespace FrobeniusSplitting

variable (C : Type*) [CommRing C] (p : ℕ) [ExpChar C p] [PerfectRing C p]

private theorem operator_ext_residues (φ ψ : FrobeniusLinearMap (Polynomial C) p)
    (h : ∀ i : Fin p, φ (X ^ (i : ℕ)) = ψ (X ^ (i : ℕ))) : φ = ψ := by
  apply FrobeniusLinearMap.ext
  intro f
  obtain ⟨v, hv⟩ := (polynomialAbsoluteEval C p).surjective f
  have hrep : ∑ i : Fin p, (v i) ^ p * X ^ (i : ℕ) = f := hv
  rw [← hrep]
  change φ.toAddMonoidHom (∑ i : Fin p, (v i) ^ p * X ^ (i : ℕ)) =
    ψ.toAddMonoidHom (∑ i : Fin p, (v i) ^ p * X ^ (i : ℕ))
  rw [map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact (φ.map_pow_mul (v i) _).trans
    ((congrArg (fun t => v i * t) (h i)).trans (ψ.map_pow_mul (v i) _).symm)

private theorem trace_residue_pair (i j : Fin p) :
    univariateTrace (RingSplitting.ofPerfectRing C p)
      ((X : Polynomial C) ^ (p - 1 - (i : ℕ) + (j : ℕ))) =
        if i = j then 1 else 0 := by
  have hp : 0 < p := expChar_pos C p
  have hi : (i : ℕ) ≤ p - 1 := by omega
  have hj : (j : ℕ) ≤ p - 1 := by omega
  by_cases hij : i = j
  · subst j
    have he : p - 1 - (i : ℕ) + (i : ℕ) = p - 1 := by omega
    rw [he, ite_eq_left rfl]
    ext n
    cases n with
    | zero =>
      simp only [Polynomial.coeff_one_zero]
      change (univariateTrace (RingSplitting.ofPerfectRing C p)
        (X ^ (p - 1))).coeff 0 = 1
      rw [univariateTrace_coeff, Polynomial.coeff_X_pow]
      simp only [mul_zero, zero_add, ↓reduceIte]
      exact (RingSplitting.ofPerfectRing C p).map_one
    | succ n =>
      have hn : p * (n + 1) + (p - 1) ≠ p - 1 := by nlinarith
      simp only [Polynomial.coeff_one, Nat.succ_ne_zero, ↓reduceIte]
      change (univariateTrace (RingSplitting.ofPerfectRing C p)
        (X ^ (p - 1))).coeff (n + 1) = 0
      rw [univariateTrace_coeff, Polynomial.coeff_X_pow, ite_eq_right hn]
      exact (RingSplitting.ofPerfectRing C p).map_zero
  · rw [ite_eq_right hij]
    ext n
    have hne : p * n + (p - 1) ≠ p - 1 - (i : ℕ) + (j : ℕ) := by
      intro he
      cases n with
      | zero =>
        apply hij
        apply Fin.ext
        omega
      | succ n =>
        have hge : p ≤ p * (n + 1) := Nat.le_mul_of_pos_right p (by omega)
        omega
    simp [univariateTrace_coeff, hne]

private def polynomialOperatorWeight (φ : FrobeniusLinearMap (Polynomial C) p) :
    Polynomial C :=
  ∑ i : Fin p, (φ (X ^ (i : ℕ))) ^ p * X ^ (p - 1 - (i : ℕ))

private theorem trace_weight_reconstruct (φ : FrobeniusLinearMap (Polynomial C) p)
    (j : Fin p) :
    (univariateTrace (RingSplitting.ofPerfectRing C p)).weight
      (polynomialOperatorWeight C p φ) (X ^ (j : ℕ)) = φ (X ^ (j : ℕ)) := by
  classical
  rw [FrobeniusLinearMap.weight_apply]
  simp only [polynomialOperatorWeight, Finset.sum_mul]
  change (univariateTrace (RingSplitting.ofPerfectRing C p)).toAddMonoidHom
      (∑ i : Fin p, (φ (X ^ (i : ℕ))) ^ p * X ^ (p - 1 - (i : ℕ)) *
        X ^ (j : ℕ)) = _
  rw [map_sum]
  have hterm (i : Fin p) :
      univariateTrace (RingSplitting.ofPerfectRing C p)
        ((φ (X ^ (i : ℕ))) ^ p * X ^ (p - 1 - (i : ℕ)) * X ^ (j : ℕ)) =
      if i = j then φ (X ^ (j : ℕ)) else 0 := by
    rw [mul_assoc, ← pow_add, FrobeniusLinearMap.map_pow_mul, trace_residue_pair]
    split_ifs with hij
    · subst i
      simp
    · simp
  simp only [hterm, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- Every polynomial Frobenius-linear operator is a weighted trace. -/
theorem polynomialTrace_weight_surjective :
    Function.Surjective
      (fun f : Polynomial C => (univariateTrace (RingSplitting.ofPerfectRing C p)).weight f) := by
  intro φ
  refine ⟨polynomialOperatorWeight C p φ, ?_⟩
  apply operator_ext_residues C p
  exact trace_weight_reconstruct C p φ

private theorem trace_coordinate_eval (v : Fin p → Polynomial C) (i : Fin p) :
    univariateTrace (RingSplitting.ofPerfectRing C p)
      ((∑ j : Fin p, (v j) ^ p * X ^ (j : ℕ)) * X ^ (p - 1 - (i : ℕ))) = v i := by
  classical
  rw [Finset.sum_mul]
  change (univariateTrace (RingSplitting.ofPerfectRing C p)).toAddMonoidHom
    (∑ j : Fin p, (v j) ^ p * X ^ (j : ℕ) * X ^ (p - 1 - (i : ℕ))) = v i
  rw [map_sum]
  have hterm (j : Fin p) :
      univariateTrace (RingSplitting.ofPerfectRing C p)
        ((v j) ^ p * X ^ (j : ℕ) * X ^ (p - 1 - (i : ℕ))) =
      if i = j then v i else 0 := by
    rw [mul_assoc, ← pow_add, Nat.add_comm (j : ℕ),
      FrobeniusLinearMap.map_pow_mul, trace_residue_pair]
    split_ifs with hij
    · subst j
      simp
    · simp
  simp only [hterm, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

/-- Input multiplication identifies polynomials with all Frobenius-linear operators. -/
theorem polynomialTrace_weight_bijective :
    Function.Bijective
      (fun f : Polynomial C => (univariateTrace (RingSplitting.ofPerfectRing C p)).weight f) := by
  refine ⟨?_, polynomialTrace_weight_surjective C p⟩
  intro f g h
  obtain ⟨v, hv⟩ := (polynomialAbsoluteEval C p).surjective f
  obtain ⟨w, hw⟩ := (polynomialAbsoluteEval C p).surjective g
  have hvec : v = w := by
    funext i
    have hi := congrArg
      (fun φ : FrobeniusLinearMap (Polynomial C) p => φ (X ^ (p - 1 - (i : ℕ)))) h
    change univariateTrace (RingSplitting.ofPerfectRing C p)
        (f * X ^ (p - 1 - (i : ℕ))) =
      univariateTrace (RingSplitting.ofPerfectRing C p)
        (g * X ^ (p - 1 - (i : ℕ))) at hi
    rw [← hv, ← hw, polynomialAbsoluteEval_apply, polynomialAbsoluteEval_apply,
      trace_coordinate_eval, trace_coordinate_eval] at hi
    exact hi
  exact hv.symm.trans ((congrArg (polynomialAbsoluteEval C p) hvec).trans hw)

end FrobeniusSplitting
