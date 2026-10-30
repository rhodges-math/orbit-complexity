import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Algebra.MonoidAlgebra.Module
import Mathlib.LinearAlgebra.Finsupp.LSum
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.FieldTheory.Perfect
import Mathlib.Algebra.Polynomial.Eval.Degree

/-! # Polynomial coordinates for Frobenius scalars -/

noncomputable section
namespace FrobeniusSplitting
universe u

open Polynomial

section
variable (C : Type u) [CommRing C] (p : ℕ) [NeZero p]

private def coefficients : Polynomial C ≃ₗ[C] ℕ →₀ C :=
  (Polynomial.toFinsuppIsoLinear C).trans (AddMonoidAlgebra.coeffLinearEquiv C)

private def residues : Polynomial C ≃ₗ[C] Fin p → Polynomial C :=
  (coefficients C).trans <|
    (Finsupp.domLCongr ((Nat.divModEquiv p).trans (Equiv.prodComm ℕ (Fin p)))).trans <|
      (Finsupp.curryLinearEquiv C).trans <|
        (Finsupp.mapRange.linearEquiv (coefficients C).symm).trans
          (Finsupp.linearEquivFunOnFinite C (Polynomial C) (Fin p))

private theorem residues_coeff (f : Polynomial C) (i : Fin p) (q : ℕ) :
    ((residues C p f) i).coeff q = f.coeff (q * p + i) := rfl

private theorem residues_monomial (q : ℕ) (a : C) :
    residues C p (monomial q a) =
      Pi.single (Fin.ofNat p q) (monomial (q / p) a) := by
  classical
  simp [residues, coefficients, Finsupp.curry_single]
  rfl

private def reassemble (v : Fin p → Polynomial C) : Polynomial C :=
  ∑ i, Polynomial.expand C p (v i) * X ^ (i : ℕ)

private theorem reconstruct (f : Polynomial C) :
    reassemble C p (residues C p f) = f := by
  classical
  induction f using Polynomial.induction_on' with
  | add f g hf hg =>
    simpa only [reassemble, map_add, Pi.add_apply, add_mul, Finset.sum_add_distrib]
      using congrArg₂ (· + ·) hf hg
  | monomial q a =>
    rw [residues_monomial]
    simp only [reassemble, Pi.single_apply, apply_ite (Polynomial.expand C p), map_zero,
      ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [Polynomial.expand_monomial]
    simp only [← Polynomial.C_mul_X_pow_eq_monomial, mul_assoc, ← pow_add,
      Fin.val_ofNat, Nat.div_add_mod']

private theorem reassemble_inverse (v : Fin p → Polynomial C) :
    reassemble C p v = (residues C p).symm v := by
  obtain ⟨f, rfl⟩ := (residues C p).surjective v
  rw [reconstruct, LinearEquiv.symm_apply_apply]

/-- Over any coefficient ring, polynomial scalars act through expansion by p. -/
@[instance_reducible]
def polynomialExpandModule : Module (Polynomial C) (Polynomial C) :=
  Module.compHom _ (Polynomial.expand C p).toRingHom

private def expandedEval :
    let domain := (inferInstance : Module (Polynomial C) (Fin p → Polynomial C))
    letI := polynomialExpandModule C p
    letI := domain
    (Fin p → Polynomial C) →ₗ[Polynomial C] Polynomial C := by
  let domain := (inferInstance : Module (Polynomial C) (Fin p → Polynomial C))
  let := polynomialExpandModule C p
  let := domain
  refine { toFun := reassemble C p, map_add' := ?_, map_smul' := ?_ }
  · intro v w
    simp [reassemble, map_add, add_mul, Finset.sum_add_distrib]
  · intro r v
    change reassemble C p (fun i => r * v i) =
      Polynomial.expand C p r * reassemble C p v
    simp [reassemble, map_mul, Finset.mul_sum, mul_assoc]

/-- Over any coefficient ring, residue monomials give the evaluation isomorphism
over p-divisible polynomial coordinates. -/
def polynomialFrobeniusEval :
    let domain := (inferInstance : Module (Polynomial C) (Fin p → Polynomial C))
    letI := polynomialExpandModule C p
    letI := domain
    (Fin p → Polynomial C) ≃ₗ[Polynomial C] Polynomial C := by
  let domain := (inferInstance : Module (Polynomial C) (Fin p → Polynomial C))
  let := polynomialExpandModule C p
  let := domain
  apply LinearEquiv.ofBijective (expandedEval C p)
  change Function.Bijective (reassemble C p)
  have he : reassemble C p = (residues C p).symm := funext (reassemble_inverse C p)
  rw [he]
  exact (residues C p).symm.bijective

/-- Evaluation is the finite sum of expanded coefficients times the residue monomials. -/
theorem polynomialFrobeniusEval_apply (v : Fin p → Polynomial C) :
    polynomialFrobeniusEval C p v =
      ∑ i, Polynomial.expand C p (v i) * X ^ (i : ℕ) := rfl

end

section
variable (C : Type u) [CommRing C] (p : ℕ) [ExpChar C p] [PerfectRing C p]

/-- The polynomial target has its scalar action restricted along absolute Frobenius. -/
@[instance_reducible]
def polynomialAbsoluteModule : Module (Polynomial C) (Polynomial C) :=
  Module.compHom _ (frobenius (Polynomial C) p)

private def absoluteEval :
    let domain := (inferInstance : Module (Polynomial C) (Fin p → Polynomial C))
    letI := polynomialAbsoluteModule C p
    letI := domain
    (Fin p → Polynomial C) →ₗ[Polynomial C] Polynomial C := by
  let domain := (inferInstance : Module (Polynomial C) (Fin p → Polynomial C))
  let := polynomialAbsoluteModule C p
  let := domain
  refine
    { toFun := fun v => ∑ i, (v i) ^ p * X ^ (i : ℕ)
      map_add' := ?_
      map_smul' := ?_ }
  · intro v w
    simp [Pi.add_apply, add_pow_expChar, add_mul, Finset.sum_add_distrib]
  · intro r v
    change (∑ i, (r * v i) ^ p * X ^ (i : ℕ)) = r ^ p * ∑ i, (v i) ^ p * X ^ (i : ℕ)
    simp [mul_pow, Finset.mul_sum, mul_assoc]

private theorem absolute_bijective :
    Function.Bijective (fun v : Fin p → Polynomial C => ∑ i, (v i) ^ p * X ^ (i : ℕ)) := by
  let : NeZero p := ⟨expChar_ne_zero C p⟩
  have he : Function.Bijective (fun v : Fin p → Polynomial C =>
      fun i => Polynomial.map (frobenius C p) (v i)) :=
    (Equiv.piCongrRight
      (fun _ : Fin p => (Polynomial.mapEquiv (frobeniusEquiv C p)).toEquiv)).bijective
  have hf : (fun v : Fin p → Polynomial C => ∑ i, (v i) ^ p * X ^ (i : ℕ)) =
      fun v => polynomialFrobeniusEval C p (fun i => Polynomial.map (frobenius C p) (v i)) := by
    funext v
    rw [polynomialFrobeniusEval_apply]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← Polynomial.map_expand, Polynomial.map_frobenius_expand]
  rw [hf]
  exact (polynomialFrobeniusEval C p).bijective.comp he

/-- Residue monomials evaluate freely for absolute Frobenius over perfect coefficients. -/
def polynomialAbsoluteEval :
    let domain := (inferInstance : Module (Polynomial C) (Fin p → Polynomial C))
    letI := polynomialAbsoluteModule C p
    letI := domain
    (Fin p → Polynomial C) ≃ₗ[Polynomial C] Polynomial C := by
  let domain := (inferInstance : Module (Polynomial C) (Fin p → Polynomial C))
  let := polynomialAbsoluteModule C p
  let := domain
  exact LinearEquiv.ofBijective (absoluteEval C p) (absolute_bijective C p)

/-- Absolute evaluation raises the coefficients to their pth powers. -/
theorem polynomialAbsoluteEval_apply (v : Fin p → Polynomial C) :
    polynomialAbsoluteEval C p v = ∑ i, (v i) ^ p * X ^ (i : ℕ) := rfl

end

end FrobeniusSplitting
