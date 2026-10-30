import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.Exact.Basic
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Batteries.Tactic.Lint

/-! # Regular elements in scalar fibres

Projectivity of a principal quotient splits the multiplication sequence as
modules over the coefficient ring. Its retraction persists after every
extension of scalars.
-/

set_option autoImplicit false

noncomputable section

open scoped TensorProduct

namespace FrobeniusSplitting

universe u v w

private theorem leftInverse_of_projective
    {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M]
    {P : Type w} [AddCommGroup P] [Module R P] [Module.Projective R P]
    (f : M →ₗ[R] M) (q : M →ₗ[R] P)
    (hf : Function.Injective f) (hq : Function.Surjective q)
    (hex : Function.Exact f q) :
    ∃ r : M →ₗ[R] M, r.comp f = LinearMap.id := by
  obtain ⟨s, hs⟩ := Module.projective_lifting_property q
    (LinearMap.id : P →ₗ[R] P) hq
  let v : M →ₗ[R] M := LinearMap.id - s.comp q
  have hv (x : M) : v x ∈ LinearMap.range f := by
    apply (hex (v x)).mp
    change q (x - s (q x)) = 0
    rw [map_sub]
    have hsq : q (s (q x)) = q x := LinearMap.congr_fun hs (q x)
    rw [hsq, sub_self]
  let e : M ≃ₗ[R] LinearMap.range f := LinearEquiv.ofInjective f hf
  let v' : M →ₗ[R] LinearMap.range f := v.codRestrict _ hv
  have hvf (x : M) : v' (f x) = e x := by
    apply Subtype.ext
    change f x - s (q (f x)) = f x
    rw [hex.apply_apply_eq_zero, map_zero, sub_zero]
  refine ⟨e.symm.toLinearMap.comp v', ?_⟩
  ext x
  change e.symm (v' (f x)) = x
  rw [hvf, e.symm_apply_apply]

/-- A regular element remains regular after arbitrary scalar extension
when its principal quotient is projective over the coefficient ring. -/
theorem regular_tmul_of_projective_quotient
    {R : Type u} {B : Type v} [CommRing R] [CommRing B] [Algebra R B]
    (d : B) (hd : IsRegular d)
    [Module.Projective R (B ⧸ Ideal.span ({d} : Set B))]
    (L : Type w) [CommRing L] [Algebra R L] :
    IsRegular ((1 : L) ⊗ₜ[R] d : L ⊗[R] B) := by
  let I : Ideal B := Ideal.span ({d} : Set B)
  let f : B →ₗ[R] B := LinearMap.mul R B d
  let q : B →ₗ[R] B ⧸ I := (Ideal.Quotient.mkₐ R I).toLinearMap
  have hex : Function.Exact f q := by
    intro x
    change Ideal.Quotient.mk I x = 0 ↔ ∃ y, d * y = x
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨y, hy.symm⟩
    · rintro ⟨y, hy⟩
      exact ⟨y, hy.symm⟩
  obtain ⟨r, hr⟩ := leftInverse_of_projective f q hd.left
    (Ideal.Quotient.mkₐ_surjective R I) hex
  have ht : (r.lTensor L).comp (f.lTensor L) = LinearMap.id := by
    rw [← LinearMap.lTensor_comp, hr, LinearMap.lTensor_id]
  have hinj : Function.Injective (f.lTensor L) :=
    Function.LeftInverse.injective (fun x => LinearMap.congr_fun ht x)
  have hmul (x : L ⊗[R] B) :
      (f.lTensor L) x = ((1 : L) ⊗ₜ[R] d) * x := by
    induction x using TensorProduct.inductionOn with
    | tmul l b =>
        change l ⊗ₜ[R] (d * b) = ((1 : L) ⊗ₜ[R] d) * (l ⊗ₜ[R] b)
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    | add a b ha hb => simp only [map_add, mul_add, ha, hb]
  have hleft : IsLeftRegular ((1 : L) ⊗ₜ[R] d : L ⊗[R] B) := by
    intro x y h
    apply hinj
    exact (hmul x).trans (h.trans (hmul y).symm)
  exact ⟨hleft, hleft.right_of_commute (fun _ => mul_comm _ _)⟩

end FrobeniusSplitting
