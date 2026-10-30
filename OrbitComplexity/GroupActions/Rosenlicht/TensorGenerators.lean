import OrbitComplexity.GroupActions.Rosenlicht.AffineCorrespondenceFields
import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Generators of tensor quotient algebras
-/

open scoped TensorProduct

namespace GroupActions

noncomputable section

universe u v w z a t

/-- A quotient of a tensor algebra is generated over its first factor by the
images of any algebra-generating tuple of the second factor. -/
theorem tensorPresentation_surjective
    (K : Type u) [CommRing K] (R : Type v) [CommRing R] [Algebra K R]
    (B : Type w) [CommRing B] [Algebra K B]
    (A : Type z) [CommRing A] (T : Type t) [CommRing T]
    (φ : R ⊗[K] B →+* A) (hφ : Function.Surjective φ)
    {ι : Type a} (c : ι → B) (hc : Algebra.adjoin K (Set.range c) = ⊤)
    (f : T →+* A)
    (hleft : ∀ r : R, φ (r ⊗ₜ[K] (1 : B)) ∈ f.range)
    (hf : ∀ i, φ ((1 : R) ⊗ₜ[K] c i) ∈ f.range) :
    Function.Surjective f := by
  let S := f.range
  have hright (b : B) : φ ((1 : R) ⊗ₜ[K] b) ∈ S := by
    have hb : b ∈ Algebra.adjoin K (Set.range c) :=
      hc.symm ▸ (show b ∈ (⊤ : Subalgebra K B) from trivial)
    induction hb using Algebra.adjoin_induction with
    | mem b hb =>
      obtain ⟨i, rfl⟩ := hb
      exact hf i
    | algebraMap k =>
      have ht : (1 : R) ⊗ₜ[K] algebraMap K B k = algebraMap K R k ⊗ₜ[K] (1 : B) := by
        simp only [Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul,
          TensorProduct.smul_tmul']
      rw [ht]
      exact hleft _
    | add b d _ _ hb hd =>
      simpa only [TensorProduct.tmul_add, map_add] using S.add_mem hb hd
    | mul b d _ _ hb hd =>
      have ht : (1 : R) ⊗ₜ[K] (b * d) =
          ((1 : R) ⊗ₜ[K] b) * ((1 : R) ⊗ₜ[K] d) := by simp
      rw [ht, map_mul]
      exact S.mul_mem hb hd
  have hall (t : R ⊗[K] B) : φ t ∈ S := by
    induction t using TensorProduct.inductionOn with
    | tmul r b =>
      have ht : r ⊗ₜ[K] b = (r ⊗ₜ[K] (1 : B)) * ((1 : R) ⊗ₜ[K] b) := by simp
      rw [ht, map_mul]
      exact S.mul_mem (hleft r) (hright b)
    | add s t hs ht => simpa only [map_add] using S.add_mem hs ht
  intro a
  obtain ⟨t, rfl⟩ := hφ a
  exact hall t

end

end GroupActions
