import OrbitComplexity.GroupActions.Rosenlicht.TensorGenerators
import OrbitComplexity.GroupActions.Varieties.AffineProduct

/-!
# TensorPointLifts
-/

open scoped TensorProduct

namespace GroupActions

noncomputable section

universe u v w z a

/-- A pair of algebra points factors through a tensor quotient when it
annihilates the polynomial relations of generators of the second factor. -/
theorem exists_tensorPoint_factor
    (K : Type u) [CommRing K] (R : Type v) [CommRing R] [Algebra K R]
    (B : Type w) [CommRing B] [Algebra K B]
    (A : Type z) [CommRing A]
    (φ : R ⊗[K] B →+* A) (hφ : Function.Surjective φ)
    {ι : Type a} (c : ι → B) (hc : Algebra.adjoin K (Set.range c) = ⊤)
    (x : R →ₐ[K] K) (y : B →ₐ[K] K) :
    letI : Algebra R A :=
      (φ.comp (Algebra.TensorProduct.includeLeft : R →ₐ[K] R ⊗[K] B).toRingHom).toAlgebra
    let f : MvPolynomial ι R →ₐ[R] A :=
      MvPolynomial.aeval (fun i ↦ φ ((1 : R) ⊗ₜ[K] c i))
    RingHom.ker f ≤ RingHom.ker (MvPolynomial.eval₂Hom x.toRingHom (fun i ↦ y (c i))) →
      ∃ ρ : A →+* K, ρ.comp φ =
        (Algebra.TensorProduct.lift x y (fun _ _ ↦ Commute.all _ _)).toRingHom := by
  let : Algebra R A :=
    (φ.comp (Algebra.TensorProduct.includeLeft : R →ₐ[K] R ⊗[K] B).toRingHom).toAlgebra
  let f : MvPolynomial ι R →ₐ[R] A :=
    MvPolynomial.aeval (fun i ↦ φ ((1 : R) ⊗ₜ[K] c i))
  change RingHom.ker f ≤ RingHom.ker
    (MvPolynomial.eval₂Hom x.toRingHom (fun i ↦ y (c i))) → _
  intro hrel
  have hf : Function.Surjective f := by
    apply tensorPresentation_surjective K R B A (MvPolynomial ι R) φ hφ c hc f.toRingHom
    · intro r
      refine ⟨MvPolynomial.C r, ?_⟩
      exact f.commutes r
    · intro i
      exact ⟨MvPolynomial.X i, MvPolynomial.aeval_X _ _⟩
  let ev := MvPolynomial.eval₂Hom x.toRingHom (fun i ↦ y (c i))
  let ρ := f.toRingHom.liftOfSurjective hf ⟨ev, hrel⟩
  have hρ (p : MvPolynomial ι R) : ρ (f p) = ev p :=
    RingHom.liftOfSurjective_comp_apply _ hf ⟨ev, hrel⟩ p
  have hleft (r : R) : ρ (φ (r ⊗ₜ[K] (1 : B))) = x r := by
    have h := hρ (MvPolynomial.C r)
    simp only [ev, MvPolynomial.eval₂Hom_C] at h
    change ρ (f (MvPolynomial.C r)) = x r at h
    exact (show f (MvPolynomial.C r) = φ (r ⊗ₜ[K] (1 : B)) from f.commutes r) ▸ h
  have hright (b : B) : ρ (φ ((1 : R) ⊗ₜ[K] b)) = y b := by
    have hb : b ∈ Algebra.adjoin K (Set.range c) :=
      hc.symm ▸ (show b ∈ (⊤ : Subalgebra K B) from trivial)
    induction hb using Algebra.adjoin_induction with
    | mem b hb =>
      obtain ⟨i, rfl⟩ := hb
      have h := hρ (MvPolynomial.X i)
      simpa only [f, ev, MvPolynomial.aeval_X, MvPolynomial.eval₂Hom_X'] using h
    | algebraMap k =>
      have ht : (1 : R) ⊗ₜ[K] algebraMap K B k = algebraMap K R k ⊗ₜ[K] (1 : B) := by
        simp only [Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul,
          TensorProduct.smul_tmul']
      rw [ht, hleft, x.commutes, y.commutes]
    | add b d _ _ hb hd =>
      simp only [TensorProduct.tmul_add, map_add, hb, hd]
    | mul b d _ _ hb hd =>
      have ht : (1 : R) ⊗ₜ[K] (b * d) =
          ((1 : R) ⊗ₜ[K] b) * ((1 : R) ⊗ₜ[K] d) := by simp
      rw [ht, map_mul, map_mul, hb, hd, map_mul]
  refine ⟨ρ, ?_⟩
  apply RingHom.ext
  intro t
  induction t using TensorProduct.inductionOn with
  | tmul r b =>
    have ht : r ⊗ₜ[K] b = (r ⊗ₜ[K] (1 : B)) * ((1 : R) ⊗ₜ[K] b) := by simp
    change ρ (φ (r ⊗ₜ[K] b)) =
      Algebra.TensorProduct.lift x y (fun _ _ ↦ Commute.all _ _) (r ⊗ₜ[K] b)
    rw [Algebra.TensorProduct.lift_tmul, ht, map_mul, map_mul, hleft, hright]
  | add s t hs ht => simpa only [map_add] using congrArg₂ (· + ·) hs ht

end

end GroupActions
