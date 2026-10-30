import OrbitComplexity.FrobeniusSplitting.Normality.Components.PrimeWitnesses
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.Nilpotent.Basic

/-! # Minimal primes from tensor-extension equations

Generators of a surjective algebra map's kernel generate the extended
kernel after every scalar extension. Power-membership equations certify
minimality when their multipliers remain nonnilpotent in the target.
-/

set_option autoImplicit false

open scoped TensorProduct

namespace FrobeniusSplitting

/-- Power equations for the original kernel generators certify minimality
in a scalar extension when the extended kernel is prime and the multiplier
images remain nonnilpotent. No flatness of the scalar extension is needed. -/
theorem tensor_minimalPrime_of_witnesses
    {R A B L J : Type*}
    [CommRing R] [CommRing A] [CommRing B] [CommRing L]
    [Algebra R A] [Algebra R B] [Algebra R L]
    (f : A →ₐ[R] B) (hf : Function.Surjective f)
    (g : J → A) (hg : Ideal.span (Set.range g) = RingHom.ker f.toRingHom)
    (I : Ideal A) (hI : I ≤ RingHom.ker f.toRingHom)
    (s : J → A) (n : J → ℕ) (heq : ∀ j, s j * g j ^ n j ∈ I)
    (hprime :
      (RingHom.ker (Algebra.TensorProduct.lTensor (S := L) L f).toRingHom).IsPrime)
    (hs : ∀ j, ¬ IsNilpotent ((1 : L) ⊗ₜ[R] f (s j))) :
    RingHom.ker (Algebra.TensorProduct.lTensor (S := L) L f).toRingHom ∈
      (I.map (Algebra.TensorProduct.includeRight : A →ₐ[R] L ⊗[R] A).toRingHom).minimalPrimes := by
  have hincl (x : A) :
      (Algebra.TensorProduct.includeRight : A →ₐ[R] L ⊗[R] A).toRingHom x =
        (1 : L) ⊗ₜ[R] x := rfl
  have hk :
      RingHom.ker (Algebra.TensorProduct.lTensor (S := L) L f).toRingHom =
        (RingHom.ker f.toRingHom).map
          (Algebra.TensorProduct.includeRight : A →ₐ[R] L ⊗[R] A).toRingHom :=
    Algebra.TensorProduct.lTensor_ker (A := L) (g := f) hf
  have hgen :
      Ideal.span (Set.range fun j => (1 : L) ⊗ₜ[R] g j) =
        RingHom.ker (Algebra.TensorProduct.lTensor (S := L) L f).toRingHom := by
    have h := (congrArg
      (fun P : Ideal A =>
        P.map (Algebra.TensorProduct.includeRight : A →ₐ[R] L ⊗[R] A).toRingHom)
      hg).trans hk.symm
    simpa only [Ideal.map_span, ← Set.range_comp, Function.comp_def, hincl] using h
  refine mem_minimalPrimes_of_generators _ _ hprime
    (Set.range fun j => (1 : L) ⊗ₜ[R] g j) hgen
    ((Ideal.map_mono hI).trans hk.ge) ?_
  rintro _ ⟨j, rfl⟩
  refine ⟨(1 : L) ⊗ₜ[R] s j, ?_, n j, ?_⟩
  · intro hmem
    have hzero :
        (Algebra.TensorProduct.lTensor (S := L) L f).toRingHom
          ((1 : L) ⊗ₜ[R] s j) = 0 := hmem
    have hz : (1 : L) ⊗ₜ[R] f (s j) = 0 := hzero
    exact hs j ⟨1, by rw [pow_one, hz]⟩
  · have hmem := Ideal.mem_map_of_mem
      (Algebra.TensorProduct.includeRight : A →ₐ[R] L ⊗[R] A).toRingHom (heq j)
    rw [map_mul, map_pow] at hmem
    simpa only [hincl] using hmem

/-- An injective map on the targets identifies the kernels in a commuting
square by inverse image along the source map. -/
theorem kernel_comap_of_square
    {A B A' B' : Type*}
    [Semiring A] [Semiring B] [Semiring A'] [Semiring B']
    (eA : A →+* A') (eB : B →+* B') (heB : Function.Injective eB)
    (f : A →+* B) (g : A' →+* B')
    (h : eB.comp f = g.comp eA) :
    RingHom.ker f = (RingHom.ker g).comap eA := by
  ext x
  change f x = 0 ↔ g (eA x) = 0
  have hpoint : eB (f x) = g (eA x) := DFunLike.congr_fun h x
  constructor
  · intro hx
    rw [← hpoint, hx, map_zero]
  · intro hx
    apply heB
    rw [hpoint, hx, map_zero]

/-- A commuting square of ring equivalences transfers minimality of an image
kernel over an ideal whose extension is the prescribed target ideal. -/
theorem kernel_minimalPrime_equiv
    {A B A' B' : Type*}
    [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    (eA : A ≃+* A') (eB : B ≃+* B')
    (f : A →+* B) (g : A' →+* B')
    (h : eB.toRingHom.comp f = g.comp eA.toRingHom)
    (I : Ideal A) (J : Ideal A') (hI : I.map eA.toRingHom = J) :
    RingHom.ker f ∈ I.minimalPrimes ↔ RingHom.ker g ∈ J.minimalPrimes := by
  have hk : RingHom.ker f = (RingHom.ker g).comap eA.toRingHom :=
    kernel_comap_of_square eA.toRingHom eB.toRingHom eB.injective f g h
  have hkmap : (RingHom.ker f).map eA.toRingHom = RingHom.ker g := by
    rw [hk]
    exact Ideal.map_comap_of_surjective eA.toRingHom eA.surjective _
  have hkerA : RingHom.ker eA.toRingHom = ⊥ :=
    (RingHom.injective_iff_ker_eq_bot eA.toRingHom).mp eA.injective
  constructor
  · intro hp
    rw [← hI, Ideal.minimalPrimes_map_of_surjective eA.surjective, hkerA, sup_bot_eq]
    exact ⟨RingHom.ker f, hp, hkmap⟩
  · intro hp
    have hcomap := Ideal.minimalPrimes_comap_of_surjective (f := eA.toRingHom) eA.surjective hp
    have hIcomap : J.comap eA.toRingHom = I := by
      rw [← hI]
      exact Ideal.comap_map_of_bijective eA.toRingHom eA.bijective
    rw [← hk, hIcomap] at hcomap
    exact hcomap

/-- Inverse image under a ring equivalence preserves a unit ideal or a
minimal-prime component of the sum of two ideals. -/
theorem minimalPrime_comap_sup
    {R S : Type*} [CommSemiring R] [CommSemiring S]
    (e : R →+* S) (he : Function.Bijective e) (P I J : Ideal S)
    (h : P = ⊤ ∨ P ∈ (I ⊔ J).minimalPrimes) :
    P.comap e = ⊤ ∨
      P.comap e ∈
        (I.comap e ⊔ J.comap e).minimalPrimes := by
  rcases h with htop | hminimal
  · exact Or.inl (by simp only [htop, Ideal.comap_top])
  · apply Or.inr
    refine ⟨⟨hminimal.isPrime.comap e,
      sup_le (Ideal.comap_mono (le_sup_left.trans hminimal.le))
        (Ideal.comap_mono (le_sup_right.trans hminimal.le))⟩, ?_⟩
    rintro Q ⟨hQprime, hIQ⟩ hQP
    have hprime : (Q.map e).IsPrime := by
      let : Q.IsPrime := hQprime
      change (Q.map (RingEquiv.ofBijective e he)).IsPrime
      infer_instance
    have hle : I ⊔ J ≤ Q.map e := by
      rw [← Ideal.map_comap_of_surjective e he.2 (I ⊔ J)]
      apply Ideal.map_mono
      have hsup : (I ⊔ J).comap e = I.comap e ⊔ J.comap e :=
        (Ideal.relIsoOfBijective e he).map_sup I J
      exact hsup ▸ hIQ
    have hmap : Q.map e ≤ P := by
      calc
        Q.map e ≤ (P.comap e).map e := Ideal.map_mono hQP
        _ = P := Ideal.map_comap_of_surjective e he.2 P
    have hminimal' : P ≤ Q.map e := hminimal.2 ⟨hprime, hle⟩ hmap
    calc
      P.comap e ≤ (Q.map e).comap e := Ideal.comap_mono hminimal'
      _ = Q := Ideal.comap_map_of_bijective e he

private theorem tensor_cancel_square
    {S R T A B : Type*}
    [CommSemiring S] [CommSemiring R] [CommSemiring T] [CommSemiring A] [CommSemiring B]
    [Algebra S R] [Algebra S T] [Algebra R T] [IsScalarTower S R T]
    [Algebra S A] [Algebra S B] (f : A →ₐ[S] B) :
    (Algebra.TensorProduct.cancelBaseChange S R T T B).toAlgHom.comp
        (Algebra.TensorProduct.lTensor (S := T) T
          (Algebra.TensorProduct.lTensor (S := R) R f)) =
      (Algebra.TensorProduct.lTensor (S := T) T f).comp
        (Algebra.TensorProduct.cancelBaseChange S R T T A).toAlgHom := by
  apply AlgHom.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul t x =>
      induction x using TensorProduct.inductionOn with
      | tmul r a =>
          change (Algebra.TensorProduct.cancelBaseChange S R T T B)
            (t ⊗ₜ[R] (r ⊗ₜ[S] f a)) =
            (Algebra.TensorProduct.lTensor (S := T) T f)
              ((Algebra.TensorProduct.cancelBaseChange S R T T A)
                (t ⊗ₜ[R] (r ⊗ₜ[S] a)))
          rw [Algebra.TensorProduct.cancelBaseChange_tmul,
            Algebra.TensorProduct.cancelBaseChange_tmul]
          rfl
      | add x y hx hy =>
          simp only [TensorProduct.tmul_add, map_add, hx, hy]
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem tensor_cancel_kernel
    {S R T A B : Type*}
    [CommSemiring S] [CommSemiring R] [CommSemiring T] [CommSemiring A] [CommSemiring B]
    [Algebra S R] [Algebra S T] [Algebra R T] [IsScalarTower S R T]
    [Algebra S A] [Algebra S B] (f : A →ₐ[S] B) :
    RingHom.ker (Algebra.TensorProduct.lTensor (S := T) T
        (Algebra.TensorProduct.lTensor (S := R) R f)).toRingHom =
      (RingHom.ker (Algebra.TensorProduct.lTensor (S := T) T f).toRingHom).comap
        (Algebra.TensorProduct.cancelBaseChange S R T T A).toRingHom := by
  exact kernel_comap_of_square
    (Algebra.TensorProduct.cancelBaseChange S R T T A).toRingHom
    (Algebra.TensorProduct.cancelBaseChange S R T T B).toRingHom
    (Algebra.TensorProduct.cancelBaseChange S R T T B).injective
    (Algebra.TensorProduct.lTensor (S := T) T
      (Algebra.TensorProduct.lTensor (S := R) R f)).toRingHom
    (Algebra.TensorProduct.lTensor (S := T) T f).toRingHom
    (congrArg AlgHom.toRingHom (tensor_cancel_square f))

private theorem tensor_cancel_minimalPrime
    {S R T A B : Type*}
    [CommRing S] [CommRing R] [CommRing T] [CommRing A] [CommRing B]
    [Algebra S R] [Algebra S T] [Algebra R T] [IsScalarTower S R T]
    [Algebra S A] [Algebra S B] (f : A →ₐ[S] B) (I : Ideal A) :
    RingHom.ker (Algebra.TensorProduct.lTensor (S := T) T
        (Algebra.TensorProduct.lTensor (S := R) R f)).toRingHom ∈
        ((I.map (Algebra.TensorProduct.includeRight : A →ₐ[S] R ⊗[S] A).toRingHom).map
          (Algebra.TensorProduct.includeRight : R ⊗[S] A →ₐ[R]
            T ⊗[R] (R ⊗[S] A)).toRingHom).minimalPrimes ↔
      RingHom.ker (Algebra.TensorProduct.lTensor (S := T) T f).toRingHom ∈
        (I.map (Algebra.TensorProduct.includeRight : A →ₐ[S] T ⊗[S]
          A).toRingHom).minimalPrimes := by
  apply kernel_minimalPrime_equiv
    (Algebra.TensorProduct.cancelBaseChange S R T T A).toRingEquiv
    (Algebra.TensorProduct.cancelBaseChange S R T T B).toRingEquiv
    (Algebra.TensorProduct.lTensor (S := T) T
      (Algebra.TensorProduct.lTensor (S := R) R f)).toRingHom
    (Algebra.TensorProduct.lTensor (S := T) T f).toRingHom
    (congrArg AlgHom.toRingHom (tensor_cancel_square f))
  simp only [Ideal.map_map]
  congr 1
  ext a
  change (Algebra.TensorProduct.cancelBaseChange S R T T A)
    ((1 : T) ⊗ₜ[R] ((1 : R) ⊗ₜ[S] a)) = (1 : T) ⊗ₜ[S] a
  rw [Algebra.TensorProduct.cancelBaseChange_tmul, one_smul]

private theorem tensor_cancel_prime_or_top
    {S R T A B : Type*}
    [CommRing S] [CommRing R] [CommRing T] [CommRing A] [CommRing B]
    [Algebra S R] [Algebra S T] [Algebra R T] [IsScalarTower S R T]
    [Algebra S A] [Algebra S B] (f : A →ₐ[S] B)
    (h : RingHom.ker (Algebra.TensorProduct.lTensor (S := T) T f).toRingHom = ⊤ ∨
      (RingHom.ker (Algebra.TensorProduct.lTensor (S := T) T f).toRingHom).IsPrime) :
    RingHom.ker (Algebra.TensorProduct.lTensor (S := T) T
        (Algebra.TensorProduct.lTensor (S := R) R f)).toRingHom = ⊤ ∨
      (RingHom.ker (Algebra.TensorProduct.lTensor (S := T) T
        (Algebra.TensorProduct.lTensor (S := R) R f)).toRingHom).IsPrime := by
  rw [tensor_cancel_kernel f]
  rcases h with htop | hp
  · exact Or.inl (by simp only [htop, Ideal.comap_top])
  · let : (RingHom.ker (Algebra.TensorProduct.lTensor (S := T) T f).toRingHom).IsPrime := hp
    exact Or.inr inferInstance

end FrobeniusSplitting
