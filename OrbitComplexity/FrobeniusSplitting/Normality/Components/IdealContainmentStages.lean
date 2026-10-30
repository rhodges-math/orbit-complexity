import OrbitComplexity.FrobeniusSplitting.Normality.Components.IdealMembershipStages
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import OrbitComplexity.FrobeniusSplitting.Normality.Components.MinimalPrimeStages
import OrbitComplexity.FrobeniusSplitting.Normality.Components.TensorPrimeWitnesses
import Batteries.Tactic.OpenPrivate

/-! # Coefficient stages for ideal inclusions

Containment after extension to the field descends to a finitely generated
coefficient enlargement when the smaller ideal has finitely many generators.
The inclusions use the same original ideals throughout.
-/

set_option autoImplicit false

open scoped TensorProduct

namespace FrobeniusSplitting

universe u

/-- The kernel formula for scalar extension with its extended scalar action. -/
private theorem scalar_kernel
    {R T A B : Type u} [CommRing R] [CommRing T] [CommRing A] [CommRing B]
    [Algebra R T] [Algebra R A] [Algebra R B]
    (f : A →ₐ[R] B) (hf : Function.Surjective f) :
    RingHom.ker (Algebra.TensorProduct.lTensor (S := T) T f).toRingHom =
      (RingHom.ker f.toRingHom).map
        (Algebra.TensorProduct.includeRight : A →ₐ[R] T ⊗[R] A).toRingHom := by
  have fact := Algebra.TensorProduct.lTensor_ker (A := T) f hf
  exact fact

/-- A finite family of ideal inclusions over the field holds over one
coefficient enlargement, provided each smaller ideal is finitely generated. -/
theorem exists_retained_ideal_le
    {K : Type u} [hK : Field K] (S : Subalgebra ℤ K) (hS : S.FG)
    {J : Type u} [hJ : Finite J] (A : J → Type u)
    [hA : ∀ j, CommRing (A j)] [hSA : ∀ j, Algebra S (A j)]
    (I P : ∀ j, Ideal (A j)) (hfg : ∀ j, (I j).FG)
    (hle : ∀ j,
      (I j).map (Algebra.TensorProduct.includeRight : A j →ₐ[S] K ⊗[S] A j).toRingHom ≤
        (P j).map (Algebra.TensorProduct.includeRight : A j →ₐ[S] K ⊗[S] A j).toRingHom) :
    ∃ (R : Subalgebra ℤ K) (hSR : S ≤ R),
      letI : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
      letI : IsScalarTower S R K := Subalgebra.inclusion.isScalarTower_right hSR K
      R.FG ∧ ∀ j,
        (I j).map (Algebra.TensorProduct.includeRight : A j →ₐ[S] R ⊗[S] A j).toRingHom ≤
          (P j).map (Algebra.TensorProduct.includeRight : A j →ₐ[S] R ⊗[S] A j).toRingHom := by
  classical
  choose t ht using hfg
  have native (i : Sigma (fun j => t j)) :
      (1 : K) ⊗ₜ[S] (i.2 : A i.1) ∈
        (P i.1).map
          (Algebra.TensorProduct.includeRight : A i.1 →ₐ[S] K ⊗[S] A i.1).toRingHom := by
    have hmem : (i.2 : A i.1) ∈ I i.1 := by
      rw [← ht i.1]
      exact Ideal.subset_span i.2.property
    exact hle i.1 (Ideal.mem_map_of_mem
      (Algebra.TensorProduct.includeRight : A i.1 →ₐ[S] K ⊗[S] A i.1).toRingHom hmem)
  have retained := @exists_retained_ideal_membership.{u, u, u}
    K hK S hS (Sigma (fun j => t j)) inferInstance (fun i => A i.1)
    (fun i => hA i.1) (fun i => hSA i.1)
    (fun i => P i.1) (fun i => (i.2 : A i.1)) native
  obtain ⟨R, hSR, hR, hmemR⟩ := retained
  refine ⟨R, hSR, ?_⟩
  refine ⟨hR, ?_⟩
  intro j
  rw [Ideal.map_le_iff_le_comap, ← ht j]
  apply Ideal.span_le.mpr
  intro a ha
  have generated := hmemR ⟨j, ⟨a, ha⟩⟩
  exact generated

/-- Inclusions in the kernels of a finite family of surjective algebra maps
over the field hold over one coefficient enlargement when the ideals have
finitely many generators. -/
theorem exists_retained_kernel_le
    {K : Type u} [hK : Field K] (S : Subalgebra ℤ K) (hS : S.FG)
    {J : Type u} [hJ : Finite J] (A B : J → Type u)
    [hA : ∀ j, CommRing (A j)] [hB : ∀ j, CommRing (B j)]
    [hSA : ∀ j, Algebra S (A j)] [hSB : ∀ j, Algebra S (B j)]
    (f : ∀ j, A j →ₐ[S] B j) (hf : ∀ j, Function.Surjective (f j))
    (I : ∀ j, Ideal (A j)) (hfg : ∀ j, (I j).FG)
    (hle : ∀ j,
      (I j).map (Algebra.TensorProduct.includeRight : A j →ₐ[S] K ⊗[S] A j).toRingHom ≤
        RingHom.ker (Algebra.TensorProduct.lTensor (S := K) K (f j)).toRingHom) :
    ∃ (R : Subalgebra ℤ K) (hSR : S ≤ R),
      letI : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
      letI : IsScalarTower S R K := Subalgebra.inclusion.isScalarTower_right hSR K
      R.FG ∧ ∀ j,
        (I j).map (Algebra.TensorProduct.includeRight : A j →ₐ[S] R ⊗[S] A j).toRingHom ≤
          RingHom.ker (Algebra.TensorProduct.lTensor (S := R) R (f j)).toRingHom := by
  have mapped_le (j : J) :
      (I j).map (Algebra.TensorProduct.includeRight : A j →ₐ[S] K ⊗[S] A j).toRingHom ≤
        (RingHom.ker (f j).toRingHom).map
          (Algebra.TensorProduct.includeRight : A j →ₐ[S] K ⊗[S] A j).toRingHom := by
    have equation := @scalar_kernel.{u} S K (A j) (B j)
      inferInstance inferInstance (hA j) (hB j) inferInstance (hSA j) (hSB j) (f j) (hf j)
    have inclusion := (hle j).trans equation.le
    exact inclusion
  have retained := @exists_retained_ideal_le.{u}
    K hK S hS J hJ A hA hSA I (fun j => RingHom.ker (f j).toRingHom) hfg mapped_le
  obtain ⟨R, hSR, hR, hIR⟩ := retained
  let algSR : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
  refine ⟨R, hSR, hR, ?_⟩
  intro j
  have equation := @scalar_kernel.{u} S R (A j) (B j)
    inferInstance inferInstance (hA j) (hB j) algSR (hSA j) (hSB j) (f j) (hf j)
  have containment := (hIR j).trans equation.ge
  exact containment


open private cancel_ideal_membership from
  OrbitComplexity.FrobeniusSplitting.Normality.Components.MinimalPrimeStages
open private tensor_cancel_kernel from
  OrbitComplexity.FrobeniusSplitting.Normality.Components.TensorPrimeWitnesses

/-- Scalar extension carries kernel generators of a surjective algebra map to generators. -/
theorem tensor_kernel_generators
    {S R A B G : Type u} [CommRing S] [CommRing R] [CommRing A] [CommRing B]
    [Algebra S R] [Algebra S A] [Algebra S B]
    (f : A →ₐ[S] B) (hf : Function.Surjective f) (g : G → A)
    (hg : Ideal.span (Set.range g) = RingHom.ker f.toRingHom)
    (fR : R ⊗[S] A →ₐ[R] R ⊗[S] B) (gR : G → R ⊗[S] A)
    (hfR : fR = Algebra.TensorProduct.lTensor (S := R) R f)
    (hgR : gR = fun j => (1 : R) ⊗ₜ[S] g j) :
    Ideal.span (Set.range gR) = RingHom.ker fR.toRingHom := by
  subst fR gR
  have hk : RingHom.ker (Algebra.TensorProduct.lTensor (S := R) R f).toRingHom =
      (RingHom.ker f.toRingHom).map
        (Algebra.TensorProduct.includeRight : A →ₐ[S] R ⊗[S] A).toRingHom :=
    @scalar_kernel.{u} S R A B inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance f hf
  have h := congrArg
    (fun I : Ideal A => I.map
      (Algebra.TensorProduct.includeRight : A →ₐ[S] R ⊗[S] A).toRingHom) hg
  have hincl (a : A) :
      (Algebra.TensorProduct.includeRight : A →ₐ[S] R ⊗[S] A).toRingHom a =
        (1 : R) ⊗ₜ[S] a := rfl
  simpa only [Ideal.map_span, ← Set.range_comp, Function.comp_def, hincl]
    using h.trans hk.symm

/-- Tensor cancellation preserves containment of an extended ideal in a kernel. -/
theorem tensor_cancel_kernel_le
    {S R T A B : Type u}
    [CommSemiring S] [CommSemiring R] [CommSemiring T] [CommSemiring A] [CommSemiring B]
    [Algebra S R] [Algebra S T] [Algebra R T] [IsScalarTower S R T]
    [Algebra S A] [Algebra S B]
    (f : A →ₐ[S] B) (I : Ideal A)
    (fR : R ⊗[S] A →ₐ[R] R ⊗[S] B) (IR : Ideal (R ⊗[S] A))
    (hfR : fR = Algebra.TensorProduct.lTensor (S := R) R f)
    (hIR : IR = I.map (Algebra.TensorProduct.includeRight : A →ₐ[S] R ⊗[S] A).toRingHom)
    (h : I.map (Algebra.TensorProduct.includeRight : A →ₐ[S] T ⊗[S] A).toRingHom ≤
      RingHom.ker (Algebra.TensorProduct.lTensor (S := T) T f).toRingHom) :
    IR.map
        (Algebra.TensorProduct.includeRight :
          R ⊗[S] A →ₐ[R] T ⊗[R] (R ⊗[S] A)).toRingHom ≤
      RingHom.ker (Algebra.TensorProduct.lTensor (S := T) T fR).toRingHom := by
  subst fR IR
  rw [@tensor_cancel_kernel.{u} S R T A B
    inferInstance inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance f]
  intro x hx
  exact h ((@cancel_ideal_membership.{u, u, u, u} S R T A
    inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance inferInstance I x).mp hx)

/-- Tensor cancellation preserves a proper scalar-extended kernel. -/
theorem tensor_cancel_kernel_ne_top
    {S R T A B : Type u}
    [CommSemiring S] [CommSemiring R] [CommSemiring T] [CommSemiring A] [CommSemiring B]
    [Algebra S R] [Algebra S T] [Algebra R T] [IsScalarTower S R T]
    [Algebra S A] [Algebra S B]
    (f : A →ₐ[S] B) (fR : R ⊗[S] A →ₐ[R] R ⊗[S] B)
    (hfR : fR = Algebra.TensorProduct.lTensor (S := R) R f)
    (hproper : RingHom.ker (Algebra.TensorProduct.lTensor (S := T) T f).toRingHom ≠ ⊤) :
    RingHom.ker (Algebra.TensorProduct.lTensor (S := T) T fR).toRingHom ≠ ⊤ := by
  subst fR
  rw [@tensor_cancel_kernel.{u} S R T A B
    inferInstance inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance f]
  intro htop
  exact hproper ((Ideal.comap_eq_top_iff
    (f := (Algebra.TensorProduct.cancelBaseChange S R T T A).toRingHom)).mp htop)

/-- A ring homomorphism carries a power-membership equation into the extended ideal. -/
theorem map_power_membership
    {A B : Type u} [CommSemiring A] [CommSemiring B]
    (q : A →+* B) (I : Ideal A) (J : Ideal B) (hJ : J = I.map q)
    (x y : A) (n : ℕ) (x' y' : B) (hx : x' = q x) (hy : y' = q y)
    (h : x * y ^ n ∈ I) : x' * y' ^ n ∈ J := by
  subst J x' y'
  have mapped := Ideal.mem_map_of_mem q h
  simpa only [map_mul, map_pow] using mapped

/-- Tensor cancellation preserves nonnilpotence of a pure scalar extension. -/
theorem tensor_cancel_not_nilpotent
    {R T L B : Type u}
    [CommSemiring R] [CommSemiring T] [CommSemiring L] [CommSemiring B]
    [Algebra R T] [Algebra R L] [Algebra T L] [IsScalarTower R T L] [Algebra R B]
    (x : B) (y : T ⊗[R] B) (hy : y = (1 : T) ⊗ₜ[R] x)
    (h : ¬ IsNilpotent ((1 : L) ⊗ₜ[R] x)) :
    ¬ IsNilpotent ((1 : L) ⊗ₜ[T] y) := by
  subst y
  intro hnil
  have mapped := hnil.map (Algebra.TensorProduct.cancelBaseChange R T L L B).toRingHom
  change IsNilpotent ((Algebra.TensorProduct.cancelBaseChange R T L L B)
    ((1 : L) ⊗ₜ[T] ((1 : T) ⊗ₜ[R] x))) at mapped
  rw [Algebra.TensorProduct.cancelBaseChange_tmul, one_smul] at mapped
  exact h mapped

end FrobeniusSplitting
