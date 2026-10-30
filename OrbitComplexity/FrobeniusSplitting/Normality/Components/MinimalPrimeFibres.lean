import OrbitComplexity.FrobeniusSplitting.Normality.Components.NonvanishingOpens
import OrbitComplexity.FrobeniusSplitting.Normality.Components.TensorPrimeWitnesses
import OrbitComplexity.FrobeniusSplitting.Normality.Components.IdealContainmentStages

/-! # Minimal primes over a common coefficient open

A finite family of power-membership equations and nonnilpotent multiplier
images determines one coefficient open on which the prime kernels are
minimal over the prescribed ideals.
-/

set_option autoImplicit false

open scoped TensorProduct

namespace FrobeniusSplitting

universe u

private theorem ker_ne_top_iff_not_nilpotent_one
    {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) :
    RingHom.ker f ≠ ⊤ ↔ ¬ IsNilpotent (1 : B) := by
  constructor
  · intro hp hnil
    apply (Ideal.ne_top_iff_one _).mp hp
    change f 1 = 0
    obtain ⟨n, hn⟩ := hnil
    simpa only [map_one, one_pow] using hn
  · intro hnil
    apply (Ideal.ne_top_iff_one _).mpr
    intro hone
    apply hnil
    refine ⟨1, ?_⟩
    change f 1 = 0 at hone
    simpa only [map_one, pow_one] using hone

/-- Finite power-membership witnesses remain witnesses for minimal primes
on one nonempty coefficient open, for every field-valued specialization
whose tensor kernel is either the unit ideal or prime. The coefficient
open excludes the unit-ideal case by retaining nonempty target fibres. -/
theorem exists_minimalPrime_open
    {K : Type u} [hK : Field K] (R : Subalgebra ℤ K)
    {J : Type u} [hJ : Finite J] (A B : J → Type u)
    [hA : ∀ j, CommRing (A j)] [hRA : ∀ j, Algebra R (A j)]
    [hB : ∀ j, CommRing (B j)] [hRB : ∀ j, Algebra R (B j)]
    [hfp : ∀ j, Algebra.FinitePresentation R (B j)]
    (G : J → Type u) [hG : ∀ j, Finite (G j)]
    (f : ∀ j, A j →ₐ[R] B j) (hf : ∀ j, Function.Surjective (f j))
    (g : ∀ j, G j → A j)
    (hg : ∀ j, Ideal.span (Set.range (g j)) = RingHom.ker (f j).toRingHom)
    (I : ∀ j, Ideal (A j)) (hI : ∀ j, I j ≤ RingHom.ker (f j).toRingHom)
    (s : ∀ j, G j → A j) (n : ∀ j, G j → ℕ)
    (heq : ∀ j k, s j k * g j k ^ n j k ∈ I j)
    (hproper : ∀ j, RingHom.ker
      (Algebra.TensorProduct.lTensor (S := K) K (f j)).toRingHom ≠ ⊤)
    (hs : ∀ j k, ¬ IsNilpotent ((1 : K) ⊗ₜ[R] (f j) (s j k))) :
    ∃ r : R, r ≠ 0 ∧
      ∀ (L : Type u) [Field L] [Algebra R L], algebraMap R L r ≠ 0 →
        ∀ j, (RingHom.ker
          (Algebra.TensorProduct.lTensor (S := L) L (f j)).toRingHom = ⊤ ∨
          (RingHom.ker
            (Algebra.TensorProduct.lTensor (S := L) L (f j)).toRingHom).IsPrime) →
          RingHom.ker (Algebra.TensorProduct.lTensor (S := L) L (f j)).toRingHom ∈
            ((I j).map
              (Algebra.TensorProduct.includeRight : A j →ₐ[R] L ⊗[R] A
                j).toRingHom).minimalPrimes := by
  let values (i : Sigma (fun j => Option (G j))) : B i.1 :=
    match i.2 with
    | none => 1
    | some k => (f i.1) (s i.1 k)
  have native (i : Sigma (fun j => Option (G j))) :
      ¬ IsNilpotent ((1 : K) ⊗ₜ[R] values i) := by
    rcases i with ⟨j, k⟩
    cases k with
    | none =>
        have hone := (@ker_ne_top_iff_not_nilpotent_one.{u, u}
          (K ⊗[R] A j) (K ⊗[R] B j) inferInstance inferInstance
          (Algebra.TensorProduct.lTensor (S := K) K (f j)).toRingHom).mp (hproper j)
        simpa only [values, Algebra.TensorProduct.one_def] using hone
    | some k => exact hs j k
  have hopen := @exists_fiber_nonvanishing_open.{u, u}
    R K inferInstance inferInstance hK inferInstance inferInstance
    (Sigma (fun j => Option (G j))) inferInstance (fun i => B i.1)
    (fun i => hB i.1) (fun i => hRB i.1) (fun i => hfp i.1)
    values native
  obtain ⟨r, hr, hfield⟩ := hopen
  refine ⟨r, hr, ?_⟩
  intro L hL hRL hrL j hp
  have hscalar := @hfield L hL hRL hrL
  have hone : ¬ IsNilpotent (1 : L ⊗[R] B j) := by
    simpa only [values, Algebra.TensorProduct.one_def] using hscalar ⟨j, none⟩
  have hproperL := (@ker_ne_top_iff_not_nilpotent_one.{u, u}
    (L ⊗[R] A j) (L ⊗[R] B j) inferInstance inferInstance
    (Algebra.TensorProduct.lTensor (S := L) L (f j)).toRingHom).mpr hone
  rcases hp with htop | hp
  · exact (hproperL htop).elim
  · have result := @tensor_minimalPrime_of_witnesses.{u, u, u, u, u}
      R (A j) (B j) L (G j)
      inferInstance (hA j) (hB j) inferInstance (hRA j) (hRB j) hRL
      (f j) (hf j) (g j) (hg j) (I j) (hI j) (s j) (n j) (heq j) hp
      (fun k => hscalar ⟨j, some k⟩)
    exact result

/-- Containment in the kernel of an algebra map. -/
def kernelContains
    {S A B : Type u} [CommSemiring S] [Semiring A] [Semiring B]
    [Algebra S A] [Algebra S B] (f : A →ₐ[S] B) (I : Ideal A) : Prop :=
  I ≤ RingHom.ker f.toRingHom

/-- The kernel of an algebra map is the unit ideal. -/
def kernelUnit
    {S A B : Type u} [CommSemiring S] [Semiring A] [Semiring B]
    [Algebra S A] [Algebra S B] (f : A →ₐ[S] B) : Prop :=
  RingHom.ker f.toRingHom = ⊤

/-- The kernel of a scalar-extended map is the unit ideal. -/
def tensorKernelUnit
    {S : Type u} [CommSemiring S] (R : Type u) [CommSemiring R]
    {A B : Type u} [Semiring A] [Semiring B]
    [Algebra S R] [Algebra S A] [Algebra S B] (f : A →ₐ[S] B) : Prop :=
  RingHom.ker (Algebra.TensorProduct.lTensor (S := R) R f).toRingHom = ⊤

/-- The extension of an ideal along two successive scalar extensions. -/
def tensorIdeal
    {S R T A : Type u}
    [CommSemiring S] [CommSemiring R] [CommSemiring T] [CommSemiring A]
    [Algebra S R] [Algebra R T] [Algebra S A]
    (I : Ideal A) : Ideal (T ⊗[R] (R ⊗[S] A)) :=
  (I.map (Algebra.TensorProduct.includeRight : A →ₐ[S] R ⊗[S] A).toRingHom).map
    (Algebra.TensorProduct.includeRight :
      R ⊗[S] A →ₐ[R] T ⊗[R] (R ⊗[S] A)).toRingHom

/-- The indices whose scalar-extended kernels are proper. -/
def ProperKernelIndex
    {K S : Type u} [CommRing K] [CommRing S] [Algebra S K]
    {J : Type u} {A B : J → Type u}
    [∀ j, CommRing (A j)] [∀ j, Algebra S (A j)]
    [∀ j, CommRing (B j)] [∀ j, Algebra S (B j)]
    (f : ∀ j, A j →ₐ[S] B j) : Type u :=
  {j : J // RingHom.ker
    (Algebra.TensorProduct.lTensor (S := K) K (f j)).toRingHom ≠ ⊤}

/-- Coefficient maps, ideal containments and power witnesses for a finite family. -/
structure TensorWitnessData
    {K : Type u} [Field K] {S R : Type u} [CommRing S] [CommRing R]
    (T : Subalgebra ℤ K) {J : Type u} (A B : J → Type u)
    [∀ j, CommRing (A j)] [∀ j, Algebra S (A j)]
    [∀ j, CommRing (B j)] [∀ j, Algebra S (B j)]
    [Algebra S R] [Algebra S K] [Algebra R K] [IsScalarTower S R K]
    [Algebra R T] [IsScalarTower R T K]
    (f : ∀ j, A j →ₐ[S] B j) (I : ∀ j, Ideal (A j)) where
  /-- The family after the first scalar extension. -/
  fR : ∀ j, R ⊗[S] A j →ₐ[R] R ⊗[S] B j
  /-- The first maps are the prescribed scalar extensions. -/
  eR : ∀ j, fR j = Algebra.TensorProduct.lTensor (S := R) R (f j)
  /-- The first maps are surjective. -/
  hfR : ∀ j, Function.Surjective (fR j)
  /-- The family after the second scalar extension. -/
  fT : ∀ j, T ⊗[R] (R ⊗[S] A j) →ₐ[T] T ⊗[R] (R ⊗[S] B j)
  /-- The second maps are the prescribed scalar extensions. -/
  eT : ∀ j, fT j = Algebra.TensorProduct.lTensor (S := T) T (fR j)
  /-- The second maps are surjective. -/
  hfT : ∀ j, Function.Surjective (fT j)
  /-- The extended ideals lie in the second kernels. -/
  hIT : ∀ j, kernelContains (fT j) (tensorIdeal (S := S) (R := R) (T := T) (I j))
  /-- Unit kernels remain unit after the second extension. -/
  hunitT : ∀ j,
    tensorKernelUnit (S := S) K (f j) → kernelUnit (fT j)
  /-- The index types of kernel generators. -/
  G : ProperKernelIndex (K := K) f → Type u
  /-- Each generator index type is finite. -/
  finiteG : ∀ j, Finite (G j)
  /-- The kernel generators over the original coefficients. -/
  g : ∀ j, G j → A j.val
  /-- The generators span the original kernels. -/
  hg : ∀ j, Ideal.span (Set.range (g j)) = RingHom.ker (f j.val).toRingHom
  /-- The multipliers in the power equations. -/
  sR : ∀ j, G j → R ⊗[S] A j.val
  /-- The exponents in the power equations. -/
  n : ∀ j, G j → ℕ
  /-- The multiplier power equations in the extended ideals. -/
  heqR : ∀ j k, sR j k * ((1 : R) ⊗ₜ[S] g j k) ^ n j k ∈
    (I j.val).map (Algebra.TensorProduct.includeRight :
      A j.val →ₐ[S] R ⊗[S] A j.val).toRingHom
  /-- The multiplier images on the field fibre are not nilpotent. -/
  hsR : ∀ j k, ¬ IsNilpotent ((1 : K) ⊗ₜ[R] (fR j.val) (sR j k))

/-- Power witnesses give a common coefficient open where prime kernels are minimal. -/
theorem open_from_tensor_witnesses
    {K : Type u} [hK : Field K] {S R : Type u} [CommRing S] [CommRing R]
    (T : Subalgebra ℤ K) {J : Type u} [Finite J] (A B : J → Type u)
    [hA : ∀ j, CommRing (A j)] [hSA : ∀ j, Algebra S (A j)]
    [hB : ∀ j, CommRing (B j)] [hSB : ∀ j, Algebra S (B j)]
    [∀ j, Algebra.FinitePresentation S (B j)]
    [Algebra S R] [Algebra S K] [Algebra R K] [IsScalarTower S R K]
    [Algebra R T] [IsScalarTower R T K]
    (f : ∀ j, A j →ₐ[S] B j) (hf : ∀ j, Function.Surjective (f j))
    (I : ∀ j, Ideal (A j)) (D : TensorWitnessData (R := R) T A B f I) :
    ∃ r : T, r ≠ 0 ∧
      ∀ (L : Type u) [Field L] [Algebra T L], algebraMap T L r ≠ 0 →
        ∀ j : ProperKernelIndex (K := K) f,
          (RingHom.ker (Algebra.TensorProduct.lTensor (S := L) L (D.fT j.val)).toRingHom = ⊤ ∨
            (RingHom.ker (Algebra.TensorProduct.lTensor (S :=
              L) L (D.fT j.val)).toRingHom).IsPrime) →
          RingHom.ker (Algebra.TensorProduct.lTensor (S := L) L (D.fT j.val)).toRingHom ∈
            ((tensorIdeal (S :=
              S) (R := R) (T := T) (I j.val)).map (Algebra.TensorProduct.includeRight :
              T ⊗[R] (R ⊗[S] A j.val) →ₐ[T]
                L ⊗[T] (T ⊗[R] (R ⊗[S] A j.val))).toRingHom).minimalPrimes := by
  let gR (j : ProperKernelIndex (K := K) f) (k : D.G j) : R ⊗[S] A j.val := (1 : R) ⊗ₜ[S] D.g j k
  let gT (j : ProperKernelIndex (K :=
    K) f) (k : D.G j) : T ⊗[R] (R ⊗[S] A j.val) := (1 : T) ⊗ₜ[R] gR j k
  have hgR (j : ProperKernelIndex (K :=
    K) f) := @tensor_kernel_generators.{u} S R (A j.val) (B j.val) (D.G j)
    inferInstance inferInstance (hA j.val) (hB j.val)
    inferInstance (hSA j.val) (hSB j.val) (f j.val) (hf j.val) (D.g j) (D.hg j) (D.fR j.val)
      (gR j) (D.eR j.val) rfl
  have hgT (j : ProperKernelIndex (K := K) f) := @tensor_kernel_generators.{u}
    R T (R ⊗[S] A j.val) (R ⊗[S] B j.val) (D.G j)
    inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance (D.fR j.val) (D.hfR j.val) (gR j) (hgR j)
    (D.fT j.val) (gT j) (D.eT j.val) rfl
  let sT (j : ProperKernelIndex (K :=
    K) f) (k : D.G j) : T ⊗[R] (R ⊗[S] A j.val) := (1 : T) ⊗ₜ[R] D.sR j k
  have heqT (j : ProperKernelIndex (K := K) f) (k : D.G j) := @map_power_membership.{u}
    (R ⊗[S] A j.val) (T ⊗[R] (R ⊗[S] A j.val)) inferInstance inferInstance
    (Algebra.TensorProduct.includeRight :
      R ⊗[S] A j.val →ₐ[R] T ⊗[R] (R ⊗[S] A j.val)).toRingHom
    ((I j.val).map (Algebra.TensorProduct.includeRight : A j.val →ₐ[S] R ⊗[S] A j.val).toRingHom)
    (tensorIdeal (S :=
      S) (R := R) (T := T) (I j.val)) rfl (D.sR j k) (gR j k) (D.n j k) (sT j k) (gT j k)
      rfl rfl (D.heqR j k)
  have hproperR (j : ProperKernelIndex (K :=
    K) f) := @tensor_cancel_kernel_ne_top.{u} S R K (A j.val) (B j.val)
    inferInstance inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance (hSA j.val) (hSB j.val)
    (f j.val) (D.fR j.val) (D.eR j.val) j.property
  have hproperT (j : ProperKernelIndex (K := K) f) := @tensor_cancel_kernel_ne_top.{u}
    R T K (R ⊗[S] A j.val) (R ⊗[S] B j.val)
    inferInstance inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (D.fR j.val) (D.fT j.val) (D.eT j.val) (hproperR j)
  have hsT (j : ProperKernelIndex (K := K) f) (k : D.G j) := @tensor_cancel_not_nilpotent.{u}
    R T K (R ⊗[S] B j.val) inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance inferInstance
    ((D.fR j.val) (D.sR j k)) ((D.fT j.val) (sT j k))
    (by rw [D.eT j.val]; rfl) (D.hsR j k)
  have result := @exists_minimalPrime_open.{u} K hK T (ProperKernelIndex (K := K) f)
    (by dsimp [ProperKernelIndex]; infer_instance)
    (fun j => T ⊗[R] (R ⊗[S] A j.val)) (fun j => T ⊗[R] (R ⊗[S] B j.val))
    (fun _ => inferInstance) (fun _ => inferInstance)
    (fun _ => inferInstance) (fun _ => inferInstance) (fun _ => inferInstance)
    D.G D.finiteG (fun j => D.fT j.val) (fun j => D.hfT j.val) gT hgT (fun j => tensorIdeal
      (S := S) (R := R) (T := T) (I j.val)) (fun j => D.hIT j.val) sT D.n heqT hproperT hsT
  exact result

end FrobeniusSplitting
