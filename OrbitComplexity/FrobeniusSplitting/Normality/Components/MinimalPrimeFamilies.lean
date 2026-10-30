import OrbitComplexity.FrobeniusSplitting.Normality.Components.MinimalPrimeStages
import OrbitComplexity.FrobeniusSplitting.Normality.Components.IdealContainmentStages
import OrbitComplexity.FrobeniusSplitting.Normality.Connectedness.CoefficientAwayStage
import OrbitComplexity.FrobeniusSplitting.Normality.Components.MinimalPrimeFibres
import Batteries.Tactic.OpenPrivate

/-! # Coefficient stages for finite families of components

Unit kernels and kernels minimal over specified ideals retain those
alternatives on every field fibre after one coefficient enlargement.
The algebras and maps remain the original scalar-extension family.
-/

set_option autoImplicit false

open scoped TensorProduct

namespace FrobeniusSplitting

universe u

open private cancel_ideal_membership from
  OrbitComplexity.FrobeniusSplitting.Normality.Components.MinimalPrimeStages
open private scalar_kernel from
  OrbitComplexity.FrobeniusSplitting.Normality.Components.IdealContainmentStages
open private tensor_cancel_kernel tensor_cancel_minimalPrime tensor_cancel_prime_or_top from
  OrbitComplexity.FrobeniusSplitting.Normality.Components.TensorPrimeWitnesses

private theorem retained_tensor_kernel_le
    {K : Type u} [hK : Field K] (S R : Subalgebra ℤ K) (hR : R.FG)
    {J : Type u} [hJ : Finite J] (A B : J → Type u)
    [hA : ∀ j, CommRing (A j)] [hSA : ∀ j, Algebra S (A j)]
    [∀ j, Algebra.FinitePresentation S (A j)]
    [hB : ∀ j, CommRing (B j)] [hSB : ∀ j, Algebra S (B j)]
    [Algebra S R]
    (fR : ∀ j, R ⊗[S] A j →ₐ[R] R ⊗[S] B j)
    (hfR : ∀ j, Function.Surjective (fR j))
    (IretR : ∀ j, Ideal (R ⊗[S] A j))
    (hleKR : ∀ j, (IretR j).map
      (Algebra.TensorProduct.includeRight : R ⊗[S] A j →ₐ[R] K ⊗[R] (R ⊗[S] A j)).toRingHom ≤
      RingHom.ker (Algebra.TensorProduct.lTensor (S := K) K (fR j)).toRingHom) :
    ∃ (T : Subalgebra ℤ K) (hRT : R ≤ T),
      letI : Algebra R T := (Subalgebra.inclusion hRT).toAlgebra
      letI : IsScalarTower R T K := Subalgebra.inclusion.isScalarTower_right hRT K
      T.FG ∧ ∀ j, (IretR j).map
        (Algebra.TensorProduct.includeRight :
          R ⊗[S] A j →ₐ[R] T ⊗[R] (R ⊗[S] A j)).toRingHom ≤
        RingHom.ker (Algebra.TensorProduct.lTensor (S := T) T (fR j)).toRingHom := by
  let : Algebra.FiniteType ℤ R := (Subalgebra.fg_iff_finiteType R).mp hR
  let : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing ℤ R
  let : ∀ j, IsNoetherianRing (R ⊗[S] A j) :=
    fun j => Algebra.FiniteType.isNoetherianRing R (R ⊗[S] A j)
  exact @exists_retained_kernel_le.{u}
    K hK R hR J hJ (fun j => R ⊗[S] A j) (fun j => R ⊗[S] B j)
    (fun _ => inferInstance) (fun _ => inferInstance)
    (fun _ => inferInstance) (fun _ => inferInstance)
    fR hfR IretR (fun j => (IretR j).fg_of_isNoetherianRing) hleKR

private theorem tensor_witness_data
    {K : Type u} [Field K] (S R T : Subalgebra ℤ K)
    {J : Type u} (A B : J → Type u)
    [∀ j, CommRing (A j)] [∀ j, Algebra S (A j)]
    [∀ j, CommRing (B j)] [∀ j, Algebra S (B j)]
    [Algebra S R] [IsScalarTower S R K]
    [Algebra R T] [IsScalarTower R T K]
    (f : ∀ j, A j →ₐ[S] B j) (I : ∀ j, Ideal (A j))
    (fR : ∀ j, R ⊗[S] A j →ₐ[R] R ⊗[S] B j)
    (eR : ∀ j, fR j = Algebra.TensorProduct.lTensor (S := R) R (f j))
    (hfR : ∀ j, Function.Surjective (fR j))
    (fT : ∀ j, T ⊗[R] (R ⊗[S] A j) →ₐ[T] T ⊗[R] (R ⊗[S] B j))
    (eT : ∀ j, fT j = Algebra.TensorProduct.lTensor (S := T) T (fR j))
    (hfT : ∀ j, Function.Surjective (fT j))
    (hIT : ∀ j, kernelContains (fT j) (tensorIdeal (S := S) (R := R) (T := T) (I j)))
    (hunitT : ∀ j,
    tensorKernelUnit (S := S) K (f j) → kernelUnit (fT j))
    (G : ProperKernelIndex (K := K) f → Type u)
    (finiteG : ∀ j, Finite (G j))
    (g : ∀ j, G j → A j.val)
    (hg : ∀ j, Ideal.span (Set.range (g j)) = RingHom.ker (f j.val).toRingHom)
    (sR : ∀ j, G j → R ⊗[S] A j.val)
    (n : ∀ j, G j → ℕ)
    (heqR : ∀ j k, sR j k * ((1 : R) ⊗ₜ[S] g j k) ^ n j k ∈
    (I j.val).map (Algebra.TensorProduct.includeRight :
      A j.val →ₐ[S] R ⊗[S] A j.val).toRingHom)
    (hsR : ∀ j k, ¬ IsNilpotent ((1 : K) ⊗ₜ[R] (fR j.val) (sR j k))) :
    Nonempty (TensorWitnessData (R := R) T A B f I) := by
  exact ⟨{
    fR := fR
    eR := eR
    hfR := hfR
    fT := fT
    eT := eT
    hfT := hfT
    hIT := hIT
    hunitT := hunitT
    G := G
    finiteG := finiteG
    g := g
    hg := hg
    sR := sR
    n := n
    heqR := heqR
    hsR := hsR
  }⟩

private theorem prepare_tensor_witnesses
    {K : Type u} [hK : Field K] (S : Subalgebra ℤ K) (hS : S.FG)
    {J : Type u} [hJ : Finite J] (A B : J → Type u)
    [hA : ∀ j, CommRing (A j)] [hSA : ∀ j, Algebra S (A j)]
    [hAFP : ∀ j, Algebra.FinitePresentation S (A j)]
    [hB : ∀ j, CommRing (B j)] [hSB : ∀ j, Algebra S (B j)]
    (f : ∀ j, A j →ₐ[S] B j) (hf : ∀ j, Function.Surjective (f j))
    (I : ∀ j, Ideal (A j))
    (hcomponent : ∀ j,
      RingHom.ker (Algebra.TensorProduct.lTensor (S := K) K (f j)).toRingHom = ⊤ ∨
      RingHom.ker (Algebra.TensorProduct.lTensor (S := K) K (f j)).toRingHom ∈
        ((I j).map (Algebra.TensorProduct.includeRight : A j →ₐ[S] K ⊗[S] A
          j).toRingHom).minimalPrimes) :
    ∃ (R : Subalgebra ℤ K) (hSR : S ≤ R),
      letI : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
      letI : IsScalarTower S R K := Subalgebra.inclusion.isScalarTower_right hSR K
      ∃ (T : Subalgebra ℤ K) (hRT : R ≤ T),
        letI : Algebra R T := (Subalgebra.inclusion hRT).toAlgebra
        letI : IsScalarTower R T K := Subalgebra.inclusion.isScalarTower_right hRT K
        T.FG ∧ Nonempty (TensorWitnessData (R := R) T A B f I) := by
  classical
  let Jp := ProperKernelIndex (K := K) f
  have hminimal (j : Jp) := (hcomponent j.val).resolve_left j.property
  obtain ⟨G, hG, g, hg, R, hSR, hR, sR, n, heqR, hsR⟩ :=
    @exists_minimalPrime_witness_stage.{u} K hK S hS Jp
      (by dsimp [Jp, ProperKernelIndex]; infer_instance)
      (fun j => A j.val) (fun j => B j.val)
      (fun j => hA j.val) (fun j => hSA j.val) (fun j => hAFP j.val)
      (fun j => hB j.val) (fun j => hSB j.val)
      (fun j => f j.val) (fun j => I j.val) hminimal
  let algSR : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
  let towerSRK : IsScalarTower S R K := Subalgebra.inclusion.isScalarTower_right hSR K
  let fR (j : J) := Algebra.TensorProduct.lTensor (S := R) R (f j)
  have hfR (j : J) : Function.Surjective (fR j) :=
    Algebra.TensorProduct.map_surjective (AlgHom.id R R) (f j) Function.surjective_id (hf j)
  let Iret (j : J) : Ideal (A j) :=
    if RingHom.ker (Algebra.TensorProduct.lTensor (S := K) K (f j)).toRingHom = ⊤ then ⊤ else I j
  let IretR (j : J) := (Iret j).map
    (Algebra.TensorProduct.includeRight : A j →ₐ[S] R ⊗[S] A j).toRingHom
  have hleK (j : J) : (Iret j).map
      (Algebra.TensorProduct.includeRight : A j →ₐ[S] K ⊗[S] A j).toRingHom ≤
      RingHom.ker (Algebra.TensorProduct.lTensor (S := K) K (f j)).toRingHom := by
    rcases hcomponent j with htop | hmin
    · dsimp only [Iret]
      rw [ite_eq_left htop, Ideal.map_top]
      exact htop.ge
    · have hne := hmin.isPrime.ne_top
      dsimp only [Iret]
      rw [ite_eq_right hne]
      exact hmin.le
  have hleKR (j : J) : (IretR j).map
      (Algebra.TensorProduct.includeRight : R ⊗[S] A j →ₐ[R] K ⊗[R] (R ⊗[S] A j)).toRingHom ≤
      RingHom.ker (Algebra.TensorProduct.lTensor (S := K) K (fR j)).toRingHom := by
    have inclusion := @tensor_cancel_kernel_le.{u} S R K (A j) (B j)
      (inferInstanceAs (CommSemiring S)) (inferInstanceAs (CommSemiring R))
      (inferInstanceAs (CommSemiring K)) (inferInstanceAs (CommSemiring (A j)))
        (inferInstanceAs (CommSemiring (B j)))
      algSR (inferInstanceAs (Algebra S K)) (inferInstanceAs (Algebra R K))
      towerSRK (hSA j) (hSB j) (f j) (Iret j) (fR j) (IretR j) rfl rfl (hleK j)
    exact inclusion
  obtain ⟨T, hRT, hT, hleT⟩ := @retained_tensor_kernel_le.{u}
    K hK S R hR J hJ A B hA hSA hAFP hB hSB algSR fR hfR IretR hleKR
  let algRT : Algebra R T := (Subalgebra.inclusion hRT).toAlgebra
  let towerRTK : IsScalarTower R T K := Subalgebra.inclusion.isScalarTower_right hRT K
  let fT (j : J) := Algebra.TensorProduct.lTensor (S := T) T (fR j)
  have hfT (j : J) : Function.Surjective (fT j) :=
    Algebra.TensorProduct.map_surjective (AlgHom.id T T) (fR j) Function.surjective_id (hfR j)
  have hIT (j : J) : kernelContains (fT j) (tensorIdeal (S := S) (R := R) (T := T) (I j)) := by
    dsimp only [kernelContains, tensorIdeal]
    apply le_trans (Ideal.map_mono (Ideal.map_mono (show I j ≤ Iret j from ?_))) (hleT j)
    by_cases htop : RingHom.ker (Algebra.TensorProduct.lTensor (S := K) K (f j)).toRingHom = ⊤
    · simp only [Iret, ite_eq_left htop]
      exact le_top
    · simp only [Iret, ite_eq_right htop]
      exact le_rfl
  have hunitT (j : J)
      (htop : tensorKernelUnit (S := S) K (f j)) : kernelUnit (fT j) := by
    change RingHom.ker (Algebra.TensorProduct.lTensor (S := K) K (f j)).toRingHom = ⊤ at htop
    change RingHom.ker (fT j).toRingHom = ⊤
    apply top_le_iff.mp
    simpa only [IretR, Iret, ite_eq_left htop, Ideal.map_top] using hleT j
  refine ⟨R, hSR, T, hRT, hT, ?_⟩
  exact @tensor_witness_data.{u} K hK S R T J A B hA hSA hB hSB
    algSR towerSRK algRT towerRTK f I fR (fun _ => rfl) hfR fT (fun _ => rfl) hfT
    hIT hunitT G hG g hg sR n heqR hsR


private theorem unit_fibre_from_tensor
    {K : Type u} [Field K] {S R : Type u} [CommRing S] [CommRing R]
    (T : Subalgebra ℤ K) {J : Type u} (A B : J → Type u)
    [hA : ∀ j, CommRing (A j)] [hSA : ∀ j, Algebra S (A j)]
    [hB : ∀ j, CommRing (B j)] [hSB : ∀ j, Algebra S (B j)]
    [Algebra S R] [Algebra S K] [Algebra R K] [IsScalarTower S R K]
    [Algebra R T] [IsScalarTower R T K]
    (f : ∀ j, A j →ₐ[S] B j) (I : ∀ j, Ideal (A j))
    (D : TensorWitnessData (R := R) T A B f I)
    {L : Type u} [Field L] [Algebra S L] [Algebra R L] [Algebra T L]
    [IsScalarTower S R L] [IsScalarTower R T L]
    (j : J)
    (htop : RingHom.ker (Algebra.TensorProduct.lTensor (S := K) K (f j)).toRingHom = ⊤) :
    RingHom.ker (Algebra.TensorProduct.lTensor (S := L) L (f j)).toRingHom = ⊤ := by
  have htopT := D.hunitT j htop
  have htopL : RingHom.ker (Algebra.TensorProduct.lTensor (S := L) L (D.fT j)).toRingHom = ⊤ := by
    rw [@scalar_kernel.{u} T L (T ⊗[R] (R ⊗[S] A j)) (T ⊗[R] (R ⊗[S] B j))
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
        inferInstance
      (D.fT j) (D.hfT j), htopT, Ideal.map_top]
  rw [D.eT j, @tensor_cancel_kernel.{u} R T L (R ⊗[S] A j) (R ⊗[S] B j)
    inferInstance inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
      (D.fR j)] at htopL
  have htopR := (Ideal.comap_eq_top_iff
    (f := (Algebra.TensorProduct.cancelBaseChange R T L L (R ⊗[S] A j)).toRingHom)).mp htopL
  rw [D.eR j, @tensor_cancel_kernel.{u} S R L (A j) (B j)
    inferInstance inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance (hSA j) (hSB j) (f j)] at htopR
  exact (Ideal.comap_eq_top_iff
    (f := (Algebra.TensorProduct.cancelBaseChange S R L L (A j)).toRingHom)).mp htopR

private theorem minimal_fibre_from_tensor
    {K : Type u} [Field K] {S R : Type u} [CommRing S] [CommRing R]
    (T : Subalgebra ℤ K) {J : Type u} (A B : J → Type u)
    [hA : ∀ j, CommRing (A j)] [hSA : ∀ j, Algebra S (A j)]
    [hB : ∀ j, CommRing (B j)] [hSB : ∀ j, Algebra S (B j)]
    [Algebra S R] [Algebra S K] [Algebra R K] [IsScalarTower S R K]
    [Algebra R T] [IsScalarTower R T K]
    (f : ∀ j, A j →ₐ[S] B j) (I : ∀ j, Ideal (A j))
    (D : TensorWitnessData (R := R) T A B f I)
    {L : Type u} [Field L] [Algebra S L] [Algebra R L] [Algebra T L]
    [IsScalarTower S R L] [IsScalarTower R T L]
    (j : J)
    (hminimalT : RingHom.ker (Algebra.TensorProduct.lTensor (S := L) L (D.fT j)).toRingHom ∈
      ((tensorIdeal (S := S) (R := R) (T := T) (I j)).map (Algebra.TensorProduct.includeRight :
        T ⊗[R] (R ⊗[S] A j) →ₐ[T]
          L ⊗[T] (T ⊗[R] (R ⊗[S] A j))).toRingHom).minimalPrimes) :
    RingHom.ker (Algebra.TensorProduct.lTensor (S := L) L (f j)).toRingHom ∈
      ((I j).map (Algebra.TensorProduct.includeRight : A j →ₐ[S] L ⊗[S] A
        j).toRingHom).minimalPrimes := by
  rw [tensorIdeal, D.eT j] at hminimalT
  have hminimalR := (@tensor_cancel_minimalPrime.{u} R T L (R ⊗[S] A j) (R ⊗[S] B j)
    inferInstance inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (D.fR j) ((I j).map (Algebra.TensorProduct.includeRight : A j →ₐ[S] R ⊗[S] A
      j).toRingHom)).mp hminimalT
  rw [D.eR j] at hminimalR
  exact (@tensor_cancel_minimalPrime.{u} S R L (A j) (B j)
    inferInstance inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance (hSA j) (hSB j) (f j) (I j)).mp
      hminimalR

private theorem fibre_from_tensor_witnesses
    {K : Type u} [hK : Field K] {S R : Type u} [hS : CommRing S] [hR : CommRing R]
    (T : Subalgebra ℤ K) {J : Type u} (A B : J → Type u)
    [hA : ∀ j, CommRing (A j)] [hSA : ∀ j, Algebra S (A j)]
    [hB : ∀ j, CommRing (B j)] [hSB : ∀ j, Algebra S (B j)]
    [hSR : Algebra S R] [hSK : Algebra S K] [hRK : Algebra R K] [hSRK : IsScalarTower S R K]
    [hRT : Algebra R T] [hRTK : IsScalarTower R T K]
    (f : ∀ j, A j →ₐ[S] B j) (I : ∀ j, Ideal (A j))
    (D : TensorWitnessData (R := R) T A B f I)
    {L : Type u} [hL : Field L] [hSL : Algebra S L] [hRL : Algebra R L] [hTL : Algebra T L]
    [hSRL : IsScalarTower S R L] [hRTL : IsScalarTower R T L]
    (hfield : ∀ j : ProperKernelIndex (K := K) f,
      (RingHom.ker (Algebra.TensorProduct.lTensor (S := L) L (D.fT j.val)).toRingHom = ⊤ ∨
        (RingHom.ker (Algebra.TensorProduct.lTensor (S := L) L (D.fT j.val)).toRingHom).IsPrime) →
      RingHom.ker (Algebra.TensorProduct.lTensor (S := L) L (D.fT j.val)).toRingHom ∈
        ((tensorIdeal (S :=
          S) (R := R) (T := T) (I j.val)).map (Algebra.TensorProduct.includeRight :
          T ⊗[R] (R ⊗[S] A j.val) →ₐ[T]
            L ⊗[T] (T ⊗[R] (R ⊗[S] A j.val))).toRingHom).minimalPrimes) :
    ∀ j, (RingHom.ker (Algebra.TensorProduct.lTensor (S := L) L (f j)).toRingHom = ⊤ ∨
      (RingHom.ker (Algebra.TensorProduct.lTensor (S := L) L (f j)).toRingHom).IsPrime) →
      RingHom.ker (Algebra.TensorProduct.lTensor (S := L) L (f j)).toRingHom = ⊤ ∨
      RingHom.ker (Algebra.TensorProduct.lTensor (S := L) L (f j)).toRingHom ∈
        ((I j).map (Algebra.TensorProduct.includeRight : A j →ₐ[S] L ⊗[S] A
          j).toRingHom).minimalPrimes := by
  intro j hp
  by_cases htop : RingHom.ker (Algebra.TensorProduct.lTensor (S := K) K (f j)).toRingHom = ⊤
  · exact Or.inl (@unit_fibre_from_tensor.{u} K hK S R hS hR T J A B hA hSA hB hSB
      hSR hSK hRK hSRK hRT hRTK f I D L hL hSL hRL hTL hSRL hRTL j htop)
  · have hpR : RingHom.ker (Algebra.TensorProduct.lTensor (S := L) L (D.fR j)).toRingHom = ⊤ ∨
        (RingHom.ker (Algebra.TensorProduct.lTensor (S := L) L (D.fR j)).toRingHom).IsPrime := by
      rw [D.eR j]
      exact (@tensor_cancel_prime_or_top.{u} S R L (A j) (B j)
        inferInstance inferInstance inferInstance inferInstance inferInstance
        inferInstance inferInstance inferInstance inferInstance (hSA j) (hSB j) (f j)) hp
    have hpT : RingHom.ker (Algebra.TensorProduct.lTensor (S := L) L (D.fT j)).toRingHom = ⊤ ∨
        (RingHom.ker (Algebra.TensorProduct.lTensor (S := L) L (D.fT j)).toRingHom).IsPrime := by
      rw [D.eT j]
      exact (@tensor_cancel_prime_or_top.{u} R T L (R ⊗[S] A j) (R ⊗[S] B j)
        inferInstance inferInstance inferInstance inferInstance inferInstance
        inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
          (D.fR j)) hpR
    have hminimalT := hfield ⟨j, htop⟩ hpT
    exact Or.inr (@minimal_fibre_from_tensor.{u} K hK S R hS hR T J A B hA hSA hB hSB
      hSR hSK hRK hSRK hRT hRTK f I D L hL hSL hRL hTL hSRL hRTL j hminimalT)

/-- A finite family of kernels which are unit ideals or minimal primes over
specified ideals over the ambient field has the same alternatives on every
field fibre after one coefficient enlargement, provided those fibre kernels
are unit ideals or prime. The coordinate algebras and maps are unchanged. -/
theorem exists_minimalPrime_family_stage
    {K : Type u} [hK : Field K] (S : Subalgebra ℤ K) (hS : S.FG)
    {J : Type u} [hJ : Finite J] (A B : J → Type u)
    [hA : ∀ j, CommRing (A j)] [hSA : ∀ j, Algebra S (A j)]
    [hAFP : ∀ j, Algebra.FinitePresentation S (A j)]
    [hB : ∀ j, CommRing (B j)] [hSB : ∀ j, Algebra S (B j)]
    [hBFP : ∀ j, Algebra.FinitePresentation S (B j)]
    (f : ∀ j, A j →ₐ[S] B j) (hf : ∀ j, Function.Surjective (f j))
    (I : ∀ j, Ideal (A j))
    (hcomponent : ∀ j,
      RingHom.ker (Algebra.TensorProduct.lTensor (S := K) K (f j)).toRingHom = ⊤ ∨
      RingHom.ker (Algebra.TensorProduct.lTensor (S := K) K (f j)).toRingHom ∈
        ((I j).map (Algebra.TensorProduct.includeRight : A j →ₐ[S] K ⊗[S] A
          j).toRingHom).minimalPrimes) :
    ∃ (T : Subalgebra ℤ K) (hST : S ≤ T), T.FG ∧
      ∀ (L : Type u) [Field L] [Algebra T L],
        letI : Algebra S L := ((algebraMap T L).comp
          (Subalgebra.inclusion hST).toRingHom).toAlgebra
        ∀ j, (RingHom.ker (Algebra.TensorProduct.lTensor (S := L) L (f j)).toRingHom = ⊤ ∨
          (RingHom.ker (Algebra.TensorProduct.lTensor (S := L) L (f j)).toRingHom).IsPrime) →
          RingHom.ker (Algebra.TensorProduct.lTensor (S := L) L (f j)).toRingHom = ⊤ ∨
          RingHom.ker (Algebra.TensorProduct.lTensor (S := L) L (f j)).toRingHom ∈
            ((I j).map (Algebra.TensorProduct.includeRight : A j →ₐ[S] L ⊗[S] A
              j).toRingHom).minimalPrimes := by
  classical
  obtain ⟨R, hSR, T, hRT, hT, ⟨D⟩⟩ := @prepare_tensor_witnesses.{u}
    K hK S hS J hJ A B hA hSA hAFP hB hSB f hf I hcomponent
  let algSR : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
  let towerSRK : IsScalarTower S R K := Subalgebra.inclusion.isScalarTower_right hSR K
  let algRT : Algebra R T := (Subalgebra.inclusion hRT).toAlgebra
  let towerRTK : IsScalarTower R T K := Subalgebra.inclusion.isScalarTower_right hRT K
  obtain ⟨r, hr, hfield⟩ := @open_from_tensor_witnesses.{u} K hK S R
    (inferInstanceAs (CommRing S)) (inferInstanceAs (CommRing R)) T J hJ A B
    hA hSA hB hSB hBFP algSR (inferInstanceAs (Algebra S K)) (inferInstanceAs (Algebra R K))
    towerSRK algRT towerRTK f hf I D
  obtain ⟨V, hTV, hV, haway⟩ := @exists_coefficient_away.{u} K hK T hT r hr
  let algTV : Algebra T V := (Subalgebra.inclusion hTV).toAlgebra
  let : IsLocalization.Away r V := haway
  let hSV := hSR.trans (hRT.trans hTV)
  refine ⟨V, hSV, hV, ?_⟩
  intro L hL hVL
  let algTL : Algebra T L := ((algebraMap V L).comp (Subalgebra.inclusion hTV).toRingHom).toAlgebra
  let algRL : Algebra R L := ((algebraMap T L).comp (Subalgebra.inclusion hRT).toRingHom).toAlgebra
  let algSL : Algebra S L := ((algebraMap V L).comp (Subalgebra.inclusion hSV).toRingHom).toAlgebra
  let towerRTL : IsScalarTower R T L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let towerSRL : IsScalarTower S R L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hrL : algebraMap T L r ≠ 0 :=
    ((IsLocalization.Away.algebraMap_isUnit r).map (algebraMap V L)).ne_zero
  exact @fibre_from_tensor_witnesses.{u} K hK S R
    (inferInstanceAs (CommRing S)) (inferInstanceAs (CommRing R)) T J A B hA hSA hB hSB
    algSR (inferInstanceAs (Algebra S K)) (inferInstanceAs (Algebra R K)) towerSRK algRT towerRTK
    f I D L hL algSL algRL algTL towerSRL towerRTL (@hfield L hL algTL hrL)

end FrobeniusSplitting
