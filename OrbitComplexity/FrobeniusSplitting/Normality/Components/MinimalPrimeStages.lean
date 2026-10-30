import OrbitComplexity.FrobeniusSplitting.Normality.Components.IdealMembershipStages
import OrbitComplexity.FrobeniusSplitting.Normality.Components.PrimeWitnesses
import OrbitComplexity.FrobeniusSplitting.Normality.Images.ChosenGraph
import Mathlib.RingTheory.TensorProduct.Maps

/-! # Finite coefficient stages for minimal-prime witnesses

Scalar maps carry the original ideals and power equations to the same
tensor models. Tensor cancellation compares the field equations with
the quotient classes used to retain them.
-/

set_option autoImplicit false

open scoped TensorProduct

namespace FrobeniusSplitting

universe u v w

private theorem cancel_map_ideal
    {S R T A : Type*} [CommSemiring S] [CommSemiring R] [CommSemiring T] [CommSemiring A]
    [Algebra S R] [Algebra S T] [Algebra R T] [IsScalarTower S R T] [Algebra S A]
    (I : Ideal A) :
    (((I.map (Algebra.TensorProduct.includeRight : A →ₐ[S] R ⊗[S] A).toRingHom).map
      (Algebra.TensorProduct.includeRight :
        R ⊗[S] A →ₐ[R] T ⊗[R] (R ⊗[S] A)).toRingHom).map
      (Algebra.TensorProduct.cancelBaseChange S R T T A).toRingHom) =
        I.map (Algebra.TensorProduct.includeRight : A →ₐ[S] T ⊗[S] A).toRingHom := by
  have hcomp :
      ((Algebra.TensorProduct.cancelBaseChange S R T T A).toRingHom.comp
        (Algebra.TensorProduct.includeRight :
          R ⊗[S] A →ₐ[R] T ⊗[R] (R ⊗[S] A)).toRingHom).comp
          (Algebra.TensorProduct.includeRight : A →ₐ[S] R ⊗[S] A).toRingHom =
        (Algebra.TensorProduct.includeRight : A →ₐ[S] T ⊗[S] A).toRingHom := by
    ext a
    change (Algebra.TensorProduct.cancelBaseChange S R T T A)
      ((1 : T) ⊗ₜ[R] ((1 : R) ⊗ₜ[S] a)) = (1 : T) ⊗ₜ[S] a
    rw [Algebra.TensorProduct.cancelBaseChange_tmul, one_smul]
  simp only [Ideal.map_map]
  congr 1

private theorem cancel_one_tensor
    {S R T A : Type*} [CommRing S] [CommRing R] [CommRing T] [CommRing A]
    [Algebra S R] [Algebra S T] [Algebra R T] [IsScalarTower S R T] [Algebra S A]
    (x : R ⊗[S] A) :
    (Algebra.TensorProduct.cancelBaseChange S R T T A) ((1 : T) ⊗ₜ[R] x) =
      (Algebra.TensorProduct.map (IsScalarTower.toAlgHom S R T) (AlgHom.id S A)) x := by
  induction x using TensorProduct.inductionOn with
  | tmul r a =>
      rw [Algebra.TensorProduct.cancelBaseChange_tmul, Algebra.TensorProduct.map_tmul]
      change (r • (1 : T)) ⊗ₜ[S] a = (algebraMap R T r) ⊗ₜ[S] a
      rw [Algebra.smul_def, mul_one]
  | add x y hx hy =>
      simp only [TensorProduct.tmul_add, map_add, hx, hy]

private theorem scalar_lTensor_apply
    {S R T A B : Type*}
    [CommRing S] [CommRing R] [CommRing T] [CommRing A] [CommRing B]
    [Algebra S R] [Algebra S T] [Algebra S A] [Algebra S B]
    (e : R →ₐ[S] T) (f : A →ₐ[S] B) (x : R ⊗[S] A) :
    (Algebra.TensorProduct.map e (AlgHom.id S B))
        ((Algebra.TensorProduct.lTensor (S := R) R f) x) =
      (Algebra.TensorProduct.lTensor (S := T) T f)
        ((Algebra.TensorProduct.map e (AlgHom.id S A)) x) := by
  induction x using TensorProduct.inductionOn with
  | tmul r a => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem cancel_ideal_membership
    {S R T A : Type*} [CommSemiring S] [CommSemiring R] [CommSemiring T] [CommSemiring A]
    [Algebra S R] [Algebra S T] [Algebra R T] [IsScalarTower S R T] [Algebra S A]
    (I : Ideal A) (x : T ⊗[R] (R ⊗[S] A)) :
    x ∈ (I.map (Algebra.TensorProduct.includeRight : A →ₐ[S] R ⊗[S] A).toRingHom).map
        (Algebra.TensorProduct.includeRight :
          R ⊗[S] A →ₐ[R] T ⊗[R] (R ⊗[S] A)).toRingHom ↔
      (Algebra.TensorProduct.cancelBaseChange S R T T A) x ∈
        I.map (Algebra.TensorProduct.includeRight : A →ₐ[S] T ⊗[S] A).toRingHom := by
  constructor
  · intro h
    have hm := Ideal.mem_map_of_mem
      (Algebra.TensorProduct.cancelBaseChange S R T T A).toRingHom h
    rw [cancel_map_ideal I] at hm
    exact hm
  · intro h
    have hm : (Algebra.TensorProduct.cancelBaseChange S R T T A) x ∈
        (((I.map (Algebra.TensorProduct.includeRight : A →ₐ[S] R ⊗[S] A).toRingHom).map
          (Algebra.TensorProduct.includeRight :
            R ⊗[S] A →ₐ[R] T ⊗[R] (R ⊗[S] A)).toRingHom).map
          (Algebra.TensorProduct.cancelBaseChange S R T T A).toRingHom) := by
      rw [cancel_map_ideal I]
      exact h
    obtain ⟨y, hy, hyx⟩ := (Ideal.mem_map_iff_of_surjective
      (Algebra.TensorProduct.cancelBaseChange S R T T A).toRingHom
      (Algebra.TensorProduct.cancelBaseChange S R T T A).surjective).mp hm
    exact ((Algebra.TensorProduct.cancelBaseChange S R T T A).injective hyx) ▸ hy

private theorem scalar_power_membership
    {S R T A : Type*} [CommRing S] [CommRing R] [CommRing T] [CommRing A]
    [Algebra S R] [Algebra S T] [Algebra R T] [IsScalarTower S R T] [Algebra S A]
    (I : Ideal A) (x : R ⊗[S] A) (a : A) (n : ℕ) :
    (1 : T) ⊗ₜ[R] (x * ((1 : R) ⊗ₜ[S] a) ^ n) ∈
        (I.map (Algebra.TensorProduct.includeRight : A →ₐ[S] R ⊗[S] A).toRingHom).map
          (Algebra.TensorProduct.includeRight :
            R ⊗[S] A →ₐ[R] T ⊗[R] (R ⊗[S] A)).toRingHom ↔
      (Algebra.TensorProduct.map (IsScalarTower.toAlgHom S R T) (AlgHom.id S A)) x *
        ((1 : T) ⊗ₜ[S] a) ^ n ∈
          I.map (Algebra.TensorProduct.includeRight : A →ₐ[S] T ⊗[S] A).toRingHom := by
  rw [@cancel_ideal_membership S R T A
    inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance inferInstance I
    ((1 : T) ⊗ₜ[R] (x * ((1 : R) ⊗ₜ[S] a) ^ n))]
  rw [@cancel_one_tensor S R T A
    inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance inferInstance
    (x * ((1 : R) ⊗ₜ[S] a) ^ n)]
  simp only [map_mul, map_pow, Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply]

private theorem not_nilpotent_image
    {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B)
    (hp : (RingHom.ker f).IsPrime) {s : A} (hs : s ∉ RingHom.ker f) :
    ¬ IsNilpotent (f s) := by
  rintro ⟨n, hn⟩
  apply hs
  apply hp.mem_of_pow_mem n
  change f (s ^ n) = 0
  rw [map_pow, hn]

private theorem not_nilpotent_of_equiv_eq
    {C A B : Type*} [CommRing C] [CommRing A] [CommRing B]
    [Algebra C A] [Algebra C B] (e : A ≃ₐ[C] B)
    (x : A) (y : B) (he : e x = y) (hy : ¬ IsNilpotent y) :
    ¬ IsNilpotent x := by
  intro hx
  exact hy (he ▸ hx.map e.toRingHom)

private theorem scalar_not_nilpotent
    {S R T A B : Type*}
    [CommRing S] [CommRing R] [CommRing T] [CommRing A] [CommRing B]
    [Algebra S R] [Algebra S T] [Algebra R T] [IsScalarTower S R T]
    [Algebra S A] [Algebra S B]
    (f : A →ₐ[S] B) (x : R ⊗[S] A) (y : T ⊗[S] A)
    (heval : (Algebra.TensorProduct.map (IsScalarTower.toAlgHom S R T)
      (AlgHom.id S A)) x = y)
    (hy : ¬ IsNilpotent ((Algebra.TensorProduct.lTensor (S := T) T f) y)) :
    ¬ IsNilpotent ((1 : T) ⊗ₜ[R]
      (Algebra.TensorProduct.lTensor (S := R) R f) x) := by
  have heq :
      (Algebra.TensorProduct.cancelBaseChange S R T T B)
        ((1 : T) ⊗ₜ[R] (Algebra.TensorProduct.lTensor (S := R) R f) x) =
      (Algebra.TensorProduct.lTensor (S := T) T f) y := by
    exact (@cancel_one_tensor S R T B
      inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance inferInstance inferInstance
      ((Algebra.TensorProduct.lTensor (S := R) R f) x)).trans
        ((@scalar_lTensor_apply S R T A B
          inferInstance inferInstance inferInstance inferInstance inferInstance
          inferInstance inferInstance inferInstance inferInstance
          (IsScalarTower.toAlgHom S R T) f x).trans
            (congrArg (Algebra.TensorProduct.lTensor (S := T) T f) heval))
  exact @not_nilpotent_of_equiv_eq T (T ⊗[R] (R ⊗[S] B)) (T ⊗[S] B)
    inferInstance inferInstance inferInstance inferInstance inferInstance
    (Algebra.TensorProduct.cancelBaseChange S R T T B)
    ((1 : T) ⊗ₜ[R] (Algebra.TensorProduct.lTensor (S := R) R f) x)
    ((Algebra.TensorProduct.lTensor (S := T) T f) y) heq hy

private theorem coefficient_power_membership
    {K : Type u} [Field K] (S R T : Subalgebra ℤ K)
    (hSR : S ≤ R) (hRT : R ≤ T) (hST : S ≤ T) :
    letI : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
    letI : Algebra R T := (Subalgebra.inclusion hRT).toAlgebra
    letI : Algebra S T := (Subalgebra.inclusion hST).toAlgebra
    letI : IsScalarTower S R T := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    ∀ {A : Type u} [CommRing A] [Algebra S A]
      (I : Ideal A) (x : R ⊗[S] A) (a : A) (n : ℕ),
      (1 : T) ⊗ₜ[R] (x * ((1 : R) ⊗ₜ[S] a) ^ n) ∈
          (I.map (Algebra.TensorProduct.includeRight : A →ₐ[S] R ⊗[S] A).toRingHom).map
            (Algebra.TensorProduct.includeRight :
              R ⊗[S] A →ₐ[R] T ⊗[R] (R ⊗[S] A)).toRingHom ↔
        (Algebra.TensorProduct.map (IsScalarTower.toAlgHom S R T) (AlgHom.id S A)) x *
          ((1 : T) ⊗ₜ[S] a) ^ n ∈
            I.map (Algebra.TensorProduct.includeRight : A →ₐ[S] T ⊗[S] A).toRingHom := by
  let : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
  let : Algebra R T := (Subalgebra.inclusion hRT).toAlgebra
  let : Algebra S T := (Subalgebra.inclusion hST).toAlgebra
  let : IsScalarTower S R T := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  intro A hA hSA I x a n
  exact @scalar_power_membership S R T A
    inferInstance inferInstance inferInstance hA
    inferInstance inferInstance inferInstance inferInstance hSA I x a n

/-- The finite generators of the original kernels admit power-membership
witnesses on one coefficient enlargement. Their multiplier images are
nonnilpotent over the original field, in the same tensor target rings. -/
private theorem witnesses_of_presentation
    {K : Type u} [hK : Field K] (S : Subalgebra ℤ K) (hS : S.FG)
    {J : Type u} [hJ : Finite J] (A B : J → Type u)
    [hA : ∀ j, CommRing (A j)] [hSA : ∀ j, Algebra S (A j)]
    [hB : ∀ j, CommRing (B j)] [hSB : ∀ j, Algebra S (B j)]
    (vars rels G : J → Type u)
    [hvars : ∀ j, Finite (vars j)] [hrels : ∀ j, Finite (rels j)]
    [hG : ∀ j, Finite (G j)]
    (Q : ∀ j, Algebra.Presentation S (A j) (vars j) (rels j))
    (f : ∀ j, A j →ₐ[S] B j) (g : ∀ j, G j → A j)
    (hg : ∀ j, Ideal.span (Set.range (g j)) = RingHom.ker (f j).toRingHom)
    (I : ∀ j, Ideal (A j))
    (hminimal : ∀ j,
      RingHom.ker (Algebra.TensorProduct.lTensor (S := K) K (f j)).toRingHom ∈
        ((I j).map
          (Algebra.TensorProduct.includeRight : A j →ₐ[S] K ⊗[S] A j).toRingHom).minimalPrimes) :
    ∃ (R : Subalgebra ℤ K) (hSR : S ≤ R),
      letI : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
      letI : IsScalarTower S R K := Subalgebra.inclusion.isScalarTower_right hSR K
      R.FG ∧ ∃ (s : ∀ j, G j → R ⊗[S] A j) (n : ∀ j, G j → ℕ),
        (∀ j k, s j k * ((1 : R) ⊗ₜ[S] g j k) ^ n j k ∈
          (I j).map
            (Algebra.TensorProduct.includeRight : A j →ₐ[S] R ⊗[S] A j).toRingHom) ∧
        ∀ j k, ¬ IsNilpotent
          ((1 : K) ⊗ₜ[R] (Algebra.TensorProduct.lTensor (S := R) R (f j)) (s j k)) := by
  classical
  have hgK (j : J) (k : G j) :
      (1 : K) ⊗ₜ[S] g j k ∈
        RingHom.ker (Algebra.TensorProduct.lTensor (S := K) K (f j)).toRingHom := by
    have hmem : g j k ∈ RingHom.ker (f j).toRingHom := by
      rw [← hg j]
      exact Ideal.subset_span (Set.mem_range_self k)
    have hzero : (f j) (g j k) = 0 := hmem
    change (1 : K) ⊗ₜ[S] (f j) (g j k) = 0
    rw [hzero, TensorProduct.tmul_zero]
  have hw (j : J) (k : G j) :
      ∃ s : K ⊗[S] A j,
        s ∉ RingHom.ker (Algebra.TensorProduct.lTensor (S := K) K (f j)).toRingHom ∧
        ∃ n : ℕ, s * ((1 : K) ⊗ₜ[S] g j k) ^ n ∈
          (I j).map
            (Algebra.TensorProduct.includeRight : A j →ₐ[S] K ⊗[S] A j).toRingHom :=
    exists_mul_pow_mem_minimalPrime (hminimal j) (hgK j k)
  choose sK hsK n hmemK using hw
  have graph :=
    @exists_chosen_graph_elements.{u, u, 0, u, u} K hK S hS J Empty hJ
      inferInstance A (fun j => K ⊗[S] A j) hA hSA
      (fun j => inferInstance) (fun j => inferInstance)
      (fun j => AlgEquiv.refl) vars rels hvars hrels Q
      Empty.elim Empty.elim (fun e => Empty.elim e) G hG sK
  obtain ⟨R, hSR, _, hR, _, hlift⟩ := graph
  let algSR : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
  let towerSRK : IsScalarTower S R K := Subalgebra.inclusion.isScalarTower_right hSR K
  choose sR hsR using hlift
  have heval (j : J) (k : G j) :
      (Algebra.TensorProduct.map (IsScalarTower.toAlgHom S R K) (AlgHom.id S (A j)))
        (sR j k) = sK j k := hsR j k
  let powers (i : Sigma G) : R ⊗[S] A i.1 :=
    sR i.1 i.2 * ((1 : R) ⊗ₜ[S] g i.1 i.2) ^ n i.1 i.2
  have hrelations (i : Sigma G) :
      (1 : K) ⊗ₜ[R] powers i ∈
        ((I i.1).map
          (Algebra.TensorProduct.includeRight : A i.1 →ₐ[S] R ⊗[S] A i.1).toRingHom).map
          (Algebra.TensorProduct.includeRight :
            R ⊗[S] A i.1 →ₐ[R] K ⊗[R] (R ⊗[S] A i.1)).toRingHom := by
    apply (@scalar_power_membership.{u, u, u, u} S R K (A i.1)
      inferInstance inferInstance inferInstance (hA i.1)
      algSR inferInstance inferInstance towerSRK (hSA i.1)
      (I i.1) (sR i.1 i.2) (g i.1 i.2) (n i.1 i.2)).mpr
    rw [heval]
    exact hmemK i.1 i.2
  have retained :=
    @exists_retained_ideal_membership.{u, u, u} K hK R hR (Sigma G)
      inferInstance (fun i => R ⊗[S] A i.1)
      (fun i => inferInstance) (fun i => inferInstance)
      (fun i => (I i.1).map
        (Algebra.TensorProduct.includeRight : A i.1 →ₐ[S] R ⊗[S] A i.1).toRingHom)
      powers hrelations
  obtain ⟨T, hRT, hT, hrelationsT⟩ := retained
  let hST : S ≤ T := hSR.trans hRT
  let algRT : Algebra R T := (Subalgebra.inclusion hRT).toAlgebra
  let algST : Algebra S T := (Subalgebra.inclusion hST).toAlgebra
  let towerSTK : IsScalarTower S T K := Subalgebra.inclusion.isScalarTower_right hST K
  let towerSRT : IsScalarTower S R T := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let sT (j : J) (k : G j) : T ⊗[S] A j :=
    (Algebra.TensorProduct.map (IsScalarTower.toAlgHom S R T) (AlgHom.id S (A j))) (sR j k)
  have hcoeff :
      (IsScalarTower.toAlgHom S T K).comp (IsScalarTower.toAlgHom S R T) =
        IsScalarTower.toAlgHom S R K := by
    ext r
    rfl
  have hevalT (j : J) (k : G j) :
      (Algebra.TensorProduct.map (IsScalarTower.toAlgHom S T K) (AlgHom.id S (A j)))
        (sT j k) = sK j k := by
    have hm :
        (Algebra.TensorProduct.map (IsScalarTower.toAlgHom S T K) (AlgHom.id S (A j))).comp
            (Algebra.TensorProduct.map (IsScalarTower.toAlgHom S R T) (AlgHom.id S (A j))) =
          Algebra.TensorProduct.map (IsScalarTower.toAlgHom S R K) (AlgHom.id S (A j)) := by
      rw [← Algebra.TensorProduct.map_comp]
      change Algebra.TensorProduct.map
        ((IsScalarTower.toAlgHom S T K).comp (IsScalarTower.toAlgHom S R T))
          (AlgHom.id S (A j)) = _
      rw [hcoeff]
    exact (AlgHom.congr_fun hm (sR j k)).trans (heval j k)
  refine ⟨T, hST, hT, sT, n, ?_, ?_⟩
  · intro j k
    have hiff := @coefficient_power_membership.{u} K hK S R T hSR hRT hST
      (A j) (hA j) (hSA j) (I j) (sR j k) (g j k) (n j k)
    have hrelation := hrelationsT ⟨j, k⟩
    exact hiff.mp hrelation
  · intro j k
    exact @scalar_not_nilpotent.{u, u, u, u, u} S T K (A j) (B j)
      inferInstance inferInstance inferInstance (hA j) (hB j)
      algST inferInstance inferInstance towerSTK (hSA j) (hSB j)
      (f j) (sT j k) (sK j k) (hevalT j k)
      (@not_nilpotent_image.{u, u} (K ⊗[S] A j) (K ⊗[S] B j)
        inferInstance inferInstance
        (Algebra.TensorProduct.lTensor (S := K) K (f j)).toRingHom
        (hminimal j).isPrime (sK j k) (hsK j k))

/-- Finite kernel generators and their power-membership witnesses can be
chosen together on one coefficient enlargement. The multiplier images
remain nonnilpotent over the original field. -/
theorem exists_minimalPrime_witness_stage
    {K : Type u} [hK : Field K] (S : Subalgebra ℤ K) (hS : S.FG)
    {J : Type u} [hJ : Finite J] (A B : J → Type u)
    [hA : ∀ j, CommRing (A j)] [hSA : ∀ j, Algebra S (A j)]
    [hAFP : ∀ j, Algebra.FinitePresentation S (A j)]
    [hB : ∀ j, CommRing (B j)] [hSB : ∀ j, Algebra S (B j)]
    (f : ∀ j, A j →ₐ[S] B j) (I : ∀ j, Ideal (A j))
    (hminimal : ∀ j,
      RingHom.ker (Algebra.TensorProduct.lTensor (S := K) K (f j)).toRingHom ∈
        ((I j).map
          (Algebra.TensorProduct.includeRight : A j →ₐ[S] K ⊗[S] A j).toRingHom).minimalPrimes) :
    ∃ (G : J → Type u) (_ : ∀ j, Finite (G j)) (g : ∀ j, G j → A j),
      (∀ j, Ideal.span (Set.range (g j)) = RingHom.ker (f j).toRingHom) ∧
      ∃ (R : Subalgebra ℤ K) (hSR : S ≤ R),
        letI : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
        letI : IsScalarTower S R K := Subalgebra.inclusion.isScalarTower_right hSR K
        R.FG ∧ ∃ (s : ∀ j, G j → R ⊗[S] A j) (n : ∀ j, G j → ℕ),
          (∀ j k, s j k * ((1 : R) ⊗ₜ[S] g j k) ^ n j k ∈
            (I j).map
              (Algebra.TensorProduct.includeRight : A j →ₐ[S] R ⊗[S] A j).toRingHom) ∧
          ∀ j k, ¬ IsNilpotent
            ((1 : K) ⊗ₜ[R] (Algebra.TensorProduct.lTensor (S := R) R (f j)) (s j k)) := by
  classical
  let : Algebra.FiniteType ℤ S := (Subalgebra.fg_iff_finiteType S).mp hS
  let : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing ℤ S
  let : ∀ j, IsNoetherianRing (A j) := fun j => Algebra.FiniteType.isNoetherianRing S (A j)
  choose t ht using fun j => (RingHom.ker (f j).toRingHom).fg_of_isNoetherianRing
  let G (j : J) := ↥(t j)
  let g (j : J) (k : G j) : A j := k.val
  have hg (j : J) : Ideal.span (Set.range (g j)) = RingHom.ker (f j).toRingHom := by
    have hrange : Set.range (g j) = (t j : Set (A j)) := by
      ext x
      constructor
      · rintro ⟨y, rfl⟩
        exact y.property
      · intro hx
        exact ⟨⟨x, hx⟩, rfl⟩
    rw [hrange]
    exact ht j
  let vars (j : J) := ULift.{u} (Fin (Algebra.Presentation.ofFinitePresentationVars S (A j)))
  let rels (j : J) := ULift.{u} (Fin (Algebra.Presentation.ofFinitePresentationRels S (A j)))
  let Q (j : J) : Algebra.Presentation S (A j) (vars j) (rels j) :=
    (Algebra.Presentation.ofFinitePresentation S (A j)).reindex Equiv.ulift Equiv.ulift
  refine ⟨G, (fun _ => inferInstance), g, hg, ?_⟩
  exact @witnesses_of_presentation.{u} K hK S hS J hJ A B hA hSA hB hSB
    vars rels G (fun _ => inferInstance) (fun _ => inferInstance) (fun _ => inferInstance)
    Q f g hg I hminimal

end FrobeniusSplitting
