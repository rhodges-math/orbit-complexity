import Mathlib.RingTheory.TensorProduct.MonoidAlgebra
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.RingTheory.Adjoin.FG
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.Data.Fintype.Sigma
import Mathlib.RingTheory.FiniteStability
import Mathlib.Algebra.Polynomial.Div

/-!
# Finite models of relative nilpotent polynomial quotients

Finite coefficient enlargement retains a polynomial quotient over a specified
coefficient model, together with its zero section and nilpotence equation.
-/

noncomputable section
namespace FrobeniusSplitting
open scoped Polynomial TensorProduct
universe u v w t

private def polynomialTensor (R : Type u) (K : Type v) (C : Type w)
    [CommRing R] [CommRing K] [CommRing C] [Algebra R K] [Algebra R C] :
    K ⊗[R] Polynomial C ≃ₐ[K] Polynomial (K ⊗[R] C) :=
  ((Algebra.TensorProduct.congr (AlgEquiv.refl : K ≃ₐ[K] K)
    ((Polynomial.toFinsuppIsoAlg C).restrictScalars R)).trans
      (AddMonoidAlgebra.rTensorEquivAlgEquiv R K K C)).trans
        ((Polynomial.toFinsuppIsoAlg (K ⊗[R] C)).symm.restrictScalars K)

private theorem polynomialTensor_coeff (R : Type u) (K : Type v) (C : Type w)
    [CommRing R] [CommRing K] [CommRing C] [Algebra R K] [Algebra R C]
    (k : K) (p : Polynomial C) (n : ℕ) :
    (polynomialTensor R K C (k ⊗ₜ[R] p)).coeff n = k ⊗ₜ[R] p.coeff n := by
  change ((AddMonoidAlgebra.rTensorEquivAlgEquiv R K K C)
    (k ⊗ₜ[R] (Polynomial.toFinsuppIsoAlg C p))).coeff n = _
  rw [AddMonoidAlgebra.rTensorEquiv_tmulAlgEquiv,
    AddMonoidAlgebra.coeff_smul]
  change k • ((AddMonoidAlgebra.mapAlgHom ℕ
    (Algebra.TensorProduct.includeRight : C →ₐ[R] K ⊗[R] C))
      (Polynomial.toFinsuppIsoAlg C p)).coeff n = _
  rw [AddMonoidAlgebra.coeff_mapAlgHom]
  simp only [Algebra.TensorProduct.includeRight_apply, TensorProduct.smul_tmul',
    smul_eq_mul, mul_one]
  rfl

private def coefficientMap (R : Type u) (K : Type v) (D : Type w) (C : Type*)
    [CommRing R] [CommRing K] [CommRing D] [CommRing C]
    [Algebra R K] [Algebra R D] [Algebra K C] [Algebra R C] [IsScalarTower R K C]
    (e : K ⊗[R] D ≃ₐ[K] C) : D →ₐ[R] C :=
  (e.toAlgHom.restrictScalars R).comp Algebra.TensorProduct.includeRight

private def polynomialBaseChange (R : Type u) (K : Type v) (D : Type w) (C : Type*)
    [CommRing R] [CommRing K] [CommRing D] [CommRing C]
    [Algebra R K] [Algebra R D] [Algebra K C]
    (e : K ⊗[R] D ≃ₐ[K] C) : K ⊗[R] D[X] ≃ₐ[K] C[X] :=
  (polynomialTensor R K D).trans (Polynomial.mapAlgEquiv e)

private theorem polynomialBaseChange_tmul (R : Type u) (K : Type v) (D : Type w) (C : Type*)
    [CommRing R] [CommRing K] [CommRing D] [CommRing C]
    [Algebra R K] [Algebra R D] [Algebra K C] [Algebra R C] [IsScalarTower R K C]
    (e : K ⊗[R] D ≃ₐ[K] C) (k : K) (p : D[X]) :
    polynomialBaseChange R K D C e (k ⊗ₜ[R] p) =
      Polynomial.C (algebraMap K C k) * p.map (coefficientMap R K D C e) := by
  ext n
  simp only [polynomialBaseChange, AlgEquiv.trans_apply,
    Polynomial.coe_mapAlgEquiv, Polynomial.coeff_map]
  rw [polynomialTensor_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_map]
  change e (k ⊗ₜ[R] p.coeff n) =
    algebraMap K C k * e (1 ⊗ₜ[R] p.coeff n)
  calc
    e (k ⊗ₜ[R] p.coeff n) = e (k • (1 ⊗ₜ[R] p.coeff n)) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    _ = k • e (1 ⊗ₜ[R] p.coeff n) := e.toLinearEquiv.map_smul _ _
    _ = _ := Algebra.smul_def _ _

private def quotientBaseChange (R : Type u) (K : Type v) (D : Type w) (C A : Type*)
    [CommRing R] [CommRing K] [CommRing D] [CommRing C] [CommRing A]
    [Algebra R K] [Algebra R D] [Algebra K C] [Algebra R C] [IsScalarTower R K C]
    [Algebra C A] [Algebra K A] [IsScalarTower K C A]
    (e : K ⊗[R] D ≃ₐ[K] C) (c : C[X] →ₐ[C] A)
    (hc : Function.Surjective c) {J : Type*} (r : J → D[X]) (s : J → C[X])
    (hs : Ideal.span (Set.range s) = RingHom.ker c.toRingHom)
    (hr : ∀ j, (r j).map (coefficientMap R K D C e) = s j) :
    K ⊗[R] (D[X] ⧸ Ideal.span (Set.range r)) ≃ₐ[K] A := by
  let I := Ideal.span (Set.range r)
  let ep := polynomialBaseChange R K D C e
  have hcomp : ep.toRingHom.comp
      (Algebra.TensorProduct.includeRight : D[X] →ₐ[R] K ⊗[R] D[X]).toRingHom =
      Polynomial.mapRingHom (coefficientMap R K D C e).toRingHom := by
    apply RingHom.ext
    intro p
    change ep (1 ⊗ₜ[R] p) = (p.map (coefficientMap R K D C e))
    rw [polynomialBaseChange_tmul]
    simp
  have hI : RingHom.ker (c.restrictScalars K).toRingHom =
      (I.map (Algebra.TensorProduct.includeRight : D[X] →ₐ[R] K ⊗[R] D[X]).toRingHom).map
        ep.toRingHom := by
    rw [Ideal.map_map, hcomp]
    change RingHom.ker c.toRingHom =
      (Ideal.span (Set.range r)).map (Polynomial.mapRingHom
        (coefficientMap R K D C e).toRingHom)
    rw [Ideal.map_span, ← Set.range_comp]
    change RingHom.ker c.toRingHom =
      Ideal.span (Set.range fun j => (r j).map (coefficientMap R K D C e))
    simpa only [hr] using hs.symm
  exact (Algebra.TensorProduct.tensorQuotientEquiv (R := R) K D[X] K I).trans
    ((Ideal.quotientEquivAlg _ _ ep hI).trans (Ideal.quotientKerAlgEquivOfSurjective hc))

private theorem quotientBaseChange_tmul
    (R : Type u) (K : Type v) (D : Type w) (C A : Type*)
    [CommRing R] [CommRing K] [CommRing D] [CommRing C] [CommRing A]
    [Algebra R K] [Algebra R D] [Algebra K C] [Algebra R C] [IsScalarTower R K C]
    [Algebra C A] [Algebra K A] [IsScalarTower K C A]
    (e : K ⊗[R] D ≃ₐ[K] C) (c : C[X] →ₐ[C] A)
    (hc : Function.Surjective c) {J : Type*} (r : J → D[X]) (s : J → C[X])
    (hs : Ideal.span (Set.range s) = RingHom.ker c.toRingHom)
    (hr : ∀ j, (r j).map (coefficientMap R K D C e) = s j) (k : K) (p : D[X]) :
    quotientBaseChange R K D C A e c hc r s hs hr
      (k ⊗ₜ[R] Ideal.Quotient.mk _ p) =
        algebraMap K A k * c (p.map (coefficientMap R K D C e)) := by
  change c (polynomialBaseChange R K D C e (k ⊗ₜ[R] p)) = _
  rw [polynomialBaseChange_tmul, map_mul]
  congr 1
  exact (c.restrictScalars K).commutes k

private theorem exists_polynomial_lifts {K : Type u} {C₀ : Type v} {C : Type w}
    [Field K] [CommRing C₀] [CommRing C] [Algebra K C]
    (R₀ : Subalgebra ℤ K) [Algebra R₀ C₀]
    (eC : K ⊗[R₀] C₀ ≃ₐ[K] C) {J : Type t} [Finite J] (g : J → Polynomial C)
    (hR₀ : R₀.FG) :
    ∃ (R : Subalgebra ℤ K) (hR₀R : R₀ ≤ R),
      letI : Algebra R₀ R := (Subalgebra.inclusion hR₀R).toAlgebra
      let j : R →ₐ[R₀] K :=
        { toRingHom := R.val.toRingHom, commutes' := fun _ => rfl }
      let η := ((eC.toAlgHom.restrictScalars R₀).comp
        (Algebra.TensorProduct.map j (AlgHom.id R₀ C₀))).toRingHom
      R.FG ∧ ∀ i, ∃ g₀ : Polynomial (R ⊗[R₀] C₀), g₀.map η = g i := by
  classical
  let : Fintype J := Fintype.ofFinite J
  let L := Σ i : J, (g i).support
  choose n k y hsum using fun a : L =>
    TensorProduct.exists_sum_tmul_eq (eC.symm ((g a.1).coeff a.2.val))
  let coeffs : Set K := ⋃ i, Set.range (k i)
  have hcoeffs : coeffs.Finite := Set.finite_iUnion fun i => Set.finite_range (k i)
  let R := R₀ ⊔ Algebra.adjoin ℤ coeffs
  have hR₀R : R₀ ≤ R := le_sup_left
  have hcore : Algebra.adjoin ℤ coeffs ≤ R := le_sup_right
  have hR : R.FG := hR₀.sup (Subalgebra.fg_def.mpr ⟨coeffs, hcoeffs, rfl⟩)
  let : Algebra R₀ R := (Subalgebra.inclusion hR₀R).toAlgebra
  let j : R →ₐ[R₀] K :=
    { toRingHom := R.val.toRingHom, commutes' := fun _ => rfl }
  let η := ((eC.toAlgHom.restrictScalars R₀).comp
    (Algebra.TensorProduct.map j (AlgHom.id R₀ C₀))).toRingHom
  let k₀ (i : L) (m : Fin (n i)) : R :=
    ⟨k i m, hcore (Algebra.subset_adjoin (Set.mem_iUnion.mpr ⟨i, ⟨m, rfl⟩⟩))⟩
  have hη (r : R) (z : C₀) : η (r ⊗ₜ[R₀] z) = eC ((r : K) ⊗ₜ[R₀] z) := by
    change eC (Algebra.TensorProduct.map j (AlgHom.id R₀ C₀) (r ⊗ₜ[R₀] z)) = _
    rw [Algebra.TensorProduct.map_tmul]
    rfl
  have hlift (i : L) : ∃ a₀, η a₀ = (g i.1).coeff i.2.val := by
    refine ⟨∑ m, k₀ i m ⊗ₜ[R₀] y i m, ?_⟩
    calc
      η (∑ m, k₀ i m ⊗ₜ[R₀] y i m) = ∑ m, eC (k i m ⊗ₜ[R₀] y i m) := by
        rw [map_sum]
        exact Finset.sum_congr rfl fun m _ => hη (k₀ i m) (y i m)
      _ = eC (∑ m, k i m ⊗ₜ[R₀] y i m) := (map_sum eC _ _).symm
      _ = (g i.1).coeff i.2.val := by rw [← hsum i, AlgEquiv.apply_symm_apply]
  refine ⟨R, hR₀R, hR, fun i => ?_⟩
  apply (Polynomial.mem_lifts (g i)).mp
  apply (Polynomial.lifts_iff_coeff_lifts (g i)).mpr
  intro n
  by_cases hn : n ∈ (g i).support
  · exact hlift ⟨i, ⟨n, hn⟩⟩
  · simp only [Polynomial.mem_support_iff, not_not] at hn
    exact ⟨0, (map_zero η).trans hn.symm⟩

private theorem exists_zero_relations {C : Type u} {A : Type v}
    [CommRing C] [IsNoetherianRing C] [CommRing A] [Algebra C A]
    (c : C[X] →ₐ[C] A) (σ : A →ₐ[C] C)
    (hzero : σ.comp c = Polynomial.aeval (0 : C)) :
    ∃ (s : Finset C[X]) (g : s → C[X]),
      (∀ j, j.val = Polynomial.X * g j) ∧
      Ideal.span (Set.range fun j => Polynomial.X * g j) = RingHom.ker c.toRingHom := by
  classical
  obtain ⟨s, hs⟩ := (RingHom.ker c.toRingHom).fg_of_isNoetherianRing
  have hdiv (j : s) : Polynomial.X ∣ j.val := by
    apply Polynomial.X_dvd_iff.mpr
    have hj : c j.val = 0 := RingHom.mem_ker.mp (by
      change j.val ∈ RingHom.ker c.toRingHom
      rw [← hs]
      exact Ideal.subset_span j.property)
    have he := AlgHom.congr_fun hzero j.val
    rw [AlgHom.comp_apply, hj, map_zero] at he
    rw [Polynomial.coeff_zero_eq_eval_zero]
    simpa using he.symm
  choose g hg using hdiv
  refine ⟨s, g, hg, ?_⟩
  have hrange : Set.range (fun j => Polynomial.X * g j) = (s : Set C[X]) := by
    simp only [← hg]
    exact Subtype.range_val
  rw [hrange]
  exact hs

private theorem coefficientBaseChange_eq
    (R₀ : Type*) (R : Type u) (K : Type v) (D : Type w) (C : Type t)
    [CommRing R₀] [CommRing R] [CommRing K] [CommRing D] [CommRing C]
    [Algebra R₀ R] [Algebra R₀ K] [Algebra R K] [IsScalarTower R₀ R K]
    [Algebra R₀ D] [Algebra K C] [Algebra R₀ C] [IsScalarTower R₀ K C]
    [Algebra R C] [IsScalarTower R K C]
    (eC : K ⊗[R₀] D ≃ₐ[K] C) :
    (coefficientMap R K (R ⊗[R₀] D) C
      ((Algebra.TensorProduct.cancelBaseChange R₀ R K K D).trans eC)).toRingHom =
        ((eC.toAlgHom.restrictScalars R₀).comp
          (Algebra.TensorProduct.map (IsScalarTower.toAlgHom R₀ R K)
            (AlgHom.id R₀ D))).toRingHom := by
  apply RingHom.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul r d =>
      change eC (Algebra.TensorProduct.cancelBaseChange R₀ R K K D
        (1 ⊗ₜ[R] (r ⊗ₜ[R₀] d))) =
          eC (Algebra.TensorProduct.map (IsScalarTower.toAlgHom R₀ R K)
            (AlgHom.id R₀ D) (r ⊗ₜ[R₀] d))
      rw [Algebra.TensorProduct.cancelBaseChange_tmul, Algebra.TensorProduct.map_tmul]
      simp only [Algebra.smul_def, mul_one, AlgHom.id_apply]
      rfl
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem exists_quotient_model
    (R : Type u) (K : Type v) (D : Type w) (C A : Type*)
    [CommRing R] [CommRing K] [CommRing D] [CommRing C] [CommRing A]
    [Algebra R K] [Algebra R D] [Algebra K C] [Algebra R C] [IsScalarTower R K C]
    [Algebra C A] [Algebra K A] [IsScalarTower K C A] [Algebra.FinitePresentation R D]
    (e : K ⊗[R] D ≃ₐ[K] C) (c : C[X] →ₐ[C] A) (σ : A →ₐ[C] C)
    (hc : Function.Surjective c) (N : ℕ) {J : Type*} [Finite J]
    (r : J → D[X]) (s : J → C[X])
    (hs : Ideal.span (Set.range s) = RingHom.ker c.toRingHom)
    (hr : ∀ j, (r j).map (coefficientMap R K D C e) = s j)
    (hzero : σ.comp c = Polynomial.aeval (0 : C))
    (hzr : ∀ j, Polynomial.aeval (0 : D) (r j) = 0)
    (hN : Polynomial.X ^ N ∈ Ideal.span (Set.range r)) :
    ∃ (B : Type w) (_ : CommRing B) (_ : Algebra R B) (_ : Algebra D B)
      (_ : IsScalarTower R D B) (eB : K ⊗[R] B ≃ₐ[K] A),
      Algebra.FinitePresentation R B ∧ Algebra.FinitePresentation D B ∧
      ∃ (c₁ : D[X] →ₐ[D] B) (σ₁ : B →ₐ[D] D),
        Function.Surjective c₁ ∧ (c₁ Polynomial.X) ^ N = 0 ∧
        σ₁.comp c₁ = Polynomial.aeval (0 : D) ∧
        (∀ (k : K) (p : D[X]), eB (k ⊗ₜ[R] c₁ p) =
          algebraMap K A k * c (p.map (coefficientMap R K D C e))) ∧
        (∀ (k : K) (b : B), σ (eB (k ⊗ₜ[R] b)) =
          algebraMap K C k * coefficientMap R K D C e (σ₁ b)) := by
  classical
  let I := Ideal.span (Set.range r)
  let B := D[X] ⧸ I
  let c₁ : D[X] →ₐ[D] B := Ideal.Quotient.mkₐ D I
  let z : D[X] →ₐ[D] D := Polynomial.aeval 0
  have hz : I ≤ RingHom.ker z.toRingHom := by
    apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact hzr j
  let σ₁ : B →ₐ[D] D := Ideal.Quotient.liftₐ I z hz
  let eB : K ⊗[R] B ≃ₐ[K] A := quotientBaseChange R K D C A e c hc r s hs hr
  have hp : (c₁ Polynomial.X) ^ N = 0 := by
    have h := Ideal.Quotient.eq_zero_iff_mem.mpr hN
    rw [map_pow] at h
    exact h
  let : Algebra.FinitePresentation D B :=
    Algebra.FinitePresentation.quotient (Submodule.fg_span (Set.finite_range r))
  let : Algebra.FinitePresentation R B := Algebra.FinitePresentation.trans R D B
  have he (k : K) (p : D[X]) : eB (k ⊗ₜ[R] c₁ p) =
      algebraMap K A k * c (p.map (coefficientMap R K D C e)) :=
    quotientBaseChange_tmul R K D C A e c hc r s hs hr k p
  refine ⟨B, inferInstance, inferInstance, inferInstance, inferInstance,
    eB, inferInstance, inferInstance, c₁, σ₁, Ideal.Quotient.mk_surjective, hp, rfl, he, ?_⟩
  intro k b
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective b
  change σ (eB (k ⊗ₜ[R] c₁ p)) =
    algebraMap K C k * coefficientMap R K D C e (σ₁ (c₁ p))
  rw [he k p, map_mul]
  have hσk : σ (algebraMap K A k) = algebraMap K C k :=
    (σ.restrictScalars K).commutes k
  rw [hσk]
  congr 1
  change σ (c (p.map (coefficientMap R K D C e))) = coefficientMap R K D C e (z p)
  rw [← AlgHom.comp_apply σ c, hzero]
  simp only [Polynomial.aeval_def, Polynomial.eval₂_at_zero]
  rw [Polynomial.coeff_map]
  simp only [z, Polynomial.aeval_def, Polynomial.eval₂_at_zero, Algebra.algebraMap_self_apply]
  rfl

end FrobeniusSplitting
