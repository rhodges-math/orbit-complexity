import OrbitComplexity.FrobeniusSplitting.Normality.ModelImages
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-!
# Finite algebra maps over arithmetic models

Monic equations for finitely many algebra generators involve finitely many coefficients.
Adjoining them to a coefficient ring descends finiteness together with the algebra map and
its scalar-extension comparison square.
-/

namespace FrobeniusSplitting

open scoped TensorProduct

private theorem finite_of_integral_generators {R A B ι : Type*}
    [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra A B]
    [Algebra R B] [IsScalarTower R A B] [Finite ι] (x : ι → B)
    (hgen : Algebra.adjoin R (Set.range x) = ⊤) (hint : ∀ i, IsIntegral A (x i)) :
    Module.Finite A B := by
  have hinc : Algebra.adjoin R (Set.range x) ≤ (integralClosure A B).restrictScalars R := by
    apply Algebra.adjoin_le
    rintro _ ⟨i, rfl⟩
    exact hint i
  have : Algebra.IsIntegral A B := ⟨fun b ↦ hinc (by rw [hgen]; trivial)⟩
  have : Algebra.FiniteType R B :=
    ⟨Subalgebra.fg_def.mpr ⟨Set.range x, Set.finite_range x, hgen⟩⟩
  have : Algebra.FiniteType A B := Algebra.FiniteType.of_restrictScalars_finiteType R A B
  exact Algebra.IsIntegral.finite

private theorem integral_of_coeffs_mem {R A B : Type*}
    [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra A B]
    (A₀ : Subalgebra R A) (b : B) (q : Polynomial A) (hq : q.Monic)
    (hroot : Polynomial.aeval b q = 0) (hc : (q.coeffs : Set A) ⊆ A₀) :
    IsIntegral A₀ b := by
  have hlift : q ∈ Polynomial.lifts A₀.val.toRingHom := by
    apply (Polynomial.lifts_iff_coeffs_subset_range q).mpr
    exact fun a ha ↦ ⟨⟨a, hc ha⟩, rfl⟩
  obtain ⟨q₀, hmap, _, hmonic⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlift hq
  refine ⟨q₀, hmonic, ?_⟩
  change Polynomial.aeval b q₀ = 0
  change Polynomial.map (algebraMap A₀ A) q₀ = q at hmap
  rw [← Polynomial.aeval_map_algebraMap A, hmap]
  exact hroot

private theorem finite_subalgebra_of_integral {R A B ι : Type*}
    [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra A B]
    [Algebra R B] [IsScalarTower R A B] [Finite ι]
    (A₀ : Subalgebra R A) (B₀ : Subalgebra R B)
    (hf : Set.MapsTo (algebraMap A B) A₀ B₀) (x : ι → B₀)
    (hgen : Algebra.adjoin R (Set.range x) = ⊤)
    (hint : ∀ i, IsIntegral A₀ (x i : B)) :
    ∃ _ : Algebra A₀ B₀, IsScalarTower R A₀ B₀ ∧ Module.Finite A₀ B₀ ∧
      ∀ a : A₀, (algebraMap A₀ B₀ a : B) = algebraMap A B (a : A) := by
  let f : A₀ →ₐ[R] B₀ := ((IsScalarTower.toAlgHom R A B).comp A₀.val).codRestrict B₀
    (fun a ↦ hf a.property)
  let : Algebra A₀ B₀ := f.toAlgebra
  have : IsScalarTower R A₀ B₀ := IsScalarTower.of_algebraMap_eq (fun r ↦ (f.commutes r).symm)
  let incl : B₀ →ₐ[A₀] B :=
    { toRingHom := B₀.val.toRingHom
      commutes' a := rfl }
  have hix (i : ι) : IsIntegral A₀ (x i) :=
    (isIntegral_algHom_iff incl Subtype.val_injective).mp (hint i)
  exact ⟨inferInstance, inferInstance, finite_of_integral_generators x hgen hix,
    fun _ ↦ rfl⟩

universe u

private theorem pair_models_over {K A B : Type u}
    [CommRing K] [CommRing A] [CommRing B] [Algebra K A] [Algebra K B]
    {n m n' m' : ℕ} (P : Algebra.Presentation K A (Fin n) (Fin m))
    (Q : Algebra.Presentation K B (Fin n') (Fin m')) (f : A →ₐ[K] B)
    (S : Subalgebra ℤ K) (hS : S.FG) :
    ∃ (R : Subalgebra ℤ K) (_ : P.HasCoeffs R) (_ : Q.HasCoeffs R)
      (f₀ : P.ModelOfHasCoeffs R →ₐ[R] Q.ModelOfHasCoeffs R),
      S ≤ R ∧ R.FG ∧ Algebra.FinitePresentation R (P.ModelOfHasCoeffs R) ∧
        Algebra.FinitePresentation R (Q.ModelOfHasCoeffs R) ∧
        (Q.tensorModelOfHasCoeffsEquiv R).toAlgHom.comp
          (Algebra.TensorProduct.lTensor (S := K) K f₀) =
        f.comp (P.tensorModelOfHasCoeffsEquiv R).toAlgHom := by
  let A' : Bool → Type u
    | false => A
    | true => B
  let (i : Bool) : CommRing (A' i) := by cases i <;> infer_instance
  let (i : Bool) : Algebra K (A' i) := by cases i <;> infer_instance
  let vars : Bool → Type
    | false => Fin n
    | true => Fin n'
  let rels : Bool → Type
    | false => Fin m
    | true => Fin m'
  have (i : Bool) : Finite (vars i) := by cases i <;> infer_instance
  have (i : Bool) : Finite (rels i) := by cases i <;> infer_instance
  let P' : ∀ i, Algebra.Presentation K (A' i) (vars i) (rels i)
    | false => P
    | true => Q
  let src (_ : Unit) := false
  let tgt (_ : Unit) := true
  let f' (_ : Unit) : A' false →ₐ[K] A' true := f
  obtain ⟨R, hP', f₀, hSR, hfg, hfp, hcomm⟩ :=
    exists_arithmetic_graph_over A' vars rels P' src tgt f' S hS
  have hP : P.HasCoeffs R := hP' false
  have hQ : Q.HasCoeffs R := hP' true
  exact ⟨R, hP, hQ, f₀ (), hSR, hfg, hfp false, hfp true, hcomm ()⟩

/-- A finite algebra has finitely presented arithmetic models with a finite algebra map
whose scalar-extension comparison square commutes. -/
theorem exists_finite_arithmetic_model {K A B : Type u}
    [CommRing K] [CommRing A] [CommRing B] [Algebra K A] [Algebra A B]
    [Algebra K B] [IsScalarTower K A B]
    [Algebra.FinitePresentation K A] [Algebra.FinitePresentation K B] [Module.Finite A B] :
    ∃ (R : Subalgebra ℤ K) (A₀ : Subalgebra R A) (B₀ : Subalgebra R B)
      (_ : Algebra A₀ B₀) (_ : IsScalarTower R A₀ B₀)
      (eA : K ⊗[R] A₀ ≃ₐ[K] A) (eB : K ⊗[R] B₀ ≃ₐ[K] B),
      R.FG ∧ Algebra.FinitePresentation R A₀ ∧ Algebra.FinitePresentation R B₀ ∧
      Module.Finite A₀ B₀ ∧
      (∀ (k : K) (a : A₀), eA (k ⊗ₜ[R] a) = algebraMap K A k * (a : A)) ∧
      (∀ (k : K) (b : B₀), eB (k ⊗ₜ[R] b) = algebraMap K B k * (b : B)) ∧
      eB.toAlgHom.comp (Algebra.TensorProduct.lTensor (S := K) K
        (IsScalarTower.toAlgHom R A₀ B₀)) =
        (IsScalarTower.toAlgHom K A B).comp eA.toAlgHom := by
  classical
  let P := Algebra.Presentation.ofFinitePresentation K A
  let Q := Algebra.Presentation.ofFinitePresentation K B
  choose q qmonic qroot using fun j ↦ IsIntegral.of_finite (R := A) (Q.val j)
  let coeffs : Set K := ⋃ j, ⋃ a ∈ (q j).coeffs, (P.σ a).coeffs
  have hC : coeffs.Finite := Set.finite_iUnion fun j ↦
    (q j).coeffs.finite_toSet.biUnion fun a _ ↦ (P.σ a).coeffs.finite_toSet
  let S : Subalgebra ℤ K := Algebra.adjoin ℤ coeffs
  have hS : S.FG := Subalgebra.fg_def.mpr ⟨coeffs, hC, rfl⟩
  obtain ⟨R, hP, hQ, f₀, hSR, hfg, hfpP, hfpQ, hcomm⟩ :=
    pair_models_over P Q (IsScalarTower.toAlgHom K A B) S hS
  have : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq fun r ↦ by
    change algebraMap K B (r : K) = algebraMap A B (algebraMap K A (r : K))
    rw [IsScalarTower.algebraMap_apply K A B]
  have : Algebra.FiniteType ℤ R := (Subalgebra.fg_iff_finiteType R).mp hfg
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing ℤ R
  have : Algebra.FinitePresentation R (P.ModelOfHasCoeffs R) := hfpP
  have : Algebra.FinitePresentation R (Q.ModelOfHasCoeffs R) := hfpQ
  let eP := P.tensorModelOfHasCoeffsEquiv R
  let eQ := Q.tensorModelOfHasCoeffsEquiv R
  let A₀ : Subalgebra R A := (tensorImageHom eP).range
  let B₀ : Subalgebra R B := (tensorImageHom eQ).range
  have hmap : Set.MapsTo (algebraMap A B) A₀ B₀ := by
    intro a ha
    obtain ⟨m, hm⟩ := ha
    change tensorImageHom eP m = a at hm
    refine ⟨f₀ m, ?_⟩
    change tensorImageHom eQ (f₀ m) = algebraMap A B a
    have hsquare := AlgHom.congr_fun hcomm ((1 : K) ⊗ₜ[R] m)
    change tensorImageHom eQ (f₀ m) = algebraMap A B (tensorImageHom eP m) at hsquare
    simpa only [hm] using hsquare
  have hcoeff (j) : ((q j).coeffs : Set A) ⊆ A₀ := by
    intro a ha
    have hlift : ∃ v : MvPolynomial _ R, MvPolynomial.map (algebraMap R K) v = P.σ a := by
      apply MvPolynomial.mem_range_map_iff_coeffs_subset.mpr
      intro k hk
      refine ⟨⟨k, hSR (Algebra.subset_adjoin ?_)⟩, rfl⟩
      exact Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr
        ⟨a, Set.mem_iUnion.mpr ⟨ha, hk⟩⟩⟩
    obtain ⟨v, hv⟩ := hlift
    change a ∈ (tensorImageHom (P.tensorModelOfHasCoeffsEquiv R)).range
    rw [tensorImageHom_range, ← MvPolynomial.aeval_range]
    refine ⟨v, ?_⟩
    change MvPolynomial.aeval P.val v = a
    rw [← MvPolynomial.aeval_map_algebraMap K, hv, P.aeval_val_σ]
  have hint (j) : IsIntegral A₀ (Q.val j) :=
    integral_of_coeffs_mem A₀ (Q.val j) (q j) (qmonic j) (qroot j) (hcoeff j)
  let x (j) : B₀ := ⟨Q.val j, by
    change Q.val j ∈ (tensorImageHom (Q.tensorModelOfHasCoeffsEquiv R)).range
    rw [tensorImageHom_range]
    exact Algebra.subset_adjoin ⟨j, rfl⟩⟩
  let ψ : MvPolynomial _ R →ₐ[R] B₀ := (tensorImageHom eQ).rangeRestrict.comp
    (Ideal.Quotient.mkₐ R _)
  have hψ : ψ = MvPolynomial.aeval x := by
    ext j
    simp only [MvPolynomial.aeval_X]
    change tensorImageHom eQ (Ideal.Quotient.mk _ (MvPolynomial.X j)) = Q.val j
    rw [tensorImageHom_mk, MvPolynomial.aeval_X]
  have hsurj : Function.Surjective (MvPolynomial.aeval (R := R) x) := by
    rw [← hψ]
    exact (tensorImageHom eQ).rangeRestrict_surjective.comp Ideal.Quotient.mk_surjective
  have hgen : Algebra.adjoin R (Set.range x) = ⊤ := by
    rw [← MvPolynomial.aeval_range]
    exact (AlgHom.range_eq_top _).mpr hsurj
  obtain ⟨alg, tower, finite, hfac⟩ := finite_subalgebra_of_integral A₀ B₀ hmap x hgen hint
  refine ⟨R, A₀, B₀, alg, tower, tensorImageEquiv eP, tensorImageEquiv eQ, hfg,
    tensorImage_finitePresentation eP, tensorImage_finitePresentation eQ, finite,
    tensorImageEquiv_tmul eP, tensorImageEquiv_tmul eQ, ?_⟩
  ext a
  change tensorImageEquiv eQ ((1 : K) ⊗ₜ[R] algebraMap A₀ B₀ a) =
    algebraMap A B (tensorImageEquiv eP ((1 : K) ⊗ₜ[R] a))
  rw [tensorImageEquiv_tmul, tensorImageEquiv_tmul]
  simp only [map_one, one_mul]
  exact hfac a

end FrobeniusSplitting
