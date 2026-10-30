import OrbitComplexity.SchubertGeometry.Frobenius.Determinant.OppositionQuadraticUnits
import OrbitComplexity.FrobeniusSplitting.Normality.Assembly.FrameUnitRetention
import Mathlib.RingTheory.Smooth.NoetherianDescent
import TauCeti.Algebra.AlgebraicGroup.Smooth.AlgebraicallyClosed
import OrbitComplexity.FrobeniusSplitting.Normality.Components.NonvanishingOpens
import OrbitComplexity.FrobeniusSplitting.Normality.Connectedness.CoefficientAwayStage

/-! # A coefficient stage for opposition determinant powers

The coefficient unit and its inverse are retained in the fixed polynomial
chart coefficient algebra. Every determinant power is the image of a power
of the same retained quadratic polynomial.
-/

set_option autoImplicit false
noncomputable section
universe u v

open AlgebraicGeometry CategoryTheory Opposite FrobeniusSplitting
open FrobeniusSplitting.RetainedCharacter
open scoped TensorProduct

namespace SchubertGeometry.DeterminantSection

open private chartAlgebra from
  OrbitComplexity.SchubertGeometry.Frobenius.Determinant.OppositionPolynomial
open private exists_unit_stage from
  OrbitComplexity.FrobeniusSplitting.Normality.Assembly.FrameUnitRetention
open private scalarMap from
  OrbitComplexity.FrobeniusSplitting.Normality.Assembly.RetainedCoframeAdjustments
open private scalar_extension unit_inverse_value from
  OrbitComplexity.SchubertGeometry.Frobenius.Determinant.OppositionQuadraticUnits

private theorem retain_unit_above {K : Type u} [Field K]
    (S : Subalgebra ℤ K) (hS : S.FG)
    {B A : Type u} [CommRing B] [Algebra S B] [Module.Flat S B]
    [CommRing A] [Algebra K A] (e : K ⊗[S] B ≃ₐ[K] A)
    (vars rels : Type v) [Finite vars] [Finite rels]
    (presentation : Algebra.Presentation S B vars rels) (a : Aˣ)
    (start : Subalgebra ℤ K) (hstart : start.FG) :
    ∃ (R : Subalgebra ℤ K) (hSR : S ≤ R), start ≤ R ∧ R.FG ∧
      let : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
      let : IsScalarTower S R K := Subalgebra.inclusion.isScalarTower_right hSR K
      ∃ w : (R ⊗[S] B)ˣ, scalarMap (R := R) e (w : R ⊗[S] B) = (a : A) := by
  obtain ⟨R₀, hSR₀, hstage⟩ := exists_unit_stage S hS
    (fun _ : Unit => B) (fun _ : Unit => A) (fun _ : Unit => e)
    (fun _ : Unit => vars) (fun _ : Unit => rels)
    (fun _ : Unit => presentation) (fun _ : Unit => a)
  let : Algebra S R₀ := (Subalgebra.inclusion hSR₀).toAlgebra
  let : IsScalarTower S R₀ K := Subalgebra.inclusion.isScalarTower_right hSR₀ K
  change R₀.FG ∧ ∃ d : Unit → (R₀ ⊗[S] B)ˣ,
    (∀ x, scalarMap (R := R₀) e (d x : R₀ ⊗[S] B) = (a : A)) ∧
      ∀ x n, scalarMap (R := R₀) e ((d x : R₀ ⊗[S] B) ^ n) = (a : A) ^ n at hstage
  obtain ⟨hR₀, d₀, hd₀, _⟩ := hstage
  let R : Subalgebra ℤ K := R₀ ⊔ start
  have hSR : S ≤ R := hSR₀.trans le_sup_left
  let : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
  let : IsScalarTower S R K := Subalgebra.inclusion.isScalarTower_right hSR K
  let f : R₀ →ₐ[S] R :=
    { __ := (Subalgebra.inclusion (show R₀ ≤ R from le_sup_left)).toRingHom
      commutes' := fun _ => rfl }
  have hf : (IsScalarTower.toAlgHom S R K).comp f = IsScalarTower.toAlgHom S R₀ K := by
    ext x
    rfl
  let w : (R ⊗[S] B)ˣ :=
    Units.map (Algebra.TensorProduct.map f (AlgHom.id S B)).toMonoidHom (d₀ ())
  refine ⟨R, hSR, le_sup_right, hR₀.sup hstart, w, ?_⟩
  exact (scalar_extension e f hf (d₀ () : R₀ ⊗[S] B)).trans (hd₀ ())

private theorem quadratic_power {A : Type u} [CommRing A] (a : A) (N : ℕ) :
    (Polynomial.C a * Polynomial.X ^ 2) ^ N =
      Polynomial.C (a ^ N) * (Polynomial.X : Polynomial A) ^ (2 * N) := by
  rw [mul_pow, ← Polynomial.C_pow, ← pow_mul]

private theorem quadratic_power_map {B A : Type u} [CommRing B] [CommRing A]
    (f : B →+* A) (w : Bˣ) (a : Aˣ) (h : f (w : B) = (a : A)) (N : ℕ) :
    Polynomial.map f ((Polynomial.C (w : B) * Polynomial.X ^ 2) ^ N) =
      (Polynomial.C (a : A) * (Polynomial.X : Polynomial A) ^ 2) ^ N := by
  simp only [Polynomial.map_pow, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X, h]

/-- The complementary-root coefficient algebra has one smooth arithmetic model
above the prescribed subring, with nonempty fibres over every field. -/
theorem exists_opposition_coefficient_model
    {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroups.ReductiveGroupData K) (i : G.rootBase.support)
    (initial : Subalgebra ℤ K) (hInitial : initial.FG) :
    ∃ (S : Subalgebra ℤ K) (_ : initial ≤ S) (_ : S.FG)
      (B : Type u) (_ : CommRing B) (_ : Algebra S B),
      Algebra.Smooth S B ∧ Nonempty (K ⊗[S] B ≃ₐ[K] chartAlgebra G i) ∧
      ∀ (κ : Type u) [Field κ] [Algebra S κ], Nontrivial (κ ⊗[S] B) := by
  classical
  let : Algebra.Smooth K (chartAlgebra G i) :=
    (TauCeti.smoothCommHopfAlgProperty_iff
      (CommHopfAlgCat.of K (chartAlgebra G i))).mp
      (TauCeti.smoothCommHopfAlgProperty_of_isAlgClosed_of_isReduced K _)
  obtain ⟨S0, B0, ring0, alg0, hS0, hSmooth0, e0⟩ :=
    Algebra.Smooth.exists_subalgebra_fg ℤ K (chartAlgebra G i)
  let : CommRing B0 := ring0
  let : Algebra S0 B0 := alg0
  let : Algebra.Smooth S0 B0 := hSmooth0
  have hx : ¬ IsNilpotent ((1 : K) ⊗ₜ[S0] (1 : B0)) := by
    intro hn
    have h := hn.map e0.some.symm.toRingHom
    exact not_isNilpotent_one (by
      simpa only [← Algebra.TensorProduct.one_def, map_one] using h)
  obtain ⟨r, hr, hnonzero⟩ :=
    @FrobeniusSplitting.exists_fiber_nonvanishing_open.{u,0}
      S0 K (inferInstanceAs (CommRing S0)) (inferInstanceAs (IsDomain S0))
      (inferInstanceAs (Field K)) (inferInstanceAs (Algebra S0 K))
      (inferInstanceAs (FaithfulSMul S0 K)) Unit (inferInstanceAs (Finite Unit))
      (fun _ : Unit => B0) (fun _ => ring0) (fun _ => alg0)
      (fun _ => inferInstanceAs (Algebra.FinitePresentation S0 B0))
      (fun _ => 1) (fun _ => hx)
  obtain ⟨A, h0A, hA, hAway⟩ :=
    FrobeniusSplitting.exists_coefficient_away S0 hS0 r hr
  let : Algebra S0 A := (Subalgebra.inclusion h0A).toAlgebra
  let : IsLocalization.Away r A := hAway
  let S : Subalgebra ℤ K := A ⊔ initial
  have hAS : A ≤ S := le_sup_left
  have h0 : S0 ≤ S := h0A.trans hAS
  let : Algebra A S := (Subalgebra.inclusion hAS).toAlgebra
  let : Algebra S0 S := (Subalgebra.inclusion h0).toAlgebra
  let : IsScalarTower S0 S K := Subalgebra.inclusion.isScalarTower_right h0 K
  have hrS : IsUnit (algebraMap S0 S r) := by
    change IsUnit (algebraMap A S (algebraMap S0 A r))
    exact (IsLocalization.Away.algebraMap_isUnit r).map (algebraMap A S)
  refine ⟨S, le_sup_right, hA.sup hInitial, S ⊗[S0] B0,
    inferInstance, inferInstance, inferInstance,
    ⟨(Algebra.TensorProduct.cancelBaseChange S0 S K K B0).trans e0.some.symm⟩, ?_⟩
  intro κ κField sκAlgebra
  let : Algebra S0 κ := ((algebraMap S κ).comp (algebraMap S0 S)).toAlgebra
  let : IsScalarTower S0 S κ := IsScalarTower.of_algebraMap_eq' rfl
  have hrκ : algebraMap S0 κ r ≠ 0 := by
    change algebraMap S κ (algebraMap S0 S r) ≠ 0
    exact (hrS.map (algebraMap S κ)).ne_zero
  have hn : ¬ IsNilpotent (1 : κ ⊗[S0] B0) := by
    simpa only [Algebra.TensorProduct.one_def] using hnonzero κ hrκ ()
  have h1 : (1 : κ ⊗[S0] B0) ≠ 0 := by
    intro h
    exact hn (h.symm ▸ ⟨1, pow_one 0⟩)
  let E := Algebra.TensorProduct.cancelBaseChange S0 S κ κ B0
  refine ⟨⟨E.symm 1, E.symm 0, ?_⟩⟩
  intro h
  exact h1 (E.symm.injective h)

/-- Above any finite coefficient stage, one retained unit and its inverse
produce every determinant power on the fixed opposition polynomial chart. -/
theorem exists_opposition_coefficient_stage
    {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroups.ReductiveGroupData K) (i : G.rootBase.support)
    (S : Subalgebra ℤ K) (hS : S.FG)
    {B : Type u} [CommRing B] [Algebra S B] [Module.Flat S B]
    (e : K ⊗[S] B ≃ₐ[K] chartAlgebra G i)
    (vars rels : Type v) [Finite vars] [Finite rels]
    (presentation : Algebra.Presentation S B vars rels)
    (start : Subalgebra ℤ K) (hstart : start.FG) :
    ∃ (R : Subalgebra ℤ K) (hSR : S ≤ R), start ≤ R ∧ R.FG ∧
      let : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
      let : IsScalarTower S R K := Subalgebra.inclusion.isScalarTower_right hSR K
      ∃ (a : (chartAlgebra G i)ˣ) (w : (R ⊗[S] B)ˣ),
        (∀ N : ℕ, oppositionChartPolynomial G i N =
          (Polynomial.C (a : chartAlgebra G i) *
            (Polynomial.X : Polynomial (chartAlgebra G i)) ^ 2) ^ N) ∧
        scalarMap (R := R) e (w : R ⊗[S] B) = (a : chartAlgebra G i) ∧
        scalarMap (R := R) e ((w⁻¹ : (R ⊗[S] B)ˣ) : R ⊗[S] B) =
          ((a⁻¹ : (chartAlgebra G i)ˣ) : chartAlgebra G i) ∧
        ∀ N : ℕ, Polynomial.map (scalarMap (R := R) e)
          ((Polynomial.C (w : R ⊗[S] B) *
            (Polynomial.X : Polynomial (R ⊗[S] B)) ^ 2) ^ N) =
            oppositionChartPolynomial G i N := by
  obtain ⟨aK, haK⟩ := oppositionChartPolynomial_formula G i
  let a : (chartAlgebra G i)ˣ :=
    Units.map (algebraMap K (chartAlgebra G i)).toMonoidHom aK
  have ha (N : ℕ) : oppositionChartPolynomial G i N =
      (Polynomial.C (a : chartAlgebra G i) * Polynomial.X ^ 2) ^ N := by
    calc
      _ = Polynomial.C (algebraMap K (chartAlgebra G i) ((aK : K) ^ N)) *
          Polynomial.X ^ (2 * N) := haK N
      _ = Polynomial.C ((a : chartAlgebra G i) ^ N) * Polynomial.X ^ (2 * N) := by
        rw [map_pow]
        rfl
      _ = _ := (quadratic_power (a : chartAlgebra G i) N).symm
  obtain ⟨R, hSR, hstartR, hR, w, hw⟩ :=
    retain_unit_above S hS e vars rels presentation a start hstart
  let : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
  let : IsScalarTower S R K := Subalgebra.inclusion.isScalarTower_right hSR K
  refine ⟨R, hSR, hstartR, hR, a, w, ha, hw, unit_inverse_value _ w a hw, ?_⟩
  intro N
  exact (quadratic_power_map (scalarMap (R := R) e) w a hw N).trans (ha N).symm

end SchubertGeometry.DeterminantSection
