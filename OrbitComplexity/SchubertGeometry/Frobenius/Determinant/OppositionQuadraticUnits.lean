import OrbitComplexity.SchubertGeometry.Frobenius.Determinant.OppositionCoframePowers
import OrbitComplexity.SchubertGeometry.Frobenius.Determinant.RetainedRootSquares
import OrbitComplexity.FrobeniusSplitting.Normality.Assembly.FrameUnitRetention
import OrbitComplexity.FrobeniusSplitting.Normality.Assembly.RetainedCoframeAdjustments
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Quadratic determinant units on coefficient extensions

A coefficient extension retains the quadratic coefficient and its inverse.
Injectivity of the tensor comparison then identifies the scalar extension of
the original determinant polynomial with the corresponding unit times X².
-/

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory AlgebraicGeometry ReductiveGroups GroupActions FrobeniusSplitting
open scoped TensorProduct

open private coefficientMap from
  OrbitComplexity.SchubertGeometry.Frobenius.Determinant.OppositionCoframePowers
open private exists_unit_stage scalarEvaluation_injective from
  OrbitComplexity.FrobeniusSplitting.Normality.Assembly.FrameUnitRetention
open private scalarMap scalarMap_factor from
  OrbitComplexity.FrobeniusSplitting.Normality.Assembly.RetainedCoframeAdjustments
open private polynomial_eq_square from
  OrbitComplexity.SchubertGeometry.Frobenius.Determinant.RetainedRootSquares
open private SchubertGeometry.DeterminantSection.chartAlgebra from
  OrbitComplexity.SchubertGeometry.Frobenius.Determinant.OppositionPolynomial

namespace SchubertGeometry.DeterminantSection

private theorem scalar_factor {S R K B A : Type u}
    [CommRing S] [CommRing R] [CommRing K] [CommRing B] [CommRing A]
    [Algebra S R] [Algebra S K] [Algebra R K] [IsScalarTower S R K]
    [Algebra S B] [Algebra K A] (e : K ⊗[S] B ≃ₐ[K] A) :
    (scalarMap (R := R) e).comp
      (Algebra.TensorProduct.includeRight : B →ₐ[S] R ⊗[S] B).toRingHom = coefficientMap e :=
  scalarMap_factor e (coefficientMap e) (fun _ => rfl)

private theorem scalar_injective {S R K B A : Type u}
    [CommRing S] [CommRing R] [CommRing K] [CommRing B] [CommRing A]
    [Algebra S R] [Algebra S K] [Algebra R K] [IsScalarTower S R K]
    [Algebra S B] [Module.Flat S B] [Algebra K A]
    (e : K ⊗[S] B ≃ₐ[K] A) (hi : Function.Injective (algebraMap R K)) :
    Function.Injective (scalarMap (R := R) e) :=
  scalarEvaluation_injective e hi

private theorem scalar_extension {S R T K B A : Type u}
    [CommRing S] [CommRing R] [CommRing T] [CommRing K] [CommRing B] [CommRing A]
    [Algebra S R] [Algebra S T] [Algebra S K] [Algebra R K] [Algebra T K]
    [IsScalarTower S R K] [IsScalarTower S T K] [Algebra S B] [Algebra K A]
    (e : K ⊗[S] B ≃ₐ[K] A) (f : R →ₐ[S] T)
    (hf : (IsScalarTower.toAlgHom S T K).comp f = IsScalarTower.toAlgHom S R K)
    (x : R ⊗[S] B) :
    scalarMap (R := T) e (Algebra.TensorProduct.map f (AlgHom.id S B) x) =
      scalarMap (R := R) e x := by
  have hmap :
      (Algebra.TensorProduct.map (IsScalarTower.toAlgHom S T K) (AlgHom.id S B)).comp
        (Algebra.TensorProduct.map f (AlgHom.id S B)) =
      Algebra.TensorProduct.map (IsScalarTower.toAlgHom S R K) (AlgHom.id S B) := by
    rw [← Algebra.TensorProduct.map_comp, hf, AlgHom.id_comp]
  exact congrArg e (AlgHom.congr_fun hmap x)

private theorem square_reflection {B C A : Type u}
    [CommRing B] [CommRing C] [CommRing A]
    (f : B →+* C) (g : C →+* A) (h : B →+* A) (hgf : g.comp f = h)
    (hg : Function.Injective g) (Q : Polynomial B) (a : Aˣ) (w : Cˣ)
    (hQ : Polynomial.map h Q = Polynomial.C (a : A) * Polynomial.X ^ 2)
    (hw : g (w : C) = (a : A)) :
    Polynomial.map f Q = Polynomial.C (w : C) * Polynomial.X ^ 2 := by
  apply polynomial_eq_square g hg (Polynomial.map f Q) w
  calc
    Polynomial.map g (Polynomial.map f Q) = Polynomial.map h Q := by
      rw [Polynomial.map_map, hgf]
    _ = Polynomial.C (a : A) * Polynomial.X ^ 2 := hQ
    _ = Polynomial.C (g (w : C)) * Polynomial.X ^ 2 := by rw [hw]

private theorem square_coefficient {B : Type u} [CommRing B]
    (Q : Polynomial B) (w : Bˣ)
    (hQ : Q = Polynomial.C (w : B) * Polynomial.X ^ 2) : (w : B) = Q.coeff 2 := by
  rw [hQ]
  simp

private theorem unit_inverse_value {B A : Type u} [CommRing B] [CommRing A]
    (f : B →+* A) (w : Bˣ) (a : Aˣ) (h : f (w : B) = (a : A)) :
    f ((w⁻¹ : Bˣ) : B) = ((a⁻¹ : Aˣ) : A) := by
  have hu : Units.map f.toMonoidHom w = a := Units.ext h
  exact congrArg (fun z : Aˣ => ((z⁻¹ : Aˣ) : A)) hu

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K)

/-- Above any finitely generated coefficient stage, the original determinant
polynomial becomes a quadratic monomial with invertible coefficient. The unit
and its inverse have the prescribed images in the full root-complement algebra. -/
theorem exists_opposition_square_stage
    (i : G.rootBase.support) (S : Subalgebra ℤ K) (hS : S.FG)
    {B : Type u} [CommRing B] [Algebra S B] [Module.Flat S B]
    (e : K ⊗[S] B ≃ₐ[K] SchubertGeometry.DeterminantSection.chartAlgebra G i)
    (vars rels : Type v) [Finite vars] [Finite rels]
    (presentation : Algebra.Presentation S B vars rels)
    (Q : Polynomial B)
    (hQ : Polynomial.map (coefficientMap e) Q = oppositionChartPolynomial G i 1)
    (start : Subalgebra ℤ K) (hstart : start.FG) :
    ∃ (R : Subalgebra ℤ K) (hSR : S ≤ R), start ≤ R ∧ R.FG ∧
      let : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
      let : IsScalarTower S R K := Subalgebra.inclusion.isScalarTower_right hSR K
      ∃ (a : (SchubertGeometry.DeterminantSection.chartAlgebra G i)ˣ)
        (w : (R ⊗[S] B)ˣ),
        oppositionChartPolynomial G i 1 =
          Polynomial.C (a : SchubertGeometry.DeterminantSection.chartAlgebra G i) * Polynomial.X ^ 2
            ∧
        scalarMap (R := R) e (w : R ⊗[S] B) = (a : SchubertGeometry.DeterminantSection.chartAlgebra
          G i) ∧
        scalarMap (R := R) e ((w⁻¹ : (R ⊗[S] B)ˣ) : R ⊗[S] B) =
          ((a⁻¹ : (SchubertGeometry.DeterminantSection.chartAlgebra G i)ˣ) :
            SchubertGeometry.DeterminantSection.chartAlgebra G i) ∧
        Polynomial.map (Algebra.TensorProduct.includeRight : B →ₐ[S] R ⊗[S] B).toRingHom Q =
          Polynomial.C (w : R ⊗[S] B) * (Polynomial.X : Polynomial (R ⊗[S] B)) ^ 2 ∧
        (w : R ⊗[S] B) =
          (Polynomial.map (Algebra.TensorProduct.includeRight : B →ₐ[S] R ⊗[S] B).toRingHom Q).coeff
            2 := by
  obtain ⟨a, ha⟩ := oppositionChartPolynomial_square G i
  obtain ⟨R₀, hSR₀, hstage⟩ := exists_unit_stage S hS
    (fun _ : Unit => B) (fun _ : Unit => SchubertGeometry.DeterminantSection.chartAlgebra G i)
    (fun _ : Unit => e) (fun _ : Unit => vars) (fun _ : Unit => rels)
    (fun _ : Unit => presentation) (fun _ : Unit => a)
  let : Algebra S R₀ := (Subalgebra.inclusion hSR₀).toAlgebra
  let : IsScalarTower S R₀ K := Subalgebra.inclusion.isScalarTower_right hSR₀ K
  obtain ⟨hR₀, d, hd, _⟩ := hstage
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
  let m := Algebra.TensorProduct.map f (AlgHom.id S B)
  let w : (R ⊗[S] B)ˣ := Units.map m.toRingHom.toMonoidHom (d ())
  have hw : scalarMap (R := R) e (w : R ⊗[S] B) =
      (a : SchubertGeometry.DeterminantSection.chartAlgebra G i) := by
    exact (scalar_extension e f hf (d () : R₀ ⊗[S] B)).trans (hd ())
  have hinj : Function.Injective (scalarMap (R := R) e) :=
    scalar_injective e (show Function.Injective (algebraMap R K) from Subtype.val_injective)
  have hsquare := square_reflection
    (Algebra.TensorProduct.includeRight : B →ₐ[S] R ⊗[S] B).toRingHom
    (scalarMap (R := R) e) (coefficientMap e) (scalar_factor e) hinj Q a w (hQ.trans ha) hw
  refine ⟨R, hSR, le_sup_right, hR₀.sup hstart, a, w, ha, hw, ?_, hsquare, ?_⟩
  · exact unit_inverse_value (scalarMap (R := R) e) w a hw
  · exact square_coefficient _ w hsquare

end SchubertGeometry.DeterminantSection
