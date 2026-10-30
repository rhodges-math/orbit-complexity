import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.GlobalSectionCovariance
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Covariance from matching section coefficients

The matching coefficient equation determines the inverse adjusted frame
factor. Weighting the normalized target prior map by this factor supplies
the normalization used to determine the entire section polynomial.
-/

set_option autoImplicit false

noncomputable section
universe u

open AlgebraicGeometry CategoryTheory Polynomial
open FrobeniusSplitting FrobeniusSplitting.CharacterLine
open FrobeniusSplitting.RetainedCharacter

namespace SchubertGeometry.RetainedCharacter

open private sectionValue from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendSectionCoordinates
open private affinePolynomialMap from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.MatchingOperatorOverlaps

private theorem adjusted_power_ratio {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (r : A) (s : B) (delta : Bˣ) (d : Aˣ) (e : Bˣ)
    (n : ℕ) (hr : f r = (delta : B) * s) :
    (s * (e : B)) ^ n =
      ((((delta * Units.map f.toMonoidHom d * e⁻¹) ^ n)⁻¹ : Bˣ) : B) *
        f ((r * (d : A)) ^ n) := by
  let u : Bˣ := delta * Units.map f.toMonoidHom d * e⁻¹
  have hue : (u : B) * (e : B) = (delta : B) * f (d : A) := by
    calc
      _ = (((delta * Units.map f.toMonoidHom d * e⁻¹) * e : Bˣ) : B) := rfl
      _ = ((delta * Units.map f.toMonoidHom d : Bˣ) : B) := by
        congr 1
        simp only [mul_assoc, inv_mul_cancel, mul_one]
      _ = _ := rfl
  have hbase : f (r * (d : A)) = (u : B) * (s * (e : B)) := by
    rw [map_mul, hr]
    calc
      _ = ((delta : B) * f (d : A)) * s := by ring
      _ = ((u : B) * (e : B)) * s := congrArg (fun x : B => x * s) hue.symm
      _ = _ := by ring
  have hpow : f ((r * (d : A)) ^ n) =
      ((u ^ n : Bˣ) : B) * (s * (e : B)) ^ n := by
    rw [map_pow, hbase, mul_pow]
    rfl
  symm
  calc
    _ = (((u ^ n)⁻¹ : Bˣ) : B) *
        (((u ^ n : Bˣ) : B) * (s * (e : B)) ^ n) :=
      congrArg (fun x : B => (((u ^ n)⁻¹ : Bˣ) : B) * x) hpow
    _ = _ := by rw [← mul_assoc, Units.inv_mul, one_mul]

/-- Matching coefficient transport and target prior normalization determine
the full polynomial covariance of a single global section in adjusted frames. -/
theorem matchingPolynomial_covariance {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) {p : ℕ} (psi : FrobeniusLinearMap B p) (hp : 1 < p)
    (r : A) (t : B) (delta : Bˣ) (d : Aˣ) (e : Bˣ) (n : ℕ)
    (hr : f r = (delta : B) * t)
    (P : Polynomial A) (Q : Polynomial B)
    (hdegree : (Polynomial.map f P).natDegree ≤ p - 1)
    (hP : P.coeff (p - 1) = (r * (d : A)) ^ n)
    (hQ : Q.coeff (p - 1) = (t * (e : B)) ^ n)
    (hnormalized : psi ((t * (e : B)) ^ n) = 1) (a : Bˣ) (b : B)
    (Z : Scheme.{u}) (L : Z.Modules)
    (s : SheafOfModules.unit Z.ringCatSheaf ⟶ L)
    (j : Spec (.of (Polynomial A)) ⟶ Z)
    (k : Spec (.of (Polynomial B)) ⟶ Z)
    (htriangle : k = Spec.map (CommRingCat.ofHom (affinePolynomialMap f a b)) ≫ j)
    (E : (Scheme.Modules.pullback j).obj L ≅
      SheafOfModules.unit (Spec (.of (Polynomial A))).ringCatSheaf)
    (F : (Scheme.Modules.pullback k).obj L ≅
      SheafOfModules.unit (Spec (.of (Polynomial B))).ringCatSheaf)
    (hs : sectionValue j L s E.hom ((Scheme.ΓSpecIso (.of (Polynomial A))).inv P))
    (ht : sectionValue k L s F.hom ((Scheme.ΓSpecIso (.of (Polynomial B))).inv Q)) :
    Q = C (((((delta * Units.map f.toMonoidHom d * e⁻¹) ^ n)⁻¹ : Bˣ) : B) *
        (↑(a⁻¹) : B) ^ (p - 1)) *
      (Polynomial.map f P).comp (C (a : B) * X + C b) := by
  let c : Bˣ := ((delta * Units.map f.toMonoidHom d * e⁻¹) ^ n)⁻¹
  have hc : Q.coeff (p - 1) = (c : B) * (Polynomial.map f P).coeff (p - 1) := by
    calc
      _ = (t * (e : B)) ^ n := hQ
      _ = (c : B) * f ((r * (d : A)) ^ n) :=
        adjusted_power_ratio f r t delta d e n hr
      _ = _ := by rw [Polynomial.coeff_map, hP]
  have hn : psi.weight (c : B) ((Polynomial.map f P).coeff (p - 1)) = 1 := by
    rw [FrobeniusLinearMap.weight_apply, ← hc, hQ]
    exact hnormalized
  exact globalPolynomial_covariance f (psi.weight (c : B)) hp P Q (p - 1)
    hdegree a c b Z L s j k htriangle E F hs ht hc hn

end SchubertGeometry.RetainedCharacter
