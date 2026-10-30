import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.MatchingOperatorOverlaps
import OrbitComplexity.FrobeniusSplitting.Normality.Assembly.PolynomialSectionCovariance
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Polynomial sections under affine coframe refinement

A section in two polynomial coframes determines its entire transition
polynomial. Coefficient extension and the affine change of coordinate are
treated by one ring map. Normalization of the highest coefficient determines
the coframe factor from its coefficient and the affine slope.
-/

set_option autoImplicit false

noncomputable section
universe u

open AlgebraicGeometry CategoryTheory Polynomial
open AlgebraicGeometry.Scheme.Modules
open FrobeniusSplitting FrobeniusSplitting.CharacterLine
open FrobeniusSplitting.RetainedCharacter

namespace SchubertGeometry.RetainedCharacter

open private unitModule from
  OrbitComplexity.FrobeniusSplitting.Normality.Assembly.PolynomialSectionCovariance
open private affinePolynomialMap affinePolynomialMap_apply from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.MatchingOperatorOverlaps

/-- A common section in affine polynomial coframes has its full covariance
identity under coefficient extension and an affine coordinate change. -/
theorem polynomialCoframe_refine {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) {p : ℕ} (phi : FrobeniusLinearMap B p) (hp : 1 < p)
    (P : Polynomial A) (Q : Polynomial B) (n : ℕ)
    (hP : (Polynomial.map f P).natDegree ≤ n) (a delta : Bˣ) (b : B)
    {L : (Spec (.of (Polynomial A))).Modules}
    {M : (Spec (.of (Polynomial B))).Modules}
    (s : unitModule (Spec (.of (Polynomial A))) ⟶ L)
    (t : unitModule (Spec (.of (Polynomial B))) ⟶ M)
    (H : M ≅ (Scheme.Modules.pullback
      (Spec.map (CommRingCat.ofHom (affinePolynomialMap f a b)))).obj L)
    (E : L ≅ unitModule (Spec (.of (Polynomial A))))
    (F : M ≅ unitModule (Spec (.of (Polynomial B))))
    (hs : s ≫ E.hom = globalSectionsSmul (unitModule (Spec (.of (Polynomial A))))
      ((Scheme.ΓSpecIso (.of (Polynomial A))).inv P))
    (ht : t ≫ F.hom = globalSectionsSmul (unitModule (Spec (.of (Polynomial B))))
      ((Scheme.ΓSpecIso (.of (Polynomial B))).inv Q))
    (hsection : t ≫ H.hom =
      (pullbackObjUnitIso (Spec.map (CommRingCat.ofHom (affinePolynomialMap f a b)))).inv ≫
        (Scheme.Modules.pullback
          (Spec.map (CommRingCat.ofHom (affinePolynomialMap f a b)))).map s)
    (hcoeff : Q.coeff n = (delta : B) * (Polynomial.map f P).coeff n)
    (hnormalized : phi ((Polynomial.map f P).coeff n) = 1) :
    Q = C ((delta : B) * (↑(a⁻¹) : B) ^ n) *
      (Polynomial.map f P).comp (C (a : B) * X + C b) := by
  let g : Polynomial A →+* Polynomial B := affinePolynomialMap f a b
  let U : (Polynomial B)ˣ := affineCoframeUnit (Polynomial B)
    (H ≪≫ (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom g))).mapIso E ≪≫
      pullbackObjUnitIso (Spec.map (CommRingCat.ofHom g))) F
  have hU : Q = (U : Polynomial B) *
      (Polynomial.map f P).comp (C (a : B) * X + C b) := by
    have h := coframe_section_transport g s t H E F P Q hs ht hsection
    rw [affinePolynomialMap_apply] at h
    exact h
  exact polynomialCoframe_section_eq phi hp Q (Polynomial.map f P) n hP
    a delta b U hU hcoeff hnormalized

end SchubertGeometry.RetainedCharacter
