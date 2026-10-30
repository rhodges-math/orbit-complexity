import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.MatchingSectionCovariance
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendSectionCoordinates
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Covariance of one global section in polynomial charts

The two chart sections are pullbacks of one section on one scheme. Their
commuting triangle determines the section comparison, and their polynomial
coframes determine the full affine covariance identity.
-/

set_option autoImplicit false

noncomputable section
universe u

open AlgebraicGeometry CategoryTheory Polynomial
open AlgebraicGeometry.Scheme.Modules
open FrobeniusSplitting FrobeniusSplitting.CharacterLine
open FrobeniusSplitting.RetainedCharacter

namespace SchubertGeometry.RetainedCharacter

open private pullSection pullSection_comp pullSection_congr from
  OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.PullbackFrames
open private sectionValue from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendSectionCoordinates
open private affinePolynomialMap from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.MatchingOperatorOverlaps

private def triangleIso {X Y Z : Scheme.{u}} (f : X ⟶ Y)
    (a : Y ⟶ Z) (b : X ⟶ Z) (h : b = f ≫ a) (L : Z.Modules) :
    (Scheme.Modules.pullback b).obj L ≅
      (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback a).obj L) :=
  (Scheme.Modules.pullbackCongr h).app L ≪≫
    ((Scheme.Modules.pullbackComp f a).app L).symm

private theorem triangle_section {X Y Z : Scheme.{u}} (f : X ⟶ Y)
    (a : Y ⟶ Z) (b : X ⟶ Z) (h : b = f ≫ a) (L : Z.Modules)
    (s : SheafOfModules.unit Z.ringCatSheaf ⟶ L) :
    pullSection b L s ≫ (triangleIso f a b h L).hom =
      (pullbackObjUnitIso f).inv ≫
        (Scheme.Modules.pullback f).map (pullSection a L s) := by
  change pullSection b L s ≫
      ((Scheme.Modules.pullbackCongr h).hom.app L ≫
        (Scheme.Modules.pullbackComp f a).inv.app L) =
    pullSection f ((Scheme.Modules.pullback a).obj L) (pullSection a L s)
  calc
    _ = (pullSection b L s ≫ (Scheme.Modules.pullbackCongr h).hom.app L) ≫
        (Scheme.Modules.pullbackComp f a).inv.app L := (Category.assoc _ _ _).symm
    _ = pullSection (f ≫ a) L s ≫ (Scheme.Modules.pullbackComp f a).inv.app L :=
      congrArg (fun k => k ≫ (Scheme.Modules.pullbackComp f a).inv.app L)
        (pullSection_congr h L s)
    _ = _ := pullSection_comp f a L s

/-- Two polynomial charts of the same global section satisfy full covariance
from their chart triangle, coframe coefficients and prior normalization. -/
theorem globalPolynomial_covariance {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) {p : ℕ} (phi : FrobeniusLinearMap B p) (hp : 1 < p)
    (P : Polynomial A) (Q : Polynomial B) (n : ℕ)
    (hP : (Polynomial.map f P).natDegree ≤ n) (a delta : Bˣ) (b : B)
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
    (ht : sectionValue k L s F.hom ((Scheme.ΓSpecIso (.of (Polynomial B))).inv Q))
    (hcoeff : Q.coeff n = (delta : B) * (Polynomial.map f P).coeff n)
    (hnormalized : phi ((Polynomial.map f P).coeff n) = 1) :
    Q = C ((delta : B) * (↑(a⁻¹) : B) ^ n) *
      (Polynomial.map f P).comp (C (a : B) * X + C b) := by
  let g : Spec (.of (Polynomial B)) ⟶ Spec (.of (Polynomial A)) :=
    Spec.map (CommRingCat.ofHom (affinePolynomialMap f a b))
  exact polynomialCoframe_refine f phi hp P Q n hP a delta b
    (pullSection j L s) (pullSection k L s) (triangleIso g j k htriangle L) E F
    hs ht (triangle_section g j k htriangle L s) hcoeff hnormalized

end SchubertGeometry.RetainedCharacter
