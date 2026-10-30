import OrbitComplexity.SchubertGeometry.Frobenius.Determinant.OppositionCoframeValues
import OrbitComplexity.FrobeniusSplitting.Normality.ModelFlat
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Powers of determinant coordinates on a common coefficient model

Flatness makes the coefficient comparison injective. The determinant formulas
therefore identify every retained section coefficient with the corresponding
power of its degree-one coefficient, on the same model and in the same coframes.
-/

set_option autoImplicit false
noncomputable section
universe u

open AlgebraicGeometry CategoryTheory Opposite
open AlgebraicGeometry.Scheme.Modules
open ReductiveGroups GroupActions FrobeniusSplitting
open scoped TensorProduct

open private pullSection from
  OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.PullbackFrames
open private wholeComparison comparedWholeFrame polynomialFineCoframe from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.CommonPolynomialCoframes
open private SchubertGeometry.DeterminantSection.chartAlgebra from
  OrbitComplexity.SchubertGeometry.Frobenius.Determinant.OppositionPolynomial
open private SchubertGeometry.DeterminantSection.chartFlag
  SchubertGeometry.DeterminantSection.chartFrame from
  OrbitComplexity.SchubertGeometry.Frobenius.Determinant.OppositionCoframeValues

namespace SchubertGeometry.DeterminantSection

private abbrev unitModule (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

private def coefficientMap {S K B A : Type u}
    [CommRing S] [CommRing K] [CommRing B] [CommRing A]
    [Algebra S K] [Algebra S B] [Algebra K A] (e : K ⊗[S] B ≃ₐ[K] A) : B →+* A :=
  e.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom

private theorem coefficientMap_injective {S K B A : Type u}
    [CommRing S] [CommRing K] [CommRing B] [CommRing A]
    [Algebra S K] [Algebra S B] [Algebra K A] [Module.Flat S B]
    (e : K ⊗[S] B ≃ₐ[K] A) (hi : Function.Injective (algebraMap S K)) :
    Function.Injective (coefficientMap e) := by
  let : Algebra S A := ((algebraMap K A).comp (algebraMap S K)).toAlgebra
  let : IsScalarTower S K A := IsScalarTower.of_algebraMap_eq' rfl
  exact tensorImageHom_injective e hi

private theorem coefficient_family_power {R A : Type u} [CommRing R] [CommRing A]
    (f : R →+* A) (a : R) (P : ℕ → Polynomial A)
    (hP : ∀ N, P N = Polynomial.C (f (a ^ N)) * Polynomial.X ^ (2 * N)) (N : ℕ) :
    P N = P 1 ^ N := by
  rw [hP N, hP 1]
  simp only [pow_one, mul_one, map_pow, mul_pow, pow_mul]

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K)

private theorem determinant_polynomial_power (i : G.rootBase.support) (N : ℕ) :
    oppositionChartPolynomial G i N = oppositionChartPolynomial G i 1 ^ N := by
  obtain ⟨a, ha⟩ := oppositionChartPolynomial_formula G i
  exact coefficient_family_power
    (algebraMap K (SchubertGeometry.DeterminantSection.chartAlgebra G i)) (a : K)
    (oppositionChartPolynomial G i) ha N

/-- The coframes obtained from the common polynomial-coframe family give powers
of one degree-one determinant coefficient after every specialization. -/
theorem oppositionCoframe_power_family
    {Y YK : Scheme.{u}} (n : YK ⟶ Y) (r : YK ⟶ (flagVariety G).toOver.left)
    (L : ℕ → Y.Modules)
    (EL : ∀ N, (pullback n).obj (L N) ≅
      (pullback r).obj (CharacterLine.flagCharacterModule G (G.positiveRootCharacter ^ N)))
    (s : ∀ N, unitModule Y ⟶ L N)
    (hs : ∀ N, pullSection n (L N) (s N) ≫ (EL N).hom =
      pullSection r (CharacterLine.flagCharacterModule G (G.positiveRootCharacter ^ N))
        (CharacterLine.flagDeterminantModuleSection G N))
    (W V : Y.OpenCover.{u}) {I : Type u} (index : V.I₀ → I)
    (P : I → Scheme.{u}) (point : I → G.points)
    (a : ∀ i, P i ⟶ (oppositeUnipotentVariety G).toOver.left)
    (g : ∀ i, P i ⟶ YK) (hc : ∀ i, g i ≫ r = SchubertGeometry.DeterminantSection.chartFlag G P point
      a i)
    (z : ∀ v, P (index v) ⟶ V.X v)
    (hwhole : ∀ v, z v ≫ V.f v = g (index v) ≫ n)
    (hfamily : ∀ N, RetainedCharacter.scalarPolynomialCoframeFamily n r (L N)
      (CharacterLine.flagCharacterModule G (G.positiveRootCharacter ^ N)) (EL N)
      W V index P g (SchubertGeometry.DeterminantSection.chartFlag G P point a) hc
        (SchubertGeometry.DeterminantSection.chartFrame G P point a N) z hwhole)
    (v : V.I₀) (i : G.rootBase.support) (S : Subalgebra ℤ K)
    {B : Type u} [CommRing B] [Algebra S B] [Module.Flat S B]
    (eCoefficient : K ⊗[S] B ≃ₐ[K] SchubertGeometry.DeterminantSection.chartAlgebra G i)
    (e : V.X v ≅ Spec (.of (Polynomial B)))
    (d : (affineVariety K (Polynomial (SchubertGeometry.DeterminantSection.chartAlgebra G
      i))).toOver.left ⟶ P (index v))
    (hd : d ≫ a (index v) = (oppositionPolynomialIso G i).hom.left)
    (hpoint : point (index v) = oppositionChartPoint G i)
    (he : (d ≫ z v) ≫ e.hom = Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (coefficientMap
      eCoefficient)))) :
    ∃ (E : ∀ N, ∀ w : W.I₀,
        (pullback ((SchubertGeometry.appendCommonCover W V).f ⟨w, v⟩)).obj (L N) ≅
          unitModule ((SchubertGeometry.commonPolynomialCover W V v).X w))
      (F : ∀ N, (pullback (V.f v)).obj (L N) ≅ unitModule (V.X v))
      (Q : ℕ → Polynomial B),
    (∀ N,
      (∀ w, (F N).hom.over ((SchubertGeometry.commonPolynomialCover W V v).f w).opensRange =
          (FrobeniusSplitting.OperatorSheaf.coframeOverRange
            ((SchubertGeometry.commonPolynomialCover W V v).f w) _
            (polynomialFineCoframe W V v (L N) (E N) w)).hom ∧
        (F N).inv.over ((SchubertGeometry.commonPolynomialCover W V v).f w).opensRange =
          (FrobeniusSplitting.OperatorSheaf.coframeOverRange
            ((SchubertGeometry.commonPolynomialCover W V v).f w) _
            (polynomialFineCoframe W V v (L N) (E N) w)).inv) ∧
      (pullback (z v)).mapIso (F N) ≪≫ pullbackObjUnitIso (z v) =
        wholeComparison n (V.f v) (g (index v)) (z v) (hwhole v) (L N) ≪≫
          comparedWholeFrame r (g (index v)) (SchubertGeometry.DeterminantSection.chartFlag G P
            point a (index v)) (hc (index v))
            ((pullback n).obj (L N))
            (CharacterLine.flagCharacterModule G (G.positiveRootCharacter ^ N)) (EL N)
            (SchubertGeometry.DeterminantSection.chartFrame G P point a N (index v)) ∧
      Polynomial.map (coefficientMap eCoefficient) (Q N) = oppositionChartPolynomial G i N ∧
      pullSection (V.f v) (L N) (s N) ≫ (F N).hom =
        globalSectionsSmul (unitModule (V.X v))
          (e.hom.appTop ((Scheme.ΓSpecIso (.of (Polynomial B))).inv (Q N))) ∧
      (∀ (T : Type u) [CommRing T] (k : B →+* T),
        let f := Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom k)) ≫ e.inv
        pullSection f ((pullback (V.f v)).obj (L N)) (pullSection (V.f v) (L N) (s N)) ≫
          ((pullback f).mapIso (F N) ≪≫ pullbackObjUnitIso f).hom =
        globalSectionsSmul (unitModule (Spec (.of (Polynomial T))))
          ((Scheme.ΓSpecIso (.of (Polynomial T))).inv (Polynomial.map k (Q N)))) ) ∧
    ∀ N, Q N = Q 1 ^ N := by
  classical
  have hcert := oppositionCoframe_coefficients G n r L EL s hs W V index P point a g hc z
    hwhole hfamily v i (coefficientMap eCoefficient) e d hd hpoint he
  choose E F Q hcert using hcert
  refine ⟨E, F, Q, hcert, ?_⟩
  intro N
  have hi : Function.Injective (coefficientMap eCoefficient) :=
    coefficientMap_injective eCoefficient
      (show Function.Injective (algebraMap S K) from Subtype.val_injective)
  apply Polynomial.map_injective (coefficientMap eCoefficient) hi
  rw [(hcert N).2.2.1, Polynomial.map_pow, (hcert 1).2.2.1]
  exact determinant_polynomial_power G i N

end SchubertGeometry.DeterminantSection
