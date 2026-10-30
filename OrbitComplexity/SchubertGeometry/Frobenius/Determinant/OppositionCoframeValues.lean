import OrbitComplexity.SchubertGeometry.Frobenius.Determinant.OppositionPolynomialChart
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.MatchingFamilySections
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Determinant coefficients in retained flag coframes

The whole coframes furnished by the polynomial-coframe family determine the
coefficients of the original determinant sections. On a transverse root chart
their scalar extensions are the determinant polynomials, in every character
degree and on the same coefficient model.
-/

set_option autoImplicit false
noncomputable section
universe u

open AlgebraicGeometry CategoryTheory Opposite
open AlgebraicGeometry.Scheme.Modules
open ReductiveGroups GroupActions FrobeniusSplitting

open private pullSection from
  OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.PullbackFrames
open private sectionValue from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendSectionCoordinates
open private unitValue unit_hom_eq_smul from
  OrbitComplexity.FrobeniusSplitting.Normality.Assembly.FrameReflection
open private pulled_section_coordinate scalar_hom_injective from
  OrbitComplexity.FrobeniusSplitting.Normality.Assembly.SectionCoframeTransport
open private whole_section compared_section chart_coordinate_map from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.MatchingFamilySections
open private wholeComparison comparedWholeFrame polynomialFineCoframe from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.CommonPolynomialCoframes
open private SchubertGeometry.DeterminantSection.chartAlgebra from
  OrbitComplexity.SchubertGeometry.Frobenius.Determinant.OppositionPolynomial

namespace SchubertGeometry.DeterminantSection

private abbrev unitModule (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

private theorem coefficient_pullback {Y YK P PK Z : Scheme.{u}}
    (n : YK ⟶ Y) (f : P ⟶ Y) (g : PK ⟶ YK) (z : PK ⟶ P)
    (h : z ≫ f = g ≫ n) (r : YK ⟶ Z) (c : PK ⟶ Z)
    (hc : g ≫ r = c) (L : Y.Modules) (LK : Z.Modules)
    (EL : (pullback n).obj L ≅ (pullback r).obj LK)
    (s : unitModule Y ⟶ L) (t : unitModule Z ⟶ LK)
    (hs : pullSection n L s ≫ EL.hom = pullSection r LK t)
    (E : (pullback c).obj LK ≅ unitModule PK)
    (F : (pullback f).obj L ≅ unitModule P)
    (hF : (pullback z).mapIso F ≪≫ pullbackObjUnitIso z =
      wholeComparison n f g z h L ≪≫
        comparedWholeFrame r g c hc ((pullback n).obj L) LK EL E)
    (b : Γ(PK, ⊤)) (ht : sectionValue c LK t E.hom b) :
    z.appTop (unitValue (pullSection f L s ≫ F.hom)) = b := by
  have hleft := pulled_section_coordinate z (pullSection f L s) F
    (unitValue (pullSection f L s ≫ F.hom))
    (unit_hom_eq_smul (pullSection f L s ≫ F.hom))
  have hright := compared_section r g c hc ((pullback n).obj L) LK EL E
    (pullSection n L s) t hs b ht
  have hwhole := whole_section n f g z h L s
  apply scalar_hom_injective
  calc
    globalSectionsSmul (unitModule PK)
        (z.appTop (unitValue (pullSection f L s ≫ F.hom))) =
        pullSection z ((pullback f).obj L) (pullSection f L s) ≫
          ((pullback z).mapIso F ≪≫ pullbackObjUnitIso z).hom := hleft.symm
    _ = pullSection z ((pullback f).obj L) (pullSection f L s) ≫
          (wholeComparison n f g z h L).hom ≫
          (comparedWholeFrame r g c hc ((pullback n).obj L) LK EL E).hom := by
      rw [hF]
      rfl
    _ = globalSectionsSmul (unitModule PK) b := by
      rw [← Category.assoc, hwhole, hright]

private theorem chart_value_inverse {A : Type u} [CommRing A]
    {P : Scheme.{u}} (e : P ≅ Spec (.of A)) (a : Γ(P, ⊤)) :
    e.hom.appTop ((Scheme.ΓSpecIso (.of A)).inv
      ((Scheme.ΓSpecIso (.of A)).hom (e.inv.appTop a))) = a := by
  have hΓ : (Scheme.ΓSpecIso (.of A)).inv
      ((Scheme.ΓSpecIso (.of A)).hom (e.inv.appTop a)) = e.inv.appTop a := by
    exact ConcreteCategory.congr_hom (Scheme.ΓSpecIso (.of A)).hom_inv_id _
  rw [hΓ, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
    e.hom_inv_id, Scheme.Hom.id_appTop]
  rfl

private theorem polynomial_value_map {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) {P PK : Scheme.{u}} (e : P ≅ Spec (.of (Polynomial A)))
    (b : PK ⟶ P) (d : Spec (.of (Polynomial B)) ⟶ PK)
    (h : (d ≫ b) ≫ e.hom = Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom φ)))
    (a : Γ(P, ⊤)) (q : Polynomial B)
    (ha : d.appTop (b.appTop a) = (Scheme.ΓSpecIso (.of (Polynomial B))).inv q) :
    Polynomial.map φ ((Scheme.ΓSpecIso (.of (Polynomial A))).hom (e.inv.appTop a)) = q := by
  let p := (Scheme.ΓSpecIso (.of (Polynomial A))).hom (e.inv.appTop a)
  have hp := chart_coordinate_map (Polynomial.mapRingHom φ) e (d ≫ b) h p
  have hc := chart_value_inverse e a
  have he : (Scheme.ΓSpecIso (.of (Polynomial B))).inv (Polynomial.map φ p) =
      (Scheme.ΓSpecIso (.of (Polynomial B))).inv q := by
    calc
      _ = (d ≫ b).appTop (e.hom.appTop
          ((Scheme.ΓSpecIso (.of (Polynomial A))).inv p)) := hp.symm
      _ = d.appTop (b.appTop a) := by
        rw [hc, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
      _ = _ := ha
  calc
    Polynomial.map φ p = (Scheme.ΓSpecIso (.of (Polynomial B))).hom
        ((Scheme.ΓSpecIso (.of (Polynomial B))).inv (Polynomial.map φ p)) :=
      (ConcreteCategory.congr_hom (Scheme.ΓSpecIso (.of (Polynomial B))).inv_hom_id _).symm
    _ = (Scheme.ΓSpecIso (.of (Polynomial B))).hom
        ((Scheme.ΓSpecIso (.of (Polynomial B))).inv q) := congrArg _ he
    _ = q := ConcreteCategory.congr_hom (Scheme.ΓSpecIso (.of (Polynomial B))).inv_hom_id _

private theorem section_specializes {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) {P : Scheme.{u}} (e : P ≅ Spec (.of A))
    (L : P.Modules) (s : unitModule P ⟶ L) (F : L ≅ unitModule P)
    (a : Γ(P, ⊤))
    (ha : s ≫ F.hom = globalSectionsSmul (unitModule P) a) :
    let f := Spec.map (CommRingCat.ofHom φ) ≫ e.inv
    pullSection f L s ≫ ((pullback f).mapIso F ≪≫ pullbackObjUnitIso f).hom =
      globalSectionsSmul (unitModule (Spec (.of B)))
        ((Scheme.ΓSpecIso (.of B)).inv
          (φ ((Scheme.ΓSpecIso (.of A)).hom (e.inv.appTop a)))) := by
  dsimp only
  have h := pulled_section_coordinate (Spec.map (CommRingCat.ofHom φ) ≫ e.inv) s F a ha
  have hcoord := chart_coordinate_map φ e (Spec.map (CommRingCat.ofHom φ) ≫ e.inv)
    (by rw [Category.assoc, e.inv_hom_id, Category.comp_id])
    ((Scheme.ΓSpecIso (.of A)).hom (e.inv.appTop a))
  rw [chart_value_inverse e a] at hcoord
  exact h.trans (congrArg (globalSectionsSmul (unitModule (Spec (.of B)))) hcoord)

private theorem section_triangle {P Q U H : Scheme.{u}}
    (d : P ⟶ Q) (a : Q ⟶ U) (b c : U ⟶ H) (t : P ⟶ U) (q : P ⟶ H)
    (ha : d ≫ a = t) (hb : b = c) (hq : q = t ≫ c)
    (s : Γ(H, ⊤)) (v : Γ(P, ⊤)) (hv : q.appTop s = v) :
    d.appTop ((a ≫ b).appTop s) = v := by
  calc
    _ = (d ≫ (a ≫ b)).appTop s := by
      simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
    _ = q.appTop s := by rw [← Category.assoc, ha, hb, hq]
    _ = v := hv

private theorem value_join {A B : Type u} (f : A → B) (a b : A) (c : B)
    (hab : a = b) (hbc : f b = c) : f a = c :=
  (congrArg f hab).trans hbc

private theorem section_inverse {K : Type u} [Field K] (A : Type u)
    [CommRing A] [Algebra K A] [IsReduced A] [Algebra.FiniteType K A] (v : A) :
    affineSection (K := K) A v = (Scheme.ΓSpecIso (.of A)).inv v := rfl

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K)

private def chartFlag {I : Type u} (P : I → Scheme.{u}) (point : I → G.points)
    (a : ∀ i, P i ⟶ (oppositeUnipotentVariety G).toOver.left) (i : I) :
    P i ⟶ (flagVariety G).toOver.left :=
  a i ≫ (flagChartMorphism G (point i)).left

private def chartFrame {I : Type u} (P : I → Scheme.{u}) (point : I → G.points)
    (a : ∀ i, P i ⟶ (oppositeUnipotentVariety G).toOver.left) (N : ℕ) (i : I) :
    (pullback (chartFlag G P point a i)).obj
      (CharacterLine.flagCharacterModule G (G.positiveRootCharacter ^ N)) ≅ unitModule (P i) :=
  CharacterLine.flagCharacterPullbackIso G (point i) (G.positiveRootCharacter ^ N) (a i)

private def chartValue {I : Type u} (P : I → Scheme.{u}) (point : I → G.points)
    (a : ∀ i, P i ⟶ (oppositeUnipotentVariety G).toOver.left) (N : ℕ) (i : I) :
    Γ(P i, ⊤) :=
  (a i ≫ (flagChartMap G (point i)).left).appTop (positiveDetPowerFunction G N)

private theorem chart_section {I : Type u} (P : I → Scheme.{u}) (point : I → G.points)
    (a : ∀ i, P i ⟶ (oppositeUnipotentVariety G).toOver.left) (N : ℕ) (i : I) :
    sectionValue (chartFlag G P point a i)
      (CharacterLine.flagCharacterModule G (G.positiveRootCharacter ^ N))
      (CharacterLine.flagDeterminantModuleSection G N)
      (chartFrame G P point a N i).hom (chartValue G P point a N i) := by
  exact CharacterLine.flagDeterminantPullback_frame G N (point i) (a i)

/-- The original sections in the polynomial-coframe family have the transverse
root determinant coefficients in every degree, and retain these section
coordinates after every coefficient specialization. -/
theorem oppositionCoframe_coefficients
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
    (g : ∀ i, P i ⟶ YK) (hc : ∀ i, g i ≫ r = chartFlag G P point a i)
    (z : ∀ v, P (index v) ⟶ V.X v)
    (hwhole : ∀ v, z v ≫ V.f v = g (index v) ≫ n)
    (hfamily : ∀ N, RetainedCharacter.scalarPolynomialCoframeFamily n r (L N)
      (CharacterLine.flagCharacterModule G (G.positiveRootCharacter ^ N)) (EL N)
      W V index P g (chartFlag G P point a) hc (chartFrame G P point a N) z hwhole)
    (v : V.I₀) (i : G.rootBase.support) {B : Type u} [CommRing B]
    (φ : B →+* SchubertGeometry.DeterminantSection.chartAlgebra G i)
    (e : V.X v ≅ Spec (.of (Polynomial B)))
    (d : (affineVariety K (Polynomial (SchubertGeometry.DeterminantSection.chartAlgebra G
      i))).toOver.left ⟶ P (index v))
    (hd : d ≫ a (index v) = (oppositionPolynomialIso G i).hom.left)
    (hpoint : point (index v) = oppositionChartPoint G i)
    (he : (d ≫ z v) ≫ e.hom = Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom φ))) :
    ∀ N, ∃ (E : ∀ w : W.I₀, (pullback ((SchubertGeometry.appendCommonCover W V).f ⟨w, v⟩)).obj (L N)
      ≅
        unitModule ((SchubertGeometry.commonPolynomialCover W V v).X w))
        (F : (pullback (V.f v)).obj (L N) ≅ unitModule (V.X v)) (Q : Polynomial B),
      (∀ w, F.hom.over ((SchubertGeometry.commonPolynomialCover W V v).f w).opensRange =
          (FrobeniusSplitting.OperatorSheaf.coframeOverRange
            ((SchubertGeometry.commonPolynomialCover W V v).f w) _
            (polynomialFineCoframe W V v (L N) E w)).hom ∧
        F.inv.over ((SchubertGeometry.commonPolynomialCover W V v).f w).opensRange =
          (FrobeniusSplitting.OperatorSheaf.coframeOverRange
            ((SchubertGeometry.commonPolynomialCover W V v).f w) _
            (polynomialFineCoframe W V v (L N) E w)).inv) ∧
      (pullback (z v)).mapIso F ≪≫ pullbackObjUnitIso (z v) =
        wholeComparison n (V.f v) (g (index v)) (z v) (hwhole v) (L N) ≪≫
          comparedWholeFrame r (g (index v)) (chartFlag G P point a (index v)) (hc (index v))
            ((pullback n).obj (L N))
            (CharacterLine.flagCharacterModule G (G.positiveRootCharacter ^ N)) (EL N)
            (chartFrame G P point a N (index v)) ∧
      Polynomial.map φ Q = oppositionChartPolynomial G i N ∧
      pullSection (V.f v) (L N) (s N) ≫ F.hom =
        globalSectionsSmul (unitModule (V.X v))
          (e.hom.appTop ((Scheme.ΓSpecIso (.of (Polynomial B))).inv Q)) ∧
      (∀ (T : Type u) [CommRing T] (k : B →+* T),
        let f := Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom k)) ≫ e.inv
        pullSection f ((pullback (V.f v)).obj (L N)) (pullSection (V.f v) (L N) (s N)) ≫
          ((pullback f).mapIso F ≪≫ pullbackObjUnitIso f).hom =
        globalSectionsSmul (unitModule (Spec (.of (Polynomial T))))
          ((Scheme.ΓSpecIso (.of (Polynomial T))).inv (Polynomial.map k Q))) := by
  intro N
  obtain ⟨E, F, hlocal, hF⟩ := hfamily N v
  let value := unitValue (pullSection (V.f v) (L N) (s N) ≫ F.hom)
  let Q := (Scheme.ΓSpecIso (.of (Polynomial B))).hom (e.inv.appTop value)
  have hvalue : (z v).appTop value = chartValue G P point a N (index v) :=
    coefficient_pullback n (V.f v) (g (index v)) (z v) (hwhole v) r
      (chartFlag G P point a (index v)) (hc (index v)) (L N)
      (CharacterLine.flagCharacterModule G (G.positiveRootCharacter ^ N)) (EL N)
      (s N) (CharacterLine.flagDeterminantModuleSection G N) (hs N)
      (chartFrame G P point a N (index v)) F hF
      (chartValue G P point a N (index v)) (chart_section G P point a N (index v))
  have hfunction := oppositionPolynomialIso_function G i N
  have htriangle := section_triangle d (a (index v)) (flagChartMap G (point (index v))).left
    (flagChartMap G (oppositionChartPoint G i)).left (oppositionPolynomialIso G i).hom.left
    ((oppositionPolynomialIso G i).hom ≫ flagChartMap G (oppositionChartPoint G i)).left
    hd (congrArg (fun t => (flagChartMap G t).left) hpoint) rfl
    (positiveDetPowerFunction G N)
    (affineSection (K := K) (Polynomial (SchubertGeometry.DeterminantSection.chartAlgebra G i))
      (oppositionChartPolynomial G i N)) hfunction
  have hinverse := section_inverse (K := K)
    (Polynomial (SchubertGeometry.DeterminantSection.chartAlgebra G i))
    (oppositionChartPolynomial G i N)
  have hpoly : d.appTop ((z v).appTop value) =
      (Scheme.ΓSpecIso (.of (Polynomial (SchubertGeometry.DeterminantSection.chartAlgebra G
        i)))).inv
        (oppositionChartPolynomial G i N) := by
    exact value_join d.appTop.hom ((z v).appTop value)
      (chartValue G P point a N (index v)) _ hvalue (htriangle.trans hinverse)
  refine ⟨E, F, Q, hlocal, hF, ?_, ?_, ?_⟩
  · exact polynomial_value_map φ e (z v) d he value (oppositionChartPolynomial G i N) hpoly
  · exact (unit_hom_eq_smul _).trans
      (congrArg (globalSectionsSmul (unitModule (V.X v))) (chart_value_inverse e value).symm)
  · intro T _ k
    exact section_specializes (Polynomial.mapRingHom k) e _ _ F value (unit_hom_eq_smul _)

end SchubertGeometry.DeterminantSection
