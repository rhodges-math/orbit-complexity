import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.MatchingFamilySections
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.MatchingSectionBaseChange
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendMatchingCover
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Polynomial section coordinates on a prescribed word fibre

The arithmetic polynomial cover is extended once to the prescribed scalar
fibre. Its coframes and section coordinates are then transported in every
character degree on that same cover.
-/

set_option autoImplicit false
noncomputable section
universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Modules
open FrobeniusSplitting FrobeniusSplitting.CharacterLine
open FrobeniusSplitting.OperatorSheaf FrobeniusSplitting.RetainedCharacter
open scoped TensorProduct

open private pullSection pullSection_comp pullSection_frame from
  OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.PullbackFrames
open private sectionValue from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendSectionCoordinates
open private polynomial_section_map from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.MatchingSectionBaseChange
open private comparisonCoframe from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendCoframeComparison
open private wholeComparison comparedWholeFrame polynomialFineCoframe from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.CommonPolynomialCoframes
open private iso_chart_projection from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.ScalarPolynomialCover

namespace SchubertGeometry.RetainedCharacter

private abbrev unitModule (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

private def chartMap {A : Type u} [CommRing A] {P Y : Scheme.{u}}
    (e : P ≅ Spec (.of (Polynomial A))) (f : P ⟶ Y) :
    Spec (.of (Polynomial A)) ⟶ Y := e.inv ≫ f

private def chartCoframe {A : Type u} [CommRing A] {P Y : Scheme.{u}}
    (e : P ≅ Spec (.of (Polynomial A))) (f : P ⟶ Y) (L : Y.Modules)
    (F : (Scheme.Modules.pullback f).obj L ≅ unitModule P) :
    (Scheme.Modules.pullback (chartMap e f)).obj L ≅ unitModule (Spec (.of (Polynomial A))) :=
  ((pullbackComp e.inv f).app L).symm ≪≫
    (Scheme.Modules.pullback e.inv).mapIso F ≪≫ pullbackObjUnitIso e.inv

private theorem inverse_coordinate {A : CommRingCat.{u}} {P : Scheme.{u}}
    (e : P ≅ Spec A) (a : Γ(Spec A, ⊤)) : e.inv.appTop (e.hom.appTop a) = a := by
  have h := congrArg (fun f : Spec A ⟶ Spec A => f.appTop a) e.inv_hom_id
  exact h

private theorem chart_section {A : Type u} [CommRing A] {P Y : Scheme.{u}}
    (e : P ≅ Spec (.of (Polynomial A))) (f : P ⟶ Y) (L : Y.Modules)
    (s : unitModule Y ⟶ L) (F : (Scheme.Modules.pullback f).obj L ≅ unitModule P)
    (a : Γ(Spec (.of (Polynomial A)), ⊤))
    (hs : sectionValue f L s F.hom (e.hom.appTop a)) :
    sectionValue (chartMap e f) L s (chartCoframe e f L F).hom a := by
  have h0 := pullSection_comp e.inv f L s
  have h1 := pullSection_frame e.inv ((Scheme.Modules.pullback f).obj L)
    (pullSection f L s) F (e.hom.appTop a) hs
  change pullSection (e.inv ≫ f) L s ≫ (pullbackComp e.inv f).inv.app L ≫
    (Scheme.Modules.pullback e.inv).map F.hom ≫ (pullbackObjUnitIso e.inv).hom = _
  calc
    _ = (pullSection (e.inv ≫ f) L s ≫ (pullbackComp e.inv f).inv.app L) ≫
        (Scheme.Modules.pullback e.inv).map F.hom ≫ (pullbackObjUnitIso e.inv).hom := by
      simp only [Category.assoc]
    _ = pullSection e.inv ((Scheme.Modules.pullback f).obj L) (pullSection f L s) ≫
        (Scheme.Modules.pullback e.inv).map F.hom ≫ (pullbackObjUnitIso e.inv).hom :=
      congrArg (fun k => k ≫ (Scheme.Modules.pullback e.inv).map F.hom ≫
        (pullbackObjUnitIso e.inv).hom) h0
    _ = globalSectionsSmul (unitModule (Spec (.of (Polynomial A))))
        (e.inv.appTop (e.hom.appTop a)) := h1
    _ = _ := congrArg (globalSectionsSmul (unitModule (Spec (.of (Polynomial A)))))
      (inverse_coordinate e a)

private theorem pullSection_refl {X Y : Scheme.{u}} (q : Y ⟶ X)
    (L : X.Modules) (s : unitModule X ⟶ L) :
    pullSection q L s ≫ (Iso.refl ((Scheme.Modules.pullback q).obj L)).hom =
      pullSection q L s := Category.comp_id _

private abbrev coefficientMap {R K A : Type u} [CommRing R] [CommRing K] [CommRing A]
    [Algebra R K] [Algebra R A] :
    Spec (.of (Polynomial (K ⊗[R] A))) ⟶ Spec (.of (Polynomial A)) :=
  Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom
    (Algebra.TensorProduct.includeRight : A →ₐ[R] K ⊗[R] A).toRingHom))

private def fieldCoframe {R K A : Type u} [CommRing R] [CommRing K] [CommRing A]
    [Algebra R K] [Algebra R A] {X Y : Scheme.{u}} (q : Y ⟶ X)
    (k : Spec (.of (Polynomial (K ⊗[R] A))) ⟶ Y)
    (r : Spec (.of (Polynomial A)) ⟶ X)
    (h : k ≫ q = coefficientMap ≫ r) (L : X.Modules)
    (E : (Scheme.Modules.pullback r).obj L ≅ unitModule (Spec (.of (Polynomial A)))) :
    (Scheme.Modules.pullback k).obj ((Scheme.Modules.pullback q).obj L) ≅
      unitModule (Spec (.of (Polynomial (K ⊗[R] A)))) :=
  comparisonCoframe k q coefficientMap r h ((Scheme.Modules.pullback q).obj L) L
    (Iso.refl _) E

private theorem field_section {R K A : Type u} [CommRing R] [CommRing K] [CommRing A]
    [Algebra R K] [Algebra R A] {X Y : Scheme.{u}} (q : Y ⟶ X)
    (k : Spec (.of (Polynomial (K ⊗[R] A))) ⟶ Y)
    (r : Spec (.of (Polynomial A)) ⟶ X)
    (h : k ≫ q = coefficientMap ≫ r) (L : X.Modules) (s : unitModule X ⟶ L)
    (E : (Scheme.Modules.pullback r).obj L ≅ unitModule (Spec (.of (Polynomial A))))
    (d n : ℕ) (P : Polynomial A) (j : Fin 2)
    (hs : sectionValue r L s E.hom ((Scheme.ΓSpecIso (.of (Polynomial A))).inv
      (sectionChartPolynomial d (P ^ n) j))) :
    sectionValue k ((Scheme.Modules.pullback q).obj L) (pullSection q L s)
      (fieldCoframe q k r h L E).hom
      ((Scheme.ΓSpecIso (.of (Polynomial (K ⊗[R] A)))).inv
        (sectionChartPolynomial d
          ((Polynomial.map (Algebra.TensorProduct.includeRight : A →ₐ[R] K ⊗[R] A).toRingHom P) ^ n)
              j)) := by
  exact polynomial_section_map q k r
    (Algebra.TensorProduct.includeRight : A →ₐ[R] K ⊗[R] A).toRingHom h
    ((Scheme.Modules.pullback q).obj L) L (Iso.refl _) E (pullSection q L s) s
    (pullSection_refl q L s) d n P j hs

/-- A polynomial cover of the prescribed scalar fibre with coframes and section
coordinates induced from the fixed arithmetic coframes in every degree. -/
def specializedPolynomialSectionData {R K : Type u} [CommRing R] [CommRing K]
    [Algebra R K] {X Y : Scheme.{u}} (baseK : Y ⟶ Spec (.of K)) (q : Y ⟶ X)
    (U : X.OpenCover.{u}) (A : U.I₀ → CommAlgCat.{u} R)
    (eU : ∀ i, U.X i ≅ Spec (.of (Polynomial (A i))))
    (L : ℕ → X.Modules) (s : ∀ n, unitModule X ⟶ L n)
    (F : ∀ n i, (Scheme.Modules.pullback (U.f i)).obj (L n) ≅ unitModule (U.X i))
    (P : ∀ i, Polynomial (A i)) (eps : U.I₀ → ULift.{u} (Fin 2)) : Prop :=
  ∃ (V : Y.OpenCover.{u}) (_hfinite : Finite V.I₀) (_haffine : ∀ v, IsAffine (V.X v))
    (index : V.I₀ ≃ U.I₀)
    (eV : ∀ v, V.X v ≅ Spec (.of (Polynomial (K ⊗[R] A (index v)))))
    (_hcart : ∀ v, IsPullback ((eV v).hom ≫ coefficientMap) (V.f v)
      (chartMap (eU (index v)) (U.f (index v))) q)
    (_hbase : ∀ v, V.f v ≫ baseK = (eV v).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap K (Polynomial (K ⊗[R] A (index v))))))
    (_hold : ∀ v, V.f v ≫ q = (eV v).hom ≫ coefficientMap ≫
      chartMap (eU (index v)) (U.f (index v)))
    (hspec : ∀ v, chartMap (eV v) (V.f v) ≫ q = coefficientMap ≫
      chartMap (eU (index v)) (U.f (index v)))
    (_hspecBase : ∀ v, chartMap (eV v) (V.f v) ≫ baseK =
      Spec.map (CommRingCat.ofHom (algebraMap K (Polynomial (K ⊗[R] A (index v)))))),
    let coordinate := fun n d => ∀ v, sectionValue (chartMap (eV v) (V.f v))
        ((Scheme.Modules.pullback q).obj (L n))
      (pullSection q (L n) (s n))
      (fieldCoframe q (chartMap (eV v) (V.f v)) (chartMap (eU (index v)) (U.f (index v)))
        (hspec v) (L n) (chartCoframe (eU (index v)) (U.f (index v)) (L n) (F n (index v)))).hom
      ((Scheme.ΓSpecIso (.of (Polynomial (K ⊗[R] A (index v))))).inv
        (sectionChartPolynomial d
          ((Polynomial.map (Algebra.TensorProduct.includeRight :
            A (index v) →ₐ[R] K ⊗[R] A (index v)).toRingHom (P (index v))) ^ n)
          (eps (index v)).down))
    (∀ n, coordinate n (2 * n)) ∧
      ∀ prime, Odd prime → coordinate ((prime - 1) / 2) (prime - 1)

private theorem odd_half_transport (coordinate : ℕ → ℕ → Prop)
    (h : ∀ n, coordinate n (2 * n)) (prime : ℕ) (hp : Odd prime) :
    coordinate ((prime - 1) / 2) (prime - 1) := by
  have hdegree := halfCharacter_degree prime hp
  exact Eq.mp (congrArg (coordinate ((prime - 1) / 2)) hdegree) (h ((prime - 1) / 2))

private theorem specialize_sections {R K : Type u} [CommRing R] [CommRing K]
    [Algebra R K] {X Y : Scheme.{u}} (base : X ⟶ Spec (.of R))
    (baseK : Y ⟶ Spec (.of K)) (q : Y ⟶ X)
    (hq : IsPullback q baseK base (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (U : X.OpenCover.{u}) [Finite U.I₀] (A : U.I₀ → CommAlgCat.{u} R)
    (eU : ∀ i, U.X i ≅ Spec (.of (Polynomial (A i))))
    (hU : ∀ i, U.f i ≫ base = (eU i).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (Polynomial (A i)))))
    (L : ℕ → X.Modules) (s : ∀ n, unitModule X ⟶ L n)
    (F : ∀ n i, (Scheme.Modules.pullback (U.f i)).obj (L n) ≅ unitModule (U.X i))
    (P : ∀ i, Polynomial (A i)) (eps : U.I₀ → ULift.{u} (Fin 2))
    (hsection : ∀ n i, sectionValue (U.f i) (L n) (s n) (F n i).hom
      ((eU i).hom.appTop ((Scheme.ΓSpecIso (.of (Polynomial (A i)))).inv
        (sectionChartPolynomial (2 * n) (P i ^ n) (eps i).down)))) :
    specializedPolynomialSectionData baseK q U A eU L s F P eps := by
  have hUbase : ∀ i, chartMap (eU i) (U.f i) ≫ base =
      Spec.map (CommRingCat.ofHom (algebraMap R (Polynomial (A i)))) := fun i =>
    iso_chart_projection (eU i) (U.f i) base _ (hU i)
  obtain ⟨V, hfinite, haffine, index, eV, hcart, hbase, hold⟩ :=
    exists_append_scalar_cover base baseK q hq U (fun i => A i) eU hUbase
  have hspec (v : V.I₀) : chartMap (eV v) (V.f v) ≫ q = coefficientMap ≫
      chartMap (eU (index v)) (U.f (index v)) :=
    iso_chart_projection (eV v) (V.f v) q _ (hold v)
  have hspecBase (v : V.I₀) : chartMap (eV v) (V.f v) ≫ baseK =
      Spec.map (CommRingCat.ofHom (algebraMap K (Polynomial (K ⊗[R] A (index v))))) :=
    iso_chart_projection (eV v) (V.f v) baseK _ (hbase v)
  refine ⟨V, hfinite, haffine, index, eV, hcart, hbase, hold, hspec, hspecBase, ?_⟩
  intro coordinate
  have hAll : ∀ n, coordinate n (2 * n) := by
    intro n v
    have hOld := chart_section (eU (index v)) (U.f (index v)) (L n) (s n)
      (F n (index v)) _ (hsection n (index v))
    exact field_section q (chartMap (eV v) (V.f v))
      (chartMap (eU (index v)) (U.f (index v))) (hspec v) (L n) (s n)
      (chartCoframe (eU (index v)) (U.f (index v)) (L n) (F n (index v)))
      (2 * n) n (P (index v)) (eps (index v)).down hOld
  exact ⟨hAll, fun prime hp => odd_half_transport coordinate hAll prime hp⟩


/-- The arithmetic whole coframe retains its fine restrictions, scalar
comparison, and section value from the original section family. -/
def arithmeticPolynomialFrameData {X XK Z : Scheme.{u}}
    (n : XK ⟶ X) (r : XK ⟶ Z) (L : X.Modules) (LK : Z.Modules)
    (EL : (Scheme.Modules.pullback n).obj L ≅ (Scheme.Modules.pullback r).obj LK)
    (W U : X.OpenCover.{u}) {I : Type u} (index : U.I₀ → I)
    (PK : I → Scheme.{u}) (g : ∀ i, PK i ⟶ XK) (c : ∀ i, PK i ⟶ Z)
    (hc : ∀ i, g i ≫ r = c i)
    (Epoly : ∀ i, (Scheme.Modules.pullback (c i)).obj LK ≅ unitModule (PK i))
    (z : ∀ i, PK (index i) ⟶ U.X i)
    (hwhole : ∀ i, z i ≫ U.f i = g (index i) ≫ n)
    (s : unitModule X ⟶ L) (value : ∀ i, Γ(U.X i, ⊤)) (i : U.I₀)
    (F : (Scheme.Modules.pullback (U.f i)).obj L ≅ unitModule (U.X i)) : Prop :=
  ∃ E : ∀ w, (Scheme.Modules.pullback ((appendCommonCover W U).f ⟨w, i⟩)).obj L ≅
      unitModule ((commonPolynomialCover W U i).X w),
    (∀ w, F.hom.over ((commonPolynomialCover W U i).f w).opensRange =
        (coframeOverRange ((commonPolynomialCover W U i).f w) _
          (polynomialFineCoframe W U i L E w)).hom ∧
      F.inv.over ((commonPolynomialCover W U i).f w).opensRange =
        (coframeOverRange ((commonPolynomialCover W U i).f w) _
          (polynomialFineCoframe W U i L E w)).inv) ∧
    (Scheme.Modules.pullback (z i)).mapIso F ≪≫ pullbackObjUnitIso (z i) =
      wholeComparison n (U.f i) (g (index i)) (z i) (hwhole i) L ≪≫
        comparedWholeFrame r (g (index i)) (c (index i)) (hc (index i))
          ((Scheme.Modules.pullback n).obj L) LK EL (Epoly (index i)) ∧
    sectionValue (U.f i) L s F.hom (value i)

/-- The fixed arithmetic section family constructs a polynomial cover of the
prescribed scalar fibre and its section coordinates in every degree.
All arithmetic coframe comparisons remain attached to the same witnesses. -/
theorem specializedWord_sections {R K : Type u} [CommRing R] [CommRing K]
    [Algebra R K] {X Y XK Z : Scheme.{u}}
    (base : X ⟶ Spec (.of R)) (baseK : Y ⟶ Spec (.of K)) (q : Y ⟶ X)
    (hq : IsPullback q baseK base (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (n : XK ⟶ X) (r : XK ⟶ Z)
    (L : ℕ → X.Modules) (LK : ℕ → Z.Modules)
    (EL : ∀ d, (Scheme.Modules.pullback n).obj (L d) ≅ (Scheme.Modules.pullback r).obj (LK d))
    (W U : X.OpenCover.{u}) [Finite U.I₀] {I : Type u} (index : U.I₀ → I)
    (PK : I → Scheme.{u}) (g : ∀ i, PK i ⟶ XK) (c : ∀ i, PK i ⟶ Z)
    (hc : ∀ i, g i ≫ r = c i)
    (Epoly : ∀ d i, (Scheme.Modules.pullback (c i)).obj (LK d) ≅ unitModule (PK i))
    (z : ∀ i, PK (index i) ⟶ U.X i)
    (hwhole : ∀ i, z i ≫ U.f i = g (index i) ≫ n)
    (A : U.I₀ → CommAlgCat.{u} R)
    (eU : ∀ i, U.X i ≅ Spec (.of (Polynomial (A i))))
    (hU : ∀ i, U.f i ≫ base = (eU i).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (Polynomial (A i)))))
    (s : ∀ d, unitModule X ⟶ L d)
    (P : ∀ i, Polynomial (A i)) (eps : U.I₀ → ULift.{u} (Fin 2))
    (hfamily : ∀ d, scalarPolynomialSectionFamily n r (L d) (LK d) (EL d)
      W U index PK g c hc (Epoly d) z hwhole (s d)
      (fun i => (eU i).hom.appTop ((Scheme.ΓSpecIso (.of (Polynomial (A i)))).inv
        (sectionChartPolynomial (2 * d) (P i ^ d) (eps i).down)))) :
    ∃ F : ∀ d i, (Scheme.Modules.pullback (U.f i)).obj (L d) ≅ unitModule (U.X i),
      (∀ d i, arithmeticPolynomialFrameData n r (L d) (LK d) (EL d) W U index PK g c hc
        (Epoly d) z hwhole (s d)
        (fun j => (eU j).hom.appTop ((Scheme.ΓSpecIso (.of (Polynomial (A j)))).inv
          (sectionChartPolynomial (2 * d) (P j ^ d) (eps j).down))) i (F d i)) ∧
      specializedPolynomialSectionData baseK q U A eU L s F P eps := by
  classical
  have hraw := fun d i => hfamily d i
  choose E F hres hscalar hcoord using hraw
  refine ⟨F, ?_, ?_⟩
  · intro d i
    exact ⟨E d i, hres d i, hscalar d i, hcoord d i⟩
  · exact specialize_sections base baseK q hq U A eU hU L s F P eps hcoord

end SchubertGeometry.RetainedCharacter
