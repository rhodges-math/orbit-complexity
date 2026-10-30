import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.MatchingPolynomialFamilies
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendArithmeticSections
import OrbitComplexity.FrobeniusSplitting.Normality.Assembly.SectionCoframeTransport
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Section coordinates on a fixed polynomial coframe family

The canonical determinant comparison determines the section in each whole
polynomial coframe. Injectivity of the scalar chart comparison reflects these
coordinates on the same coefficient model in every character degree.
-/

set_option autoImplicit false
noncomputable section
universe u v w

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Modules
open ReductiveGroups GroupActions FrobeniusSplitting
open FrobeniusSplitting.CharacterLine FrobeniusSplitting.RetainedCharacter
open FrobeniusSplitting.OperatorSheaf
open CartesianMonoidalCategory MonoidalCategory
open scoped TensorProduct CategoryTheory.MonObj

open private pullSection pullSection_comp pullSection_congr from
  OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.PullbackFrames
open private sectionValue pull_section_morphism pull_section_comp_hom section_chart_map from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendSectionCoordinates
open private unitValue unit_hom_eq_smul from
  OrbitComplexity.FrobeniusSplitting.Normality.Assembly.FrameReflection
open private pulled_section_coordinate scalar_hom_injective from
  OrbitComplexity.FrobeniusSplitting.Normality.Assembly.SectionCoframeTransport
open private wholeComparison comparedWholeFrame polynomialFineCoframe from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.CommonPolynomialCoframes
open private spec_scalar_image from
  OrbitComplexity.FrobeniusSplitting.Normality.Assembly.AdjustedCoframes
open private common_field_coordinates from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendMatchingCover
open private tensor_coordinate_factor from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.RetainedAppendAtlas
open private extendedCoefficient from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.ScalarPolynomialComparison
open private fieldMap oldMap from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.ScalarPolynomialCover
open private polynomialFamilyData modelPolynomialFamilyData from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.MatchingPolynomialFamilies
open private singletonIndex from OrbitComplexity.FrobeniusSplitting.Modules.MatchingModule
open private chartLift from
    OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.WordMatchingBase
open private framePolynomial from
    OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.AppendSections

namespace SchubertGeometry.RetainedCharacter

private abbrev unitModule (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

private theorem section_reflection {P PK : Scheme.{u}} (z : PK ⟶ P)
    (hinj : Function.Injective z.appTop.hom) (M : P.Modules)
    (s : unitModule P ⟶ M) (F : M ≅ unitModule P) (a : Γ(P, ⊤))
    (h : pullSection z M s ≫
      ((Scheme.Modules.pullback z).mapIso F ≪≫ pullbackObjUnitIso z).hom =
        globalSectionsSmul (unitModule PK) (z.appTop a)) :
    s ≫ F.hom = globalSectionsSmul (unitModule P) a := by
  let b := unitValue (s ≫ F.hom)
  have hb : s ≫ F.hom = globalSectionsSmul (unitModule P) b := unit_hom_eq_smul _
  have hc := pulled_section_coordinate z s F b hb
  have he : z.appTop b = z.appTop a := scalar_hom_injective (hc.symm.trans h)
  exact hb.trans (congrArg (globalSectionsSmul (unitModule P)) (hinj he))

private theorem whole_section {Y YK P PK : Scheme.{u}}
    (q : YK ⟶ Y) (f : P ⟶ Y) (g : PK ⟶ YK) (z : PK ⟶ P)
    (h : z ≫ f = g ≫ q) (L : Y.Modules) (s : unitModule Y ⟶ L) :
    pullSection z ((Scheme.Modules.pullback f).obj L) (pullSection f L s) ≫
        (wholeComparison q f g z h L).hom =
      pullSection g ((Scheme.Modules.pullback q).obj L) (pullSection q L s) := by
  change pullSection z ((Scheme.Modules.pullback f).obj L) (pullSection f L s) ≫
      (pullbackComp z f).hom.app L ≫ (pullbackCongr h).hom.app L ≫
        (pullbackComp g q).inv.app L = _
  have h0 := pull_section_comp_hom z f L s
  have h1 := pullSection_congr h L s
  have h2 := pullSection_comp g q L s
  calc
    _ = (pullSection (z ≫ f) L s ≫ (pullbackCongr h).hom.app L) ≫
        (pullbackComp g q).inv.app L :=
      congrArg (fun k => (k ≫ (pullbackCongr h).hom.app L) ≫
        (pullbackComp g q).inv.app L) h0
    _ = pullSection (g ≫ q) L s ≫ (pullbackComp g q).inv.app L :=
      congrArg (fun k => k ≫ (pullbackComp g q).inv.app L) h1
    _ = _ := h2

private theorem compared_section {YK PK Z : Scheme.{u}}
    (r : YK ⟶ Z) (g : PK ⟶ YK) (c : PK ⟶ Z) (h : g ≫ r = c)
    (M : YK.Modules) (LK : Z.Modules)
    (EL : M ≅ (Scheme.Modules.pullback r).obj LK)
    (E : (Scheme.Modules.pullback c).obj LK ≅ unitModule PK)
    (s : unitModule YK ⟶ M) (t : unitModule Z ⟶ LK)
    (hs : s ≫ EL.hom = pullSection r LK t) (a : Γ(PK, ⊤))
    (ht : sectionValue c LK t E.hom a) :
    pullSection g M s ≫ (comparedWholeFrame r g c h M LK EL E).hom =
      globalSectionsSmul (unitModule PK) a := by
  have hs' := (pull_section_morphism g M ((Scheme.Modules.pullback r).obj LK) s EL.hom).trans
    (congrArg (pullSection g ((Scheme.Modules.pullback r).obj LK)) hs)
  change pullSection g M s ≫ (Scheme.Modules.pullback g).map EL.hom ≫
      (pullbackComp g r).hom.app LK ≫ (pullbackCongr h).hom.app LK ≫ E.hom = _
  have h0 := pull_section_comp_hom g r LK t
  have h1 := pullSection_congr h LK t
  calc
    _ = (((pullSection g M s ≫ (Scheme.Modules.pullback g).map EL.hom) ≫
        (pullbackComp g r).hom.app LK) ≫ (pullbackCongr h).hom.app LK) ≫ E.hom := by
      simp only [Category.assoc]
    _ = ((pullSection g ((Scheme.Modules.pullback r).obj LK) (pullSection r LK t) ≫
        (pullbackComp g r).hom.app LK) ≫ (pullbackCongr h).hom.app LK) ≫ E.hom :=
      congrArg (fun k => ((k ≫ (pullbackComp g r).hom.app LK) ≫
        (pullbackCongr h).hom.app LK) ≫ E.hom) hs'
    _ = (pullSection (g ≫ r) LK t ≫ (pullbackCongr h).hom.app LK) ≫ E.hom :=
      congrArg (fun k => (k ≫ (pullbackCongr h).hom.app LK) ≫ E.hom) h0
    _ = pullSection c LK t ≫ E.hom := congrArg (fun k => k ≫ E.hom) h1
    _ = _ := ht

private theorem canonical_section_input {Y YK Z : Scheme.{u}}
    (m : YK ⟶ Y) (r : YK ⟶ Z) (L : Y.Modules) (LK : Z.Modules)
    (EL : (Scheme.Modules.pullback m).obj L ≅ (Scheme.Modules.pullback r).obj LK)
    (s : unitModule Y ⟶ L) (t : unitModule Z ⟶ LK)
    (hs : (pullbackObjUnitIso m).inv ≫ (Scheme.Modules.pullback m).map s ≫ EL.hom =
      (pullbackObjUnitIso r).inv ≫ (Scheme.Modules.pullback r).map t) :
    pullSection m L s ≫ EL.hom = pullSection r LK t := by
  change ((pullbackObjUnitIso m).inv ≫ (Scheme.Modules.pullback m).map s) ≫ EL.hom = _
  exact (Category.assoc (pullbackObjUnitIso m).inv
    ((Scheme.Modules.pullback m).map s) EL.hom).trans hs

private theorem scalar_section_comparison {Y YT YK Z : Scheme.{u}}
    (q : YT ⟶ Y) (n : YK ⟶ YT) (m : YK ⟶ Y) (h : n ≫ q = m)
    (r : YK ⟶ Z) (L : Y.Modules) (LK : Z.Modules)
    (EL : (Scheme.Modules.pullback m).obj L ≅ (Scheme.Modules.pullback r).obj LK)
    (s : unitModule Y ⟶ L) (t : unitModule Z ⟶ LK)
    (hs : (pullbackObjUnitIso m).inv ≫ (Scheme.Modules.pullback m).map s ≫ EL.hom =
      (pullbackObjUnitIso r).inv ≫ (Scheme.Modules.pullback r).map t) :
    pullSection n ((Scheme.Modules.pullback q).obj L) (pullSection q L s) ≫
      (((pullbackComp n q).app L ≪≫ (pullbackCongr h).app L) ≪≫ EL).hom =
        pullSection r LK t := by
  change pullSection n ((Scheme.Modules.pullback q).obj L) (pullSection q L s) ≫
    (pullbackComp n q).hom.app L ≫ (pullbackCongr h).hom.app L ≫ EL.hom = _
  have hsection := canonical_section_input m r L LK EL s t hs
  have h0 := pull_section_comp_hom n q L s
  have h1 := pullSection_congr h L s
  calc
    _ = (pullSection (n ≫ q) L s ≫ (pullbackCongr h).hom.app L) ≫ EL.hom :=
      congrArg (fun k => (k ≫ (pullbackCongr h).hom.app L) ≫ EL.hom) h0
    _ = pullSection m L s ≫ EL.hom := congrArg (fun k => k ≫ EL.hom) h1
    _ = _ := hsection

private theorem chart_section_reflection {Y YK P PK Z : Scheme.{u}}
    (q : YK ⟶ Y) (f : P ⟶ Y) (g : PK ⟶ YK) (z : PK ⟶ P)
    (h : z ≫ f = g ≫ q) (hinj : Function.Injective z.appTop.hom)
    (r : YK ⟶ Z) (c : PK ⟶ Z) (hc : g ≫ r = c)
    (L : Y.Modules) (LK : Z.Modules)
    (EL : (Scheme.Modules.pullback q).obj L ≅ (Scheme.Modules.pullback r).obj LK)
    (s : unitModule Y ⟶ L) (t : unitModule Z ⟶ LK)
    (hs : pullSection q L s ≫ EL.hom = pullSection r LK t)
    (E : (Scheme.Modules.pullback c).obj LK ≅ unitModule PK)
    (F : (Scheme.Modules.pullback f).obj L ≅ unitModule P)
    (hF : (Scheme.Modules.pullback z).mapIso F ≪≫ pullbackObjUnitIso z =
      wholeComparison q f g z h L ≪≫
        comparedWholeFrame r g c hc ((Scheme.Modules.pullback q).obj L) LK EL E)
    (a : Γ(P, ⊤)) (b : Γ(PK, ⊤)) (hab : z.appTop a = b)
    (ht : sectionValue c LK t E.hom b) : sectionValue f L s F.hom a := by
  apply section_reflection z hinj ((Scheme.Modules.pullback f).obj L) (pullSection f L s) F a
  rw [hF, Iso.trans_hom, ← Category.assoc, whole_section]
  exact (compared_section r g c hc ((Scheme.Modules.pullback q).obj L) LK EL E
    (pullSection q L s) t hs b ht).trans
      (congrArg (globalSectionsSmul (unitModule PK)) hab.symm)

private theorem chart_coordinate_map {A B : Type u} [CommRing A] [CommRing B]
    (phi : A →+* B) {P : Scheme.{u}} (e : P ≅ Spec (.of A))
    (z : Spec (.of B) ⟶ P) (hz : z ≫ e.hom = Spec.map (CommRingCat.ofHom phi)) (a : A) :
    z.appTop (e.hom.appTop ((Scheme.ΓSpecIso (.of A)).inv a)) =
      (Scheme.ΓSpecIso (.of B)).inv (phi a) := by
  have he := congrArg (fun f : Spec (.of B) ⟶ Spec (.of A) =>
    f.appTop ((Scheme.ΓSpecIso (.of A)).inv a)) hz
  exact he.trans (spec_scalar_image phi a)

private theorem scalar_polynomial_coordinate {S T K A B : Type u}
    [CommRing S] [CommRing T] [CommRing K] [CommRing A] [CommRing B]
    [Algebra S T] [Algebra S K] [Algebra T K] [IsScalarTower S T K]
    [Algebra S A] [Algebra K B] (e : K ⊗[S] A ≃ₐ[K] B)
    (P : Polynomial A) (Q : Polynomial B)
    (hP : Polynomial.map (e.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom) P = Q)
    (d : ℕ) (j : Fin 2) :
    Polynomial.map (extendedCoefficient (T := T) e)
      (sectionChartPolynomial (2 * d)
        ((Polynomial.map (Algebra.TensorProduct.includeRight : A →ₐ[S] T ⊗[S] A).toRingHom P) ^ d)
            j) =
      sectionChartPolynomial (2 * d) (Q ^ d) j := by
  rw [section_chart_map, Polynomial.map_pow, Polynomial.map_map, tensor_coordinate_factor, hP]


/-- Whole polynomial coframes together with coordinates of one section. -/
def scalarPolynomialSectionFamily {Y YK Z : Scheme.{u}}
    (n : YK ⟶ Y) (r : YK ⟶ Z) (L : Y.Modules) (LK : Z.Modules)
    (EL : (Scheme.Modules.pullback n).obj L ≅ (Scheme.Modules.pullback r).obj LK)
    (W V : Y.OpenCover.{u}) {I : Type u} (index : V.I₀ → I)
    (P : I → Scheme.{u}) (g : ∀ i, P i ⟶ YK) (c : ∀ i, P i ⟶ Z)
    (hc : ∀ i, g i ≫ r = c i)
    (Epoly : ∀ i, (Scheme.Modules.pullback (c i)).obj LK ≅ unitModule (P i))
    (z : ∀ v, P (index v) ⟶ V.X v)
    (hwhole : ∀ v, z v ≫ V.f v = g (index v) ≫ n)
    (s : unitModule Y ⟶ L) (value : ∀ v, Γ(V.X v, ⊤)) : Prop :=
  ∀ v, ∃ (E : ∀ w, (Scheme.Modules.pullback ((appendCommonCover W V).f ⟨w, v⟩)).obj L ≅
      unitModule ((commonPolynomialCover W V v).X w))
      (F : (Scheme.Modules.pullback (V.f v)).obj L ≅ unitModule (V.X v)),
    (∀ w, F.hom.over ((commonPolynomialCover W V v).f w).opensRange =
        (coframeOverRange ((commonPolynomialCover W V v).f w) _
          (polynomialFineCoframe W V v L E w)).hom ∧
      F.inv.over ((commonPolynomialCover W V v).f w).opensRange =
        (coframeOverRange ((commonPolynomialCover W V v).f w) _
          (polynomialFineCoframe W V v L E w)).inv) ∧
    (Scheme.Modules.pullback (z v)).mapIso F ≪≫ pullbackObjUnitIso (z v) =
      wholeComparison n (V.f v) (g (index v)) (z v) (hwhole v) L ≪≫
        comparedWholeFrame r (g (index v)) (c (index v)) (hc (index v))
          ((Scheme.Modules.pullback n).obj L) LK EL (Epoly (index v)) ∧
    sectionValue (V.f v) L s F.hom (value v)

private theorem scalar_family_sections {Y YK Z : Scheme.{u}}
    (n : YK ⟶ Y) (r : YK ⟶ Z) (L : Y.Modules) (LK : Z.Modules)
    (EL : (Scheme.Modules.pullback n).obj L ≅ (Scheme.Modules.pullback r).obj LK)
    (W V : Y.OpenCover.{u}) {I : Type u} (index : V.I₀ → I)
    (P : I → Scheme.{u}) (g : ∀ i, P i ⟶ YK) (c : ∀ i, P i ⟶ Z)
    (hc : ∀ i, g i ≫ r = c i)
    (Epoly : ∀ i, (Scheme.Modules.pullback (c i)).obj LK ≅ unitModule (P i))
    (z : ∀ v, P (index v) ⟶ V.X v)
    (hwhole : ∀ v, z v ≫ V.f v = g (index v) ≫ n)
    (s : unitModule Y ⟶ L) (t : unitModule Z ⟶ LK)
    (hs : pullSection n L s ≫ EL.hom = pullSection r LK t)
    (value : ∀ v, Γ(V.X v, ⊤)) (fieldValue : ∀ i, Γ(P i, ⊤))
    (hinj : ∀ v, Function.Injective (z v).appTop.hom)
    (hvalue : ∀ v, (z v).appTop (value v) = fieldValue (index v))
    (ht : ∀ i, sectionValue (c i) LK t (Epoly i).hom (fieldValue i))
    (hfamily : scalarPolynomialCoframeFamily n r L LK EL W V index P g c hc Epoly z hwhole) :
    scalarPolynomialSectionFamily n r L LK EL W V index P g c hc Epoly z hwhole s value := by
  intro v
  obtain ⟨E, F, hres, hF⟩ := hfamily v
  exact ⟨E, F, hres, hF, chart_section_reflection n (V.f v) (g (index v)) (z v)
    (hwhole v) (hinj v) r (c (index v)) (hc (index v)) L LK EL s t hs
      (Epoly (index v)) F hF (value v) (fieldValue (index v)) (hvalue v) (ht (index v))⟩

private theorem scalar_chart_injective {R K : Type u} [CommRing R] [CommRing K]
    [Algebra R K] (hR : Function.Injective (algebraMap R K))
    {Y YK P : Scheme.{u}} (base : Y ⟶ Spec (.of R)) [Smooth base]
    (baseK : YK ⟶ Spec (.of K)) (n : YK ⟶ Y)
    (hn : IsPullback n baseK base (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (V : Y.OpenCover.{u}) [∀ v, IsAffine (V.X v)] (v : V.I₀)
    (g : P ⟶ YK) (z : P ⟶ V.X v) (h : IsPullback z g (V.f v) n) :
    Function.Injective z.appTop.hom := by
  let : IsOpenImmersion (V.f v) := V.map_prop v
  let : Smooth (V.f v ≫ base) := inferInstance
  have hfield := h.paste_vert hn
  exact (common_field_coordinates hR (V.f v ≫ base) (g ≫ baseK) z hfield).2.1

section Matching
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K) {J : Type u}
    (F : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} K)
    [hFopen : ∀ {s t} (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (F.map f).hom.toRingHom))]
    [hFdir : ((F.op ⋙ algSpec (.of K) ⋙ Over.forget (Spec (.of K))) ⋙
      Scheme.forget).IsLocallyDirected]
    (cF : Cocone (F.op ⋙ algSpec (.of K))) (hcF : IsColimit cF)
    (word : List G.rootBase.support) (i : G.rootBase.support)
    (q : cF.pt.left ⟶ bsdhScheme G (word ++ [i]))
    (point : J → G.points)
    (a : ∀ j, (algSpec (.of K)).obj (op (F.obj (singletonIndex j))) ⟶
      (oppositeUnipotentVariety G).toOver)
    (ha : ∀ j, (a j).left ≫ (flagChartMorphism G (point j)).left =
      (cF.ι.app (op (singletonIndex j))).left ≫ (q ≫ bsdhMap G (word ++ [i])))
    (beta : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val)
      (k : J) (_ : k ∈ s.val),
      (algSpec (.of K)).obj (op (F.obj s)) ⟶ (borelVariety G).toOver)
    (hgroup : ∀ s j hj k hk, chartLift G F point a s j hj =
      chartLift G F point a s k hk * (beta s j hj k hk ≫ borelInclusion G))
    (hco : ∀ s j hj k hk l hl, wordTransitionUnit G F beta s j hj l hl =
      wordTransitionUnit G F beta s k hk l hl * wordTransitionUnit G F beta s j hj k hk)
    (hn : ∀ s t (f : s ⟶ t) j hj k hk,
      Units.map (F.map f).hom.toMonoidHom (wordTransitionUnit G F beta s j hj k hk) =
        wordTransitionUnit G F beta t j ((leOfHom f) hj) k ((leOfHom f) hk))
    {R : Type u} [CommRing R]
    (N : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} R)
    [hNopen : ∀ {s t} (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (N.map f).hom.toRingHom))]
    [hNdir : ((N.op ⋙ algSpec (.of R) ⋙ Over.forget (Spec (.of R))) ⋙
      Scheme.forget).IsLocallyDirected]
    (v : N ⋙ forget₂ (CommAlgCat R) CommRingCat ⟶
      F ⋙ forget₂ (CommAlgCat K) CommRingCat)
    (deltaN : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val)
      (k : J) (_ : k ∈ s.val), (N.obj s)ˣ)
    (hd : ∀ s j hj k hk, (v.app s).hom (deltaN s j hj k hk : N.obj s) =
      (wordTransitionUnit G F beta s j hj k hk : F.obj s))
    (cN : Cocone (N.op ⋙ algSpec (.of R))) (hcN : IsColimit cN)
    (qN : cF.pt.left ⟶ cN.pt.left)
    (hqN : ∀ s, Spec.map (v.app s) ≫ (cN.ι.app (op s)).left =
      (cF.ι.app (op s)).left ≫ qN)
    (hcoN : ∀ s j hj k hk l hl,
      deltaN s j hj l hl = deltaN s k hk l hl * deltaN s j hj k hk)
    (hnN : ∀ s t (f : s ⟶ t) j hj k hk,
      Units.map (N.map f).hom.toMonoidHom (deltaN s j hj k hk) =
        deltaN t j ((leOfHom f) hj) k ((leOfHom f) hk))


variable (hv : ∀ s, Function.Injective (v.app s).hom)
    (PN : ∀ s : {s : Finset J // s.Nonempty}, Polynomial (N.obj s))
    (hPN : ∀ j, (v.app (singletonIndex j)).hom ((PN (singletonIndex j)).coeff 2) =
      wordRingCoefficient G F point a j)
    {T : Type u} [CommRing T] [Algebra R T] [Algebra T K] [Algebra R K]
    [IsScalarTower R T K] (hT : Function.Injective (algebraMap T K))
    {YT : Scheme.{u}} (baseT : YT ⟶ Spec (.of T)) [Smooth baseT]
    (qT : YT ⟶ cN.pt.left) (n : cF.pt.left ⟶ YT) (hbase : n ≫ qT = qN)
    (hnative : IsPullback n cF.pt.hom baseT
      (Spec.map (CommRingCat.ofHom (algebraMap T K))))
    (W VT : YT.OpenCover.{u}) [∀ z, IsAffine (VT.X z)]
    {I : Type u} (index : VT.I₀ → I)
    (V0 : I → Over (Spec (.of K))) (g : I → G.points)
    (b : ∀ z, V0 z ⟶ (oppositeUnipotentVariety G).toOver)
    (c : ∀ z, V0 z ⊗ (schubertVariety G
      (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver ⟶
        Over.mk (bsdhToSpec G (word ++ [i])))
    (hend : ∀ z, (c z).left ≫ (bsdhAppendIso G word i).hom.left ≫
      pullback.snd (bsdhMap G word) (flagBundleProjection G
        (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val))) =
      (b z ⊗ₘ 𝟙 (schubertVariety G
        (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver).left ≫ flagBundleChart G _ (g z))
    (A : I → CommAlgCat.{u} R) (B : I → CommAlgCat.{u} K)
    (p : ∀ z, (algSpec (.of K)).obj (op (B z)) ⟶ V0 z)
    (eps : I → ULift.{u} (Fin 2))
    (e0 : ∀ z, K ⊗[R] A z ≃ₐ[K] B z)
    (eVT : ∀ z, VT.X z ≅ Spec (.of (Polynomial (T ⊗[R] A (index z)))))
    (jK : ∀ z, Spec (.of (Polynomial (B z))) ⟶ cF.pt.left)
    (hword : ∀ z, jK z ≫ q = projectiveLinePolynomialChart (B z) (eps z) ≫
      projectiveAppendChart G i (B z) (p z) (c z))
    (hactual : ∀ z, IsPullback (fieldMap (e0 (index z)) ≫ (eVT z).inv)
      (jK (index z)) (VT.f z) n)
    (P : ∀ z, Polynomial (A z))
    (hP : ∀ z, Polynomial.map
      ((e0 z).toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom) (P z) =
        framePolynomial G i (B z) (p z ≫ b z) (g z))


private theorem append_field_section (d : ℕ) (l : I) (eps0 : ULift.{u} (Fin 2)) :
    sectionValue
      (projectiveLinePolynomialChart (B l) eps0 ≫ projectiveAppendChart G i (B l) (p l) (c l))
      (CharacterLine.wordCharacterModule G (G.positiveRootCharacter ^ d) (word ++ [i]))
      (CharacterLine.wordDeterminantModuleSection G d (word ++ [i]))
      (appendPolynomialFrame G word i (V0 l) (g l) (b l) (c l) (hend l) (B l) (p l) d eps0).hom
      ((Scheme.ΓSpecIso (.of (Polynomial (B l)))).inv
        (sectionChartPolynomial (2 * d)
          (framePolynomial G i (B l) (p l ≫ b l) (g l) ^ d) eps0.down)) := by
  rcases eps0 with ⟨j⟩
  exact appendPolynomialFrame_section G word i (V0 l) (g l) (b l) (c l)
    (hend l) (B l) (p l) d j

include hT hnative hactual hP hv hPN in
/-- The fixed whole polynomial coframes carry the canonical section in every
character degree, on the same scalar model and the same polynomial cover. -/
theorem matchingFamily_sections :
    let L := fun d => matchingModule N cN deltaN d
    let LK := fun d => CharacterLine.wordCharacterModule G
      (G.positiveRootCharacter ^ d) (word ++ [i])
    let EL := fun d => retainedWordLineIso G F cF hcF (word ++ [i]) q point a ha beta
      hgroup hco hn N v deltaN hd cN hcN qN hqN hcoN hnN d
    let s := fun d => retainedWordSection G F cF hcF (word ++ [i]) q point a ha beta
      hgroup hco hn N v hv deltaN hd PN hPN cN d
    let polyLeg := fun z => projectiveLinePolynomialChart (B z) (eps z) ≫
      projectiveAppendChart G i (B z) (p z) (c z)
    let Epoly := fun d z => appendPolynomialFrame G word i (V0 z) (g z) (b z) (c z)
      (hend z) (B z) (p z) d (eps z)
    let z := fun l => fieldMap (e0 (index l)) ≫ (eVT l).inv
    let hwhole := fun l => (hactual l).w
    let value := fun d l => (eVT l).hom.appTop
      ((Scheme.ΓSpecIso (.of (Polynomial (T ⊗[R] A (index l))))).inv
        (sectionChartPolynomial (2 * d)
          ((Polynomial.map (Algebra.TensorProduct.includeRight :
            A (index l) →ₐ[R] T ⊗[R] A (index l)).toRingHom (P (index l))) ^ d)
          (eps (index l)).down))
    (∀ d, scalarPolynomialCoframeFamily n q ((Scheme.Modules.pullback qT).obj (L d)) (LK d)
      (((pullbackComp n qT).app (L d) ≪≫ (pullbackCongr hbase).app (L d)) ≪≫ EL d)
      W VT index (fun l => Spec (.of (Polynomial (B l)))) jK polyLeg hword (Epoly d) z hwhole) →
    ∀ d, scalarPolynomialSectionFamily n q ((Scheme.Modules.pullback qT).obj (L d)) (LK d)
      (((pullbackComp n qT).app (L d) ≪≫ (pullbackCongr hbase).app (L d)) ≪≫ EL d)
      W VT index (fun l => Spec (.of (Polynomial (B l)))) jK polyLeg hword (Epoly d) z hwhole
      (pullSection qT (L d) (s d)) (value d) := by
  intro L LK EL s polyLeg Epoly z hwhole value hfamily d
  let t := fun e => CharacterLine.wordDeterminantModuleSection G e (word ++ [i])
  have hcanonical := retainedWordLineIso_section G F cF hcF (word ++ [i]) q point a ha beta
    hgroup hco hn N v deltaN hd cN hcN qN hqN hcoN hnN hv PN hPN d
  have hsection := scalar_section_comparison qT n qN hbase q (L d) (LK d) (EL d)
    (s d) (t d) hcanonical
  have hinj : ∀ l, Function.Injective (z l).appTop.hom := fun l =>
    scalar_chart_injective hT baseT cF.pt.hom n hnative VT l
      (jK (index l)) (z l) (hactual l)
  have hfield : ∀ l, (z l).appTop (value d l) =
      (Scheme.ΓSpecIso (.of (Polynomial (B (index l))))).inv
        (sectionChartPolynomial (2 * d)
          (framePolynomial G i (B (index l)) (p (index l) ≫ b (index l)) (g (index l)) ^ d)
          (eps (index l)).down) := by
    intro l
    have hz : z l ≫ (eVT l).hom = fieldMap (e0 (index l)) := by
      simp only [z, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    have hcoord := chart_coordinate_map (Polynomial.mapRingHom (extendedCoefficient (T := T)
      (e0 (index l)))) (eVT l) (z l) hz
      (sectionChartPolynomial (2 * d)
        ((Polynomial.map (Algebra.TensorProduct.includeRight :
          A (index l) →ₐ[R] T ⊗[R] A (index l)).toRingHom (P (index l))) ^ d)
        (eps (index l)).down)
    exact hcoord.trans (congrArg (fun Q : Polynomial (B (index l)) =>
      (Scheme.ΓSpecIso (.of (Polynomial (B (index l))))).inv Q)
        (scalar_polynomial_coordinate (e0 (index l)) (P (index l)) _ (hP (index l))
          d (eps (index l)).down))
  have ht : ∀ l, sectionValue (polyLeg l) (LK d) (t d) (Epoly d l).hom
      ((Scheme.ΓSpecIso (.of (Polynomial (B l)))).inv
        (sectionChartPolynomial (2 * d)
          (framePolynomial G i (B l) (p l ≫ b l) (g l) ^ d) (eps l).down)) := by
    intro l
    exact append_field_section G word i V0 g b c hend B p d l (eps l)
  exact scalar_family_sections n q ((Scheme.Modules.pullback qT).obj (L d)) (LK d)
    (((pullbackComp n qT).app (L d) ≪≫ (pullbackCongr hbase).app (L d)) ≪≫ EL d)
    W VT index (fun l => Spec (.of (Polynomial (B l)))) jK polyLeg hword (Epoly d) z hwhole
    (pullSection qT (L d) (s d)) (t d) hsection (value d)
    (fun l => (Scheme.ΓSpecIso (.of (Polynomial (B l)))).inv
      (sectionChartPolynomial (2 * d)
        (framePolynomial G i (B l) (p l ≫ b l) (g l) ^ d) (eps l).down))
    hinj hfield ht (hfamily d)

/-- The homogeneous degree of the half-character section is the Frobenius degree. -/
theorem halfCharacter_degree (prime : ℕ) (hodd : Odd prime) :
    2 * ((prime - 1) / 2) = prime - 1 := by
  obtain ⟨k, hk⟩ := hodd
  omega

end Matching

end SchubertGeometry.RetainedCharacter
