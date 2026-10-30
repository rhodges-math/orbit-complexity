import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.RetainedLocalFrames
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.PolynomialChartSections
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordCoefficientDescent
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Append sections on both polynomial charts

The full character section is compared on the fixed polynomial chart at every
power. The second chart uses the homogeneous reverse in degree twice that
power. Pullback, the append degree comparison, and the matching comparison
transport the same global section before its affine coordinate is evaluated.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open ReductiveGroups GroupActions CartesianMonoidalCategory MonoidalCategory
open FrobeniusSplitting.CharacterLine FrobeniusSplitting.RetainedCharacter
open scoped CategoryTheory.MonObj

noncomputable section
universe u v w

namespace SchubertGeometry.RetainedCharacter

open private pullSection pullSection_comp pullSection_congr pullSection_frame
  from OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.PullbackFrames
open private restrict_adjunct
  from OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.NativeFrame
open private section_by_adjunct matching_section_coordinate singleton_selected_frame
  affine_smul_power
  from OrbitComplexity.SchubertGeometry.Frobenius.Assembly.RetainedLocalFrames
open private chart_adjunction_projection transpose_counit
  from OrbitComplexity.SchubertGeometry.LineBundles.Modules.GlobalCoordinates
open private chartSection
  from OrbitComplexity.SchubertGeometry.LineBundles.Affine.GlobalAffineEndpoint
open private polynomial_projection
  from OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordCompatibleSplitting
open private framePolynomial framePower_degree
  from OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.AppendSections
open private comparisonCoframe
  from OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendCoframeComparison
open private singletonIndex singletonArrow
  from OrbitComplexity.FrobeniusSplitting.Modules.MatchingModule
open private chartLift
  from OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.WordMatchingBase
open private wordMatchingSection_from_coefficients
  from OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordCoefficientDescent
open private unit_scalar_top
  from OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendPowerFrames

private theorem iso_section_inverse {C : Type v} [Category.{w} C]
    {O M N : C} (E : M ≅ N) (s : O ⟶ M) (t : O ⟶ N)
    (h : t ≫ E.inv = s) : s ≫ E.hom = t := by
  rw [← h, Category.assoc, E.inv_hom_id, Category.comp_id]

private theorem pull_section_morphism {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M N : Y.Modules) (s : SheafOfModules.unit Y.ringCatSheaf ⟶ M) (t : M ⟶ N) :
    pullSection f M s ≫ (Scheme.Modules.pullback f).map t =
      pullSection f N (s ≫ t) := by
  change (Scheme.Modules.pullbackObjUnitIso f).inv ≫
      (Scheme.Modules.pullback f).map s ≫ (Scheme.Modules.pullback f).map t =
    (Scheme.Modules.pullbackObjUnitIso f).inv ≫ (Scheme.Modules.pullback f).map (s ≫ t)
  exact congrArg (fun a => (Scheme.Modules.pullbackObjUnitIso f).inv ≫ a)
    ((Scheme.Modules.pullback f).map_comp s t).symm

private theorem pull_section_comp_hom {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (M : Z.Modules)
    (s : SheafOfModules.unit Z.ringCatSheaf ⟶ M) :
    pullSection f ((Scheme.Modules.pullback g).obj M) (pullSection g M s) ≫
        (Scheme.Modules.pullbackComp f g).hom.app M = pullSection (f ≫ g) M s := by
  rw [← pullSection_comp f g M s, Category.assoc, Iso.inv_hom_id_app,
    Category.comp_id]


private def sectionValue {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules)
    (s : SheafOfModules.unit Y.ringCatSheaf ⟶ M)
    (e : (Scheme.Modules.pullback f).obj M ⟶ SheafOfModules.unit X.ringCatSheaf)
    (z : Γ(X, ⊤)) : Prop :=
  pullSection f M s ≫ e =
    Scheme.Modules.globalSectionsSmul (SheafOfModules.unit X.ringCatSheaf) z

private def localSectionValue {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    (M : Y.Modules) (s : SheafOfModules.unit Y.ringCatSheaf ⟶ M)
    (e : (Scheme.Modules.restrictFunctor j).obj M ⟶
      SheafOfModules.unit X.ringCatSheaf) (z : Γ(X, ⊤)) : Prop :=
  sectionValue j M s
    ((Scheme.Modules.restrictFunctorIsoPullback j).inv.app M ≫ e) z


private theorem standard_local_section {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j] (M : Y.Modules)
    (s : SheafOfModules.unit Y.ringCatSheaf ⟶ M)
    (e : (Scheme.Modules.restrictFunctor j).obj M ⟶
      SheafOfModules.unit X.ringCatSheaf)
    (c : M ⟶ (Scheme.Modules.pushforward j).obj (SheafOfModules.unit X.ringCatSheaf))
    (z : Γ(X, ⊤))
    (he : (Scheme.Modules.restrictAdjunction j).homEquiv M
      (SheafOfModules.unit X.ringCatSheaf) e = c)
    (hs : s ≫ c = SheafOfModules.unitToPushforwardObjUnit j.toRingCatSheafHom ≫
      (Scheme.Modules.pushforward j).map
        (Scheme.Modules.globalSectionsSmul (SheafOfModules.unit X.ringCatSheaf) z)) :
    localSectionValue j M s e z := by
  exact section_by_adjunct (Scheme.Modules.pullback j) (Scheme.Modules.pushforward j)
    (Scheme.Modules.pullbackPushforwardAdjunction j)
    (Scheme.Modules.pullbackObjUnitIso j) s
    ((Scheme.Modules.restrictFunctorIsoPullback j).inv.app M ≫ e) c
    (Scheme.Modules.globalSectionsSmul (SheafOfModules.unit X.ringCatSheaf) z)
    (SheafOfModules.unitToPushforwardObjUnit j.toRingCatSheafHom)
    ((restrict_adjunct j M (SheafOfModules.unit X.ringCatSheaf) e).trans he)
    (Scheme.Modules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitIso_hom j) hs

private theorem right_chart_adjunct (A : Type u) [CommRing A] (d : ℕ) :
    (Scheme.Modules.restrictAdjunction (projectiveLinePolynomialChart A ⟨1⟩)).homEquiv
        (ProjectiveLine.projectiveTransitionModule A d)
        (SheafOfModules.unit (Spec (.of (Polynomial A))).ringCatSheaf)
        (ProjectiveLine.projectiveTransitionChart A d ⟨1⟩).hom =
      pullback.snd (ProjectiveLine.leftRestriction A)
        (ProjectiveLine.twistedRestriction A d) := by
  let j := projectiveLinePolynomialChart A ⟨1⟩
  let M := ProjectiveLine.projectiveTransitionModule A d
  let U := SheafOfModules.unit (Spec (.of (Polynomial A))).ringCatSheaf
  let adj := Scheme.Modules.restrictAdjunction j
  let c : M ⟶ (Scheme.Modules.pushforward j).obj U :=
    pullback.snd (ProjectiveLine.leftRestriction A) (ProjectiveLine.twistedRestriction A d)
  have he : (ProjectiveLine.projectiveTransitionChart A d ⟨1⟩).hom =
      (Scheme.Modules.restrictFunctor j).map c ≫ adj.counit.app U := by
    ext V x
    rfl
  exact (congrArg (adj.homEquiv M U) he).trans (transpose_counit adj c)

/-- The chosen polynomial coordinate uses the first polynomial on the first
chart and its homogeneous reverse on the second chart. -/
def sectionChartPolynomial {A : Type u} [CommRing A] (d : ℕ)
    (P : Polynomial A) (j : Fin 2) : Polynomial A :=
  if j = 0 then P else ProjectiveLine.homogeneousReverse d P

private theorem section_chart_map {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (d : ℕ) (P : Polynomial A) (j : Fin 2) :
    Polynomial.map f (sectionChartPolynomial d P j) =
      sectionChartPolynomial d (Polynomial.map f P) j := by
  by_cases hj : j = 0
  · simp only [sectionChartPolynomial, ite_eq_left hj]
  · simpa only [sectionChartPolynomial, ite_eq_right hj] using
      ProjectiveLine.homogeneousReverse_map f d P


private theorem standard_section_value {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j] (M : Y.Modules)
    (s : SheafOfModules.unit Y.ringCatSheaf ⟶ M)
    (e : (Scheme.Modules.restrictFunctor j).obj M ⟶
      SheafOfModules.unit X.ringCatSheaf)
    (c : M ⟶ (Scheme.Modules.pushforward j).obj (SheafOfModules.unit X.ringCatSheaf))
    (z : Γ(X, ⊤))
    (he : (Scheme.Modules.restrictAdjunction j).homEquiv M
      (SheafOfModules.unit X.ringCatSheaf) e = c)
    (hs : s ≫ c = SheafOfModules.unitToPushforwardObjUnit j.toRingCatSheafHom ≫
      (Scheme.Modules.pushforward j).map
        (Scheme.Modules.globalSectionsSmul (SheafOfModules.unit X.ringCatSheaf) z)) :
    sectionValue j M s
      (((Scheme.Modules.restrictFunctorIsoPullback j).symm.app M).hom ≫ e) z := by
  exact standard_local_section j M s e c z he hs

private theorem section_value_fin2 {X Y : Scheme.{u}} (f : Fin 2 → (X ⟶ Y))
    (M : Y.Modules) (s : SheafOfModules.unit Y.ringCatSheaf ⟶ M)
    (e : ∀ j, (Scheme.Modules.pullback (f j)).obj M ⟶
      SheafOfModules.unit X.ringCatSheaf) (z : Fin 2 → Γ(X, ⊤))
    (h0 : sectionValue (f 0) M s (e 0) (z 0))
    (h1 : sectionValue (f 1) M s (e 1) (z 1)) (j : Fin 2) :
    sectionValue (f j) M s (e j) (z j) := by
  fin_cases j <;> assumption

private theorem polynomial_head_zero (A : Type u) [CommRing A] (d : ℕ)
    (P : Polynomial A) (hP : P.natDegree ≤ d) :
    sectionValue (projectiveLinePolynomialChart A ⟨0⟩)
      (ProjectiveLine.projectiveTransitionModule A d)
      (ProjectiveLine.projectivePolynomialSection A d P hP)
      (((Scheme.Modules.restrictFunctorIsoPullback (projectiveLinePolynomialChart A ⟨0⟩)).symm.app
        (ProjectiveLine.projectiveTransitionModule A d)).hom ≫
          (ProjectiveLine.projectiveTransitionChart A d ⟨0⟩).hom)
      ((Scheme.ΓSpecIso (.of (Polynomial A))).inv (sectionChartPolynomial d P 0)) := by
  have leaf := standard_section_value (projectiveLinePolynomialChart A ⟨0⟩)
    (ProjectiveLine.projectiveTransitionModule A d)
  exact leaf
    (ProjectiveLine.projectivePolynomialSection A d P hP)
    (ProjectiveLine.projectiveTransitionChart A d ⟨0⟩).hom
    (pullback.fst (ProjectiveLine.leftRestriction A) (ProjectiveLine.twistedRestriction A d))
    ((Scheme.ΓSpecIso (.of (Polynomial A))).inv (P))
    (chart_adjunction_projection A d) (polynomial_projection A d P hP)

private theorem polynomial_head_one (A : Type u) [CommRing A] (d : ℕ)
    (P : Polynomial A) (hP : P.natDegree ≤ d) :
    sectionValue (projectiveLinePolynomialChart A ⟨1⟩)
      (ProjectiveLine.projectiveTransitionModule A d)
      (ProjectiveLine.projectivePolynomialSection A d P hP)
      (((Scheme.Modules.restrictFunctorIsoPullback (projectiveLinePolynomialChart A ⟨1⟩)).symm.app
        (ProjectiveLine.projectiveTransitionModule A d)).hom ≫
          (ProjectiveLine.projectiveTransitionChart A d ⟨1⟩).hom)
      ((Scheme.ΓSpecIso (.of (Polynomial A))).inv (sectionChartPolynomial d P 1)) := by
  have leaf := standard_section_value (projectiveLinePolynomialChart A ⟨1⟩)
    (ProjectiveLine.projectiveTransitionModule A d)
  exact leaf
    (ProjectiveLine.projectivePolynomialSection A d P hP)
    (ProjectiveLine.projectiveTransitionChart A d ⟨1⟩).hom
    (pullback.snd (ProjectiveLine.leftRestriction A) (ProjectiveLine.twistedRestriction A d))
    ((Scheme.ΓSpecIso (.of (Polynomial A))).inv (ProjectiveLine.homogeneousReverse d P))
    (right_chart_adjunct A d) (ProjectiveLine.projectivePolynomialSection_right A d P hP)

private theorem polynomial_chart_section (A : Type u) [CommRing A] (d : ℕ)
    (P : Polynomial A) (hP : P.natDegree ≤ d) (j : Fin 2) :
    sectionValue (projectiveLinePolynomialChart A ⟨j⟩)
      (ProjectiveLine.projectiveTransitionModule A d)
      (ProjectiveLine.projectivePolynomialSection A d P hP)
      (((Scheme.Modules.restrictFunctorIsoPullback (projectiveLinePolynomialChart A ⟨j⟩)).symm.app
        (ProjectiveLine.projectiveTransitionModule A d)).hom ≫
          (ProjectiveLine.projectiveTransitionChart A d ⟨j⟩).hom)
      ((Scheme.ΓSpecIso (.of (Polynomial A))).inv (sectionChartPolynomial d P j)) := by
  exact section_value_fin2
    (fun j : Fin 2 => projectiveLinePolynomialChart A ⟨j⟩)
    (ProjectiveLine.projectiveTransitionModule A d)
    (ProjectiveLine.projectivePolynomialSection A d P hP)
    (fun j : Fin 2 =>
      ((Scheme.Modules.restrictFunctorIsoPullback (projectiveLinePolynomialChart A ⟨j⟩)).symm.app
        (ProjectiveLine.projectiveTransitionModule A d)).hom ≫
          (ProjectiveLine.projectiveTransitionChart A d ⟨j⟩).hom)
    (fun j : Fin 2 =>
      (Scheme.ΓSpecIso (.of (Polynomial A))).inv (sectionChartPolynomial d P j))
    (polynomial_head_zero A d P hP) (polynomial_head_one A d P hP) j

private theorem assoc_four {C : Type v} [Category.{w} C] {A B D E F : C}
    (a : A ⟶ B) (b : B ⟶ D) (c : D ⟶ E) (d : E ⟶ F) :
    a ≫ b ≫ c ≫ d = (a ≫ b ≫ c) ≫ d := by
  simp only [Category.assoc]

private theorem composite_section {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (N : Z.Modules) (M : Y.Modules)
    (s : SheafOfModules.unit Z.ringCatSheaf ⟶ N)
    (t : SheafOfModules.unit Y.ringCatSheaf ⟶ M)
    (E : (Scheme.Modules.pullback g).obj N ≅ M)
    (e : (Scheme.Modules.pullback f).obj M ⟶ SheafOfModules.unit X.ringCatSheaf)
    (hs : pullSection g N s ≫ E.hom = t) :
    pullSection (f ≫ g) N s ≫
        ((Scheme.Modules.pullbackComp f g).inv.app N ≫
          (Scheme.Modules.pullback f).map E.hom ≫ e) = pullSection f M t ≫ e := by
  calc
    _ = (pullSection f ((Scheme.Modules.pullback g).obj N) (pullSection g N s) ≫
        (Scheme.Modules.pullback f).map E.hom) ≫ e := by
      rw [← pullSection_comp f g N s]
      exact assoc_four _ _ _ _
    _ = pullSection f M (pullSection g N s ≫ E.hom) ≫ e :=
      congrArg (fun a => a ≫ e) (pull_section_morphism f _ _ _ E.hom)
    _ = _ := congrArg (fun a => pullSection f M a ≫ e) hs

private theorem composite_section_value {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (N : Z.Modules) (M : Y.Modules)
    (s : SheafOfModules.unit Z.ringCatSheaf ⟶ N)
    (t : SheafOfModules.unit Y.ringCatSheaf ⟶ M)
    (E : (Scheme.Modules.pullback g).obj N ≅ M)
    (e : (Scheme.Modules.pullback f).obj M ⟶ SheafOfModules.unit X.ringCatSheaf)
    (eF : (Scheme.Modules.pullback (f ≫ g)).obj N ⟶
      SheafOfModules.unit X.ringCatSheaf) (z : Γ(X, ⊤))
    (hF : eF = (Scheme.Modules.pullbackComp f g).inv.app N ≫
      (Scheme.Modules.pullback f).map E.hom ≫ e)
    (hs : pullSection g N s ≫ E.hom = t) (hv : sectionValue f M t e z) :
    sectionValue (f ≫ g) N s eF z := by
  change pullSection (f ≫ g) N s ≫ eF = _
  rw [hF]
  exact (composite_section f g N M s t E e hs).trans hv

private abbrev lineUnit (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

private def fourFrame {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (N : Z.Modules) (M : Y.Modules) (P : X.Modules)
    (E : (Scheme.Modules.pullback g).obj N ≅ M)
    (R : (Scheme.Modules.pullback f).obj M ≅ P) (T : P ≅ lineUnit X) :
    (Scheme.Modules.pullback (f ≫ g)).obj N ≅ lineUnit X :=
  ((Scheme.Modules.pullbackComp f g).app N).symm ≪≫
    (Scheme.Modules.pullback f).mapIso E ≪≫ R ≪≫ T

private def fourFrameEq {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (N : Z.Modules) (M : Y.Modules) (P : X.Modules)
    (E : (Scheme.Modules.pullback g).obj N ≅ M)
    (R : (Scheme.Modules.pullback f).obj M ≅ P) (T : P ≅ lineUnit X)
    (F : (Scheme.Modules.pullback (f ≫ g)).obj N ≅ lineUnit X) : Prop :=
  F = fourFrame f g N M P E R T

private theorem fourFrame_hom {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (N : Z.Modules) (M : Y.Modules) (P : X.Modules)
    (E : (Scheme.Modules.pullback g).obj N ≅ M)
    (R : (Scheme.Modules.pullback f).obj M ≅ P) (T : P ≅ lineUnit X)
    (F : (Scheme.Modules.pullback (f ≫ g)).obj N ≅ lineUnit X)
    (h : fourFrameEq f g N M P E R T F) :
    F.hom = (Scheme.Modules.pullbackComp f g).inv.app N ≫
      (Scheme.Modules.pullback f).map E.hom ≫ R.hom ≫ T.hom := by
  cases h
  rfl

private theorem fourFrame_section {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (N : Z.Modules) (M : Y.Modules) (P : X.Modules)
    (s : lineUnit Z ⟶ N) (t : lineUnit Y ⟶ M)
    (E : (Scheme.Modules.pullback g).obj N ≅ M)
    (R : (Scheme.Modules.pullback f).obj M ≅ P) (T : P ≅ lineUnit X)
    (F : (Scheme.Modules.pullback (f ≫ g)).obj N ≅ lineUnit X) (z : Γ(X, ⊤))
    (hF : fourFrameEq f g N M P E R T F)
    (hs : pullSection g N s ≫ E.hom = t)
    (hv : sectionValue f M t (R.hom ≫ T.hom) z) :
    sectionValue (f ≫ g) N s F.hom z := by
  exact composite_section_value f g N M s t E (R.hom ≫ T.hom) F.hom z
    (fourFrame_hom f g N M P E R T F hF) hs hv


private def comparisonFrameEq {P X Y Q : Scheme.{u}}
    (j : P ⟶ X) (q : X ⟶ Y) (k : P ⟶ Q) (r : Q ⟶ Y)
    (h : j ≫ q = k ≫ r) (M : X.Modules) (N : Y.Modules)
    (E : M ≅ (Scheme.Modules.pullback q).obj N)
    (e : (Scheme.Modules.pullback r).obj N ≅ SheafOfModules.unit Q.ringCatSheaf)
    (F : (Scheme.Modules.pullback j).obj M ≅ SheafOfModules.unit P.ringCatSheaf) : Prop :=
  F = comparisonCoframe j q k r h M N E e

private theorem comparison_section {P X Y Q : Scheme.{u}}
    (j : P ⟶ X) (q : X ⟶ Y) (k : P ⟶ Q) (r : Q ⟶ Y)
    (h : j ≫ q = k ≫ r) (M : X.Modules) (N : Y.Modules)
    (E : M ≅ (Scheme.Modules.pullback q).obj N)
    (e : (Scheme.Modules.pullback r).obj N ≅ SheafOfModules.unit Q.ringCatSheaf)
    (F : (Scheme.Modules.pullback j).obj M ≅ SheafOfModules.unit P.ringCatSheaf)
    (s : SheafOfModules.unit X.ringCatSheaf ⟶ M)
    (t : SheafOfModules.unit Y.ringCatSheaf ⟶ N) (z : Γ(Q, ⊤))
    (hF : comparisonFrameEq j q k r h M N E e F)
    (hs : s ≫ E.hom = pullSection q N t)
    (hr : sectionValue r N t e.hom z) :
    sectionValue j M s F.hom (k.appTop z) := by
  cases hF
  have h₀ := pull_section_morphism j M ((Scheme.Modules.pullback q).obj N) s E.hom
  have h₀s := h₀.trans (congrArg
    (pullSection j ((Scheme.Modules.pullback q).obj N)) hs)
  have h₁ := pull_section_comp_hom j q N t
  have h₂ := pullSection_congr h N t
  have h₃ := pullSection_comp k r N t
  have h₄ := pullSection_frame k ((Scheme.Modules.pullback r).obj N)
    (pullSection r N t) e z hr
  change pullSection j M s ≫ (Scheme.Modules.pullback j).map E.hom ≫
      (Scheme.Modules.pullbackComp j q).hom.app N ≫
      (Scheme.Modules.pullbackCongr h).hom.app N ≫
      (Scheme.Modules.pullbackComp k r).inv.app N ≫
      (Scheme.Modules.pullback k).map e.hom ≫
      (Scheme.Modules.pullbackObjUnitIso k).hom = _
  calc
    _ = (pullSection j ((Scheme.Modules.pullback q).obj N) (pullSection q N t) ≫
        (Scheme.Modules.pullbackComp j q).hom.app N) ≫
        (Scheme.Modules.pullbackCongr h).hom.app N ≫
        (Scheme.Modules.pullbackComp k r).inv.app N ≫
        (Scheme.Modules.pullback k).map e.hom ≫
        (Scheme.Modules.pullbackObjUnitIso k).hom := by
      simp only [← Category.assoc, h₀s]
    _ = (pullSection (j ≫ q) N t ≫ (Scheme.Modules.pullbackCongr h).hom.app N) ≫
        (Scheme.Modules.pullbackComp k r).inv.app N ≫
        (Scheme.Modules.pullback k).map e.hom ≫
        (Scheme.Modules.pullbackObjUnitIso k).hom := by rw [h₁, Category.assoc]
    _ = (pullSection (k ≫ r) N t ≫ (Scheme.Modules.pullbackComp k r).inv.app N) ≫
        (Scheme.Modules.pullback k).map e.hom ≫
        (Scheme.Modules.pullbackObjUnitIso k).hom := by rw [h₂, Category.assoc]
    _ = _ := by
      rw [h₃]
      exact h₄

private theorem section_frame_product {C : Type v} [Category.{w} C]
    {O M : C} (s : O ⟶ M) (e f : M ⟶ O) (x y z : O ⟶ O)
    (hf : f = e ≫ y) (hs : s ≫ e = x) (hp : x ≫ y = z) : s ≫ f = z := by
  rw [hf, ← Category.assoc, hs, hp]

private theorem affine_scalar_injective (A : Type u) [CommRing A] (x y : A)
    (h : Scheme.Modules.globalSectionsSmul
        (SheafOfModules.unit (Spec (.of A)).ringCatSheaf) ((Scheme.ΓSpecIso (.of A)).inv x) =
      Scheme.Modules.globalSectionsSmul
        (SheafOfModules.unit (Spec (.of A)).ringCatSheaf) ((Scheme.ΓSpecIso (.of A)).inv y)) :
    x = y := by
  have he := congrArg (fun f : SheafOfModules.unit (Spec (.of A)).ringCatSheaf ⟶
      SheafOfModules.unit (Spec (.of A)).ringCatSheaf =>
    (f.val.app (op ⊤)).hom (1 : Γ(Spec (.of A), ⊤))) h
  have hx := unit_scalar_top (Spec (.of A)) ((Scheme.ΓSpecIso (.of A)).inv x)
  have hy := unit_scalar_top (Spec (.of A)) ((Scheme.ΓSpecIso (.of A)).inv y)
  have hxy := congrArg (fun r : Γ(Spec (.of A), ⊤) => (Scheme.ΓSpecIso (.of A)).hom r)
    (hx.symm.trans (he.trans hy))
  exact (ConcreteCategory.congr_hom (Scheme.ΓSpecIso (.of A)).inv_hom_id x).symm.trans
    (hxy.trans (ConcreteCategory.congr_hom (Scheme.ΓSpecIso (.of A)).inv_hom_id y))

private theorem section_value_replace {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules)
    (s t : SheafOfModules.unit Y.ringCatSheaf ⟶ M)
    (e : (Scheme.Modules.pullback f).obj M ⟶ SheafOfModules.unit X.ringCatSheaf)
    (z : Γ(X, ⊤)) (hst : s = t) (hs : sectionValue f M s e z) :
    sectionValue f M t e z := by
  cases hst
  exact hs

private theorem coframe_replace {C : Type v} [Category.{w} C] {M U : C}
    (f : M ⟶ U) (e0 e : M ≅ U) (a : U ⟶ U)
    (hf : f = e0.hom ≫ a) (he : e0 = e) : f = e.hom ≫ a := by
  cases he
  exact hf

private theorem section_value_product {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules)
    (s : SheafOfModules.unit Y.ringCatSheaf ⟶ M)
    (e e' : (Scheme.Modules.pullback f).obj M ⟶ SheafOfModules.unit X.ringCatSheaf)
    (x y z : Γ(X, ⊤))
    (hf : e' = e ≫ Scheme.Modules.globalSectionsSmul (SheafOfModules.unit X.ringCatSheaf) y)
    (hs : sectionValue f M s e x)
    (hp : Scheme.Modules.globalSectionsSmul (SheafOfModules.unit X.ringCatSheaf) x ≫
      Scheme.Modules.globalSectionsSmul (SheafOfModules.unit X.ringCatSheaf) y =
      Scheme.Modules.globalSectionsSmul (SheafOfModules.unit X.ringCatSheaf) z) :
    sectionValue f M s e' z :=
  section_frame_product (pullSection f M s) e e' _ _ _ hf hs hp

private theorem section_value_scalar {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules)
    (s : SheafOfModules.unit Y.ringCatSheaf ⟶ M)
    (e : (Scheme.Modules.pullback f).obj M ⟶ SheafOfModules.unit X.ringCatSheaf)
    (x y : Γ(X, ⊤)) (hxy : x = y) (hs : sectionValue f M s e x) :
    sectionValue f M s e y := by
  cases hxy
  exact hs

private theorem section_values_injective (A : Type u) [CommRing A] {Y : Scheme.{u}}
    (f : Spec (.of A) ⟶ Y) (M : Y.Modules)
    (s : SheafOfModules.unit Y.ringCatSheaf ⟶ M)
    (e : (Scheme.Modules.pullback f).obj M ⟶
      SheafOfModules.unit (Spec (.of A)).ringCatSheaf) (x y : A)
    (hx : sectionValue f M s e ((Scheme.ΓSpecIso (.of A)).inv x))
    (hy : sectionValue f M s e ((Scheme.ΓSpecIso (.of A)).inv y)) : x = y :=
  affine_scalar_injective A x y (hx.symm.trans hy)

section Polynomial
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K) (word : List G.rootBase.support) (i : G.rootBase.support)
    (V : Over (Spec (.of K))) (g : G.points)
    (b : V ⟶ (oppositeUnipotentVariety G).toOver)
    (c : V ⊗ (schubertVariety G
      (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver ⟶
        Over.mk (bsdhToSpec G (word ++ [i])))
    (hend : c.left ≫ (bsdhAppendIso G word i).hom.left ≫
      pullback.snd (bsdhMap G word) (flagBundleProjection G
        (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val))) =
      (b ⊗ₘ 𝟙 (schubertVariety G
        (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver).left ≫
          flagBundleChart G _ g)
    (B : CommAlgCat.{u} K) (p : (algSpec (.of K)).obj (op B) ⟶ V)

private theorem append_four_iso_eq (n : ℕ) (j : Fin 2) :
    fourFrameEq (projectiveLinePolynomialChart B ⟨j⟩)
      (projectiveAppendChart G i B p c)
      (CharacterLine.wordCharacterModule G (G.positiveRootCharacter ^ n) (word ++ [i]))
      (ProjectiveLine.projectiveTransitionModule B (2 * n))
      ((Scheme.Modules.restrictFunctor (projectiveLinePolynomialChart B ⟨j⟩)).obj
        (ProjectiveLine.projectiveTransitionModule B (2 * n)))
      (CharacterLine.appendCharacterDegreeIso G word i V g b c hend B p n)
      ((Scheme.Modules.restrictFunctorIsoPullback (projectiveLinePolynomialChart B ⟨j⟩)).symm.app
        (ProjectiveLine.projectiveTransitionModule B (2 * n)))
      (ProjectiveLine.projectiveTransitionChart B (2 * n) ⟨j⟩)
      (appendPolynomialFrame G word i V g b c hend B p n ⟨j⟩) := by
  rfl

private theorem append_section_from_polynomial (n : ℕ) (j : Fin 2)
    (hv : sectionValue (projectiveLinePolynomialChart B ⟨j⟩)
      (ProjectiveLine.projectiveTransitionModule B (2 * n))
      (CharacterLine.appendPolynomialSection G n i B (p ≫ b) g)
      (((Scheme.Modules.restrictFunctorIsoPullback
          (projectiveLinePolynomialChart B ⟨j⟩)).symm.app
            (ProjectiveLine.projectiveTransitionModule B (2 * n))).hom ≫
        (ProjectiveLine.projectiveTransitionChart B (2 * n) ⟨j⟩).hom)
      ((Scheme.ΓSpecIso (.of (Polynomial B))).inv
        (sectionChartPolynomial (2 * n) (framePolynomial G i B (p ≫ b) g ^ n) j))) :
    sectionValue
      (projectiveLinePolynomialChart B ⟨j⟩ ≫ projectiveAppendChart G i B p c)
      (CharacterLine.wordCharacterModule G (G.positiveRootCharacter ^ n) (word ++ [i]))
      (CharacterLine.wordDeterminantModuleSection G n (word ++ [i]))
      (appendPolynomialFrame G word i V g b c hend B p n ⟨j⟩).hom
      ((Scheme.ΓSpecIso (.of (Polynomial B))).inv
        (sectionChartPolynomial (2 * n) (framePolynomial G i B (p ≫ b) g ^ n) j)) := by
  have hs := CharacterLine.appendDeterminant_section G word i V g b c hend B p n
  exact fourFrame_section (projectiveLinePolynomialChart B ⟨j⟩)
    (projectiveAppendChart G i B p c)
    (CharacterLine.wordCharacterModule G (G.positiveRootCharacter ^ n) (word ++ [i]))
    (ProjectiveLine.projectiveTransitionModule B (2 * n))
    ((Scheme.Modules.restrictFunctor (projectiveLinePolynomialChart B ⟨j⟩)).obj
      (ProjectiveLine.projectiveTransitionModule B (2 * n)))
    (CharacterLine.wordDeterminantModuleSection G n (word ++ [i]))
    (CharacterLine.appendPolynomialSection G n i B (p ≫ b) g)
    (CharacterLine.appendCharacterDegreeIso G word i V g b c hend B p n)
    ((Scheme.Modules.restrictFunctorIsoPullback (projectiveLinePolynomialChart B ⟨j⟩)).symm.app
      (ProjectiveLine.projectiveTransitionModule B (2 * n)))
    (ProjectiveLine.projectiveTransitionChart B (2 * n) ⟨j⟩)
    (appendPolynomialFrame G word i V g b c hend B p n ⟨j⟩)
    ((Scheme.ΓSpecIso (.of (Polynomial B))).inv
      (sectionChartPolynomial (2 * n) (framePolynomial G i B (p ≫ b) g ^ n) j))
    (append_four_iso_eq G word i V g b c hend B p n j) hs hv

/-- Every character power of the append determinant section has the specified
coordinate on each of the two polynomial charts of the same append map. -/
theorem appendPolynomialFrame_section (n : ℕ) (j : Fin 2) :
    sectionValue
      (projectiveLinePolynomialChart B ⟨j⟩ ≫ projectiveAppendChart G i B p c)
      (CharacterLine.wordCharacterModule G (G.positiveRootCharacter ^ n) (word ++ [i]))
      (CharacterLine.wordDeterminantModuleSection G n (word ++ [i]))
      (appendPolynomialFrame G word i V g b c hend B p n ⟨j⟩).hom
      ((Scheme.ΓSpecIso (.of (Polynomial B))).inv
        (sectionChartPolynomial (2 * n) (framePolynomial G i B (p ≫ b) g ^ n) j)) := by
  exact append_section_from_polynomial G word i V g b c hend B p n j
    (polynomial_chart_section B (2 * n) (framePolynomial G i B (p ≫ b) g ^ n)
      (framePower_degree G n i B (p ≫ b) g) j)

end Polynomial

section Matching
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K) (word : List G.rootBase.support) (i : G.rootBase.support)
    {J : Type u} (F : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} K)
    [hopen : ∀ {s t} (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (F.map f).hom.toRingHom))]
    [hdir : ((F.op ⋙ algSpec (.of K) ⋙ Over.forget (Spec (.of K))) ⋙
      Scheme.forget).IsLocallyDirected]
    (cF : Cocone (F.op ⋙ algSpec (.of K))) (hcF : IsColimit cF)
    (q : cF.pt.left ⟶ bsdhScheme G (word ++ [i])) (point : J → G.points)
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
    (V : Over (Spec (.of K))) (g : G.points)
    (b : V ⟶ (oppositeUnipotentVariety G).toOver)
    (c : V ⊗ (schubertVariety G
      (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver ⟶
        Over.mk (bsdhToSpec G (word ++ [i])))
    (hend : c.left ≫ (bsdhAppendIso G word i).hom.left ≫
      pullback.snd (bsdhMap G word) (flagBundleProjection G
        (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val))) =
      (b ⊗ₘ 𝟙 (schubertVariety G
        (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver).left ≫
          flagBundleChart G _ g)
    (B : CommAlgCat.{u} K) (p : (algSpec (.of K)).obj (op B) ⟶ V)

/-- The word matching section has the append polynomial coordinate at every
power on the prescribed polynomial factor of each intersection chart. -/
theorem appendMatchingFrame_section (s : {s : Finset J // s.Nonempty})
    (j : Fin 2) (k : Spec (.of (F.obj s)) ⟶ Spec (.of (Polynomial B)))
    (hk : (cF.ι.app (op s)).left ≫ q =
      k ≫ projectiveLinePolynomialChart B ⟨j⟩ ≫ projectiveAppendChart G i B p c)
    (n : ℕ) :
    sectionValue (cF.ι.app (op s)).left
      (matchingModule F cF (wordTransitionUnit G F beta) n)
      (wordMatchingSection G F cF hcF (word ++ [i]) q n point a ha beta hgroup hco hn)
      (appendPowerFrame G word i F cF hcF q point a ha beta hgroup hco hn
        s V g b c hend B p j k hk n).hom
      (k.appTop ((Scheme.ΓSpecIso (.of (Polynomial B))).inv
        (sectionChartPolynomial (2 * n) (framePolynomial G i B (p ≫ b) g ^ n) j))) := by
  have hs := wordDeterminant_section_match G F cF hcF (word ++ [i]) q n
    point a ha beta hgroup hco hn
  have hi := iso_section_inverse
    (wordCharacterMatchingIso G F cF hcF (word ++ [i]) q n point a ha beta hgroup hco hn).symm
    (wordMatchingSection G F cF hcF (word ++ [i]) q n point a ha beta hgroup hco hn)
    (pullSection q (CharacterLine.wordCharacterModule G (G.positiveRootCharacter ^ n) (word ++ [i]))
      (CharacterLine.wordDeterminantModuleSection G n (word ++ [i]))) hs
  exact comparison_section (cF.ι.app (op s)).left q k
    (projectiveLinePolynomialChart B ⟨j⟩ ≫ projectiveAppendChart G i B p c) hk
    (matchingModule F cF (wordTransitionUnit G F beta) n)
    (CharacterLine.wordCharacterModule G (G.positiveRootCharacter ^ n) (word ++ [i]))
    (wordCharacterMatchingIso G F cF hcF (word ++ [i]) q n point a ha beta hgroup hco hn).symm
    (appendPolynomialFrame G word i V g b c hend B p n ⟨j⟩)
    (appendPowerFrame G word i F cF hcF q point a ha beta hgroup hco hn
      s V g b c hend B p j k hk n)
    (wordMatchingSection G F cF hcF (word ++ [i]) q n point a ha beta hgroup hco hn)
    (CharacterLine.wordDeterminantModuleSection G n (word ++ [i]))
    ((Scheme.ΓSpecIso (.of (Polynomial B))).inv
      (sectionChartPolynomial (2 * n) (framePolynomial G i B (p ≫ b) g ^ n) j)) rfl hi
    (appendPolynomialFrame_section G word i V g b c hend B p n j)

/-- On each original affine member, the word coefficient times the constructed
append unit has every power equal to the corresponding append section coordinate. -/
theorem appendWordCoefficient_coordinate (l : J) (j : Fin 2)
    (k : Spec (.of (F.obj (singletonIndex l))) ⟶ Spec (.of (Polynomial B)))
    (hk : (cF.ι.app (op (singletonIndex l))).left ≫ q =
      k ≫ projectiveLinePolynomialChart B ⟨j⟩ ≫ projectiveAppendChart G i B p c)
    (n : ℕ) :
    (wordRingCoefficient G F point a l *
        (appendFrameUnit G word i F cF hcF q point a ha beta hgroup hco hn
          (singletonIndex l) V g b c hend B p ⟨j⟩ k hk : F.obj (singletonIndex l))) ^ n =
      (Spec.preimage k).hom
        (sectionChartPolynomial (2 * n) (framePolynomial G i B (p ≫ b) g ^ n) j) := by
  let d := appendFrameUnit G word i F cF hcF q point a ha beta hgroup hco hn
    (singletonIndex l) V g b c hend B p ⟨j⟩ k hk
  let T := matchingModule F cF (wordTransitionUnit G F beta) n
  let U : (Spec (.of (F.obj (singletonIndex l)))).Modules :=
    SheafOfModules.unit (Spec (.of (F.obj (singletonIndex l)))).ringCatSheaf
  let aF := (cF.ι.app (op (singletonIndex l))).left
  let sF := wordMatchingSection G F cF hcF (word ++ [i]) q n point a ha beta hgroup hco hn
  let e := localCharacterTrivialization F cF hcF (wordTransitionUnit G F beta) n hco hn
    (singletonIndex l) l (Finset.mem_singleton_self l)
  let f := appendPowerFrame G word i F cF hcF q point a ha beta hgroup hco hn
    (singletonIndex l) V g b c hend B p j k hk n
  have hc := wordMatchingSection_from_coefficients G F cF hcF (word ++ [i]) q
    point a ha beta hgroup hco hn n
  have hm := matching_section_coordinate F cF hcF (wordTransitionUnit G F beta) n hco hn
    (wordRingCoefficient G F point a)
    (wordRingCoefficient_matching G F cF hcF (word ++ [i]) q point a ha beta hgroup hco hn) l
  have hs : sectionValue aF T sF e.hom
      ((Scheme.ΓSpecIso (.of (F.obj (singletonIndex l)))).inv
        ((wordRingCoefficient G F point a l) ^ n)) :=
    section_value_replace aF T _ sF e.hom _ hc hm
  have hsel := singleton_selected_frame F cF hcF (wordTransitionUnit G F beta) n hco hn l
  have hf : f.hom = e.hom ≫ Scheme.Modules.globalSectionsSmul U
      ((Scheme.ΓSpecIso (.of (F.obj (singletonIndex l)))).inv
        ((d : F.obj (singletonIndex l)) ^ n)) :=
    coframe_replace f.hom _ e _
      (appendPowerFrame_unit G word i F cF hcF q point a ha beta hgroup hco hn
        (singletonIndex l) V g b c hend B p j k hk n) hsel
  have hx := section_value_product aF T sF e.hom f.hom
    ((Scheme.ΓSpecIso (.of (F.obj (singletonIndex l)))).inv
      ((wordRingCoefficient G F point a l) ^ n))
    ((Scheme.ΓSpecIso (.of (F.obj (singletonIndex l)))).inv
      ((d : F.obj (singletonIndex l)) ^ n))
    ((Scheme.ΓSpecIso (.of (F.obj (singletonIndex l)))).inv
      ((wordRingCoefficient G F point a l * (d : F.obj (singletonIndex l))) ^ n))
    hf hs (affine_smul_power (F.obj (singletonIndex l)) U (wordRingCoefficient G F point a l)
      (d : F.obj (singletonIndex l)) n)
  have hy := appendMatchingFrame_section G word i F cF hcF q point a ha beta hgroup hco hn
    V g b c hend B p (singletonIndex l) j k hk n
  let P := sectionChartPolynomial (2 * n) (framePolynomial G i B (p ≫ b) g ^ n) j
  have hp : k.appTop ((Scheme.ΓSpecIso (.of (Polynomial B))).inv P) =
      (Scheme.ΓSpecIso (.of (F.obj (singletonIndex l)))).inv ((Spec.preimage k).hom P) := by
    simpa only [pow_one] using affine_preimage_coefficient k P 1
  have hy' := section_value_scalar aF T sF f.hom _ _ hp hy
  exact section_values_injective (F.obj (singletonIndex l)) aF T sF f.hom
    ((wordRingCoefficient G F point a l * (d : F.obj (singletonIndex l))) ^ n)
    ((Spec.preimage k).hom P) hx hy'

end Matching

end SchubertGeometry.RetainedCharacter
