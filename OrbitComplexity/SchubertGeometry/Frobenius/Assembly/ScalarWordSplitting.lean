import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.ScalarWordCoordinates
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.ScalarNodeSquares
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordNodeCartier
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.ScalarAppendTransitions
import Mathlib.AlgebraicGeometry.RelativeGluing
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Splitting a prescribed scalar word model

The retained node coordinates and the original projective cocone supply the
section and transition inputs of the global word operator construction.
-/

set_option autoImplicit false
noncomputable section
universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite GroupActions
open FrobeniusSplitting FrobeniusSplitting.RetainedCharacter
open FrobeniusSplitting.OperatorSheaf
open scoped TensorProduct

open private sectionValue from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendSectionCoordinates
open private pullSection from
  OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.PullbackFrames
open private singletonIndex singletonArrow from
  OrbitComplexity.FrobeniusSplitting.Modules.MatchingModule
open private nodePolynomial polynomialLeg from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.RetainedWordCartier
open private affinePolynomialMap projectiveRefinement from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.MatchingOperatorOverlaps
open private affineProjectiveMap from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.ScalarProjectiveTransitions
open private polynomialScalar_base from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.ScalarProjectiveCharts
open private projectiveLinePolynomial_coeff from
  OrbitComplexity.SchubertGeometry.IntegralProjectiveLine.AffineFamilies
open private coefficient_comp from
  OrbitComplexity.SchubertGeometry.Normality.Transitions.AppendChartCoefficients
open private coefficient nodeBase projectiveScalar_square from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.ScalarProjectiveNodes
open private stageRings terminalRings from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.ScalarWordCoordinates
open private AppendChartData AppendChartData.I AppendChartData.N AppendChartData.sel
  AppendChartContext AppendChartStage AppendChartStage.q
  AppendChartContext.D AppendChartContext.eP AppendChartContext.cD AppendChartContext.base
  from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendRetentionContexts

namespace SchubertGeometry.RetainedCharacter

private abbrev unitModule (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

private abbrev line (A : Type u) [CommRing A] : Scheme.{u} :=
  projectiveScheme A (ULift.{u} (Fin 2))

private theorem refinement_eq {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (a : Bˣ) (b : B) :
    projectiveRefinement f a b = affineProjectiveMap f a b := by
  change (projectiveBaseChange (ULift.{u} (Fin 2)) f).hom ≫
      ((projectiveBaseChange (ULift.{u} (Fin 2)) f).inv ≫
        (projectiveLineScalingIso a).hom ≫ (projectiveLineTranslationIso b).hom ≫
          projectiveCoeffMap (ULift.{u} (Fin 2)) f) = _
  simp only [Iso.hom_inv_id_assoc]
  rfl

private theorem projective_chain {A B C D : Type u}
    [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    (f : A →+* B) (g : B →+* C) (h : C →+* D) :
    projectiveCoeffMap (ULift.{u} (Fin 2)) h ≫
      projectiveCoeffMap (ULift.{u} (Fin 2)) g ≫
        projectiveCoeffMap (ULift.{u} (Fin 2)) f =
      projectiveCoeffMap (ULift.{u} (Fin 2)) (h.comp (g.comp f)) := by
  rw [coefficient_comp, coefficient_comp]

private theorem projective_natural_chain {J : Type u} [Category J]
    (F₀ F₁ F₂ F₃ : J ⥤ CommRingCat.{u}) (μ₀ : F₀ ⟶ F₁)
    (μ₁ : F₁ ⟶ F₂) (μ₂ : F₂ ⟶ F₃) (s : J) :
    projectiveCoeffMap (ULift.{u} (Fin 2)) (μ₂.app s).hom ≫
      projectiveCoeffMap (ULift.{u} (Fin 2)) (μ₁.app s).hom ≫
        projectiveCoeffMap (ULift.{u} (Fin 2)) (μ₀.app s).hom =
      projectiveCoeffMap (ULift.{u} (Fin 2)) ((μ₀ ≫ μ₁ ≫ μ₂).app s).hom := by
  exact projective_chain (μ₀.app s).hom (μ₁.app s).hom (μ₂.app s).hom

private theorem spec_chain {A B C D : Type u}
    [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    (f : A →+* B) (g : B →+* C) (h : C →+* D) :
    Spec.map (CommRingCat.ofHom h) ≫ Spec.map (CommRingCat.ofHom g) ≫
        Spec.map (CommRingCat.ofHom f) = Spec.map (CommRingCat.ofHom (h.comp (g.comp f))) := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  rfl

private theorem pullback_right_cast {C : Type*} [Category C]
    {A X Y Z : C} {f : A ⟶ X} {g : A ⟶ Y} {h : X ⟶ Z}
    {k k' : Y ⟶ Z} (hk : k = k') (hp : IsPullback f g h k) :
    IsPullback f g h k' := hk ▸ hp

private theorem pullback_post_cast {C : Type*} [Category C]
    {P Q A X Y : C} {a b : P ⟶ Q} (e : Q ⟶ A) {f : P ⟶ X}
    {g : A ⟶ Y} {q : X ⟶ Y} (hab : a = b)
    (hp : IsPullback (a ≫ e) f g q) : IsPullback (b ≫ e) f g q := hab ▸ hp

private theorem node_projection_chain {C : Type*} [Category C]
    {P₀ PS PT PK X₀ XS XT XK : C}
    (cS : PS ⟶ P₀) (cT : PT ⟶ PS) (cK : PK ⟶ PT)
    (qS : XS ⟶ X₀) (qT : XT ⟶ XS) (qK : XK ⟶ XT)
    (old : P₀ ⟶ X₀) (nS : PS ⟶ XS) (nT : PT ⟶ XT) (nK : PK ⟶ XK)
    (hS : nS ≫ qS = cS ≫ old) (hT : nT ≫ qT = cT ≫ nS)
    (hK : nK ≫ qK = cK ≫ nT) :
    nK ≫ (qK ≫ qT ≫ qS) = (cK ≫ cT ≫ cS) ≫ old := by
  calc
    _ = (nK ≫ qK) ≫ qT ≫ qS := (Category.assoc _ _ _).symm
    _ = (cK ≫ nT) ≫ qT ≫ qS := congrArg (fun a => a ≫ qT ≫ qS) hK
    _ = cK ≫ (nT ≫ qT) ≫ qS := by simp only [Category.assoc]
    _ = cK ≫ (cT ≫ nS) ≫ qS := congrArg (fun a => cK ≫ a ≫ qS) hT
    _ = (cK ≫ cT) ≫ (nS ≫ qS) := by simp only [Category.assoc]
    _ = (cK ≫ cT) ≫ (cS ≫ old) := congrArg (fun a => (cK ≫ cT) ≫ a) hS
    _ = _ := by simp only [Category.assoc]

private theorem node_projection_cast {C : Type*} [Category C]
    {P Q A X Y : C} {a b : P ⟶ Q} (e : Q ⟶ A) (leg : A ⟶ Y)
    {n : P ⟶ X} {q : X ⟶ Y} (hab : a = b)
    (h : n ≫ q = a ≫ e ≫ leg) : n ≫ q = b ≫ e ≫ leg :=
  h.trans (congrArg (fun c => c ≫ e ≫ leg) hab)

private theorem polynomial_node_old {A B : Type u} [CommRing A] [CommRing B]
    {X Y : Scheme.{u}} (q : Y ⟶ X) (f : A →+* B)
    (old : line A ⟶ X) (K : line B ⟶ Y)
    (hold : K ≫ q = projectiveCoeffMap (ULift.{u} (Fin 2)) f ≫ old)
    (j : ULift.{u} (Fin 2)) :
    (projectiveLinePolynomialChart B j ≫ K) ≫ q =
      Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom f)) ≫
        projectiveLinePolynomialChart A j ≫ old := by
  calc
    _ = projectiveLinePolynomialChart B j ≫ (K ≫ q) := Category.assoc _ _ _
    _ = (projectiveLinePolynomialChart B j ≫ projectiveCoeffMap (ULift.{u} (Fin 2)) f) ≫ old := by
      rw [hold, Category.assoc]
    _ = _ := by
      simpa only [Category.assoc] using congrArg (fun a => a ≫ old)
        (projectiveLinePolynomial_coeff A B f j)

private theorem polynomial_node_base {R A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] {X : Scheme.{u}} (base : X ⟶ Spec (.of R)) (K : line A ⟶ X)
    (hbase : K ≫ base = projectiveToSpec A (ULift.{u} (Fin 2)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R A))) (j : ULift.{u} (Fin 2)) :
    (projectiveLinePolynomialChart A j ≫ K) ≫ base =
      Spec.map (CommRingCat.ofHom (algebraMap R (Polynomial A))) := by
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun a => projectiveLinePolynomialChart A j ≫ a) hbase).trans
      (polynomialScalar_base j))

private theorem nodes_cover {J : Type u} (A : J → Type u) [∀ s, CommRing (A s)]
    {X : Scheme.{u}} (K : ∀ s, line (A s) ⟶ X)
    (V : X.OpenCover.{u}) (index : V.I₀ → J × ULift.{u} (Fin 2))
    (eV : ∀ v, V.X v ≅ Spec (.of (Polynomial (A (index v).1))))
    (hchart : ∀ v, projectiveLinePolynomialChart (A (index v).1) (index v).2 ≫
      K (index v).1 = (eV v).inv ≫ V.f v) :
    ∀ x : X, ∃ s y, K s y = x := by
  intro x
  obtain ⟨v, z, hz⟩ := V.exists_eq x
  refine ⟨(index v).1, projectiveLinePolynomialChart (A (index v).1) (index v).2
    ((eV v).hom z), ?_⟩
  have he : (eV v).inv ((eV v).hom z) = z :=
    congrArg (fun f : V.X v ⟶ V.X v => f z) (eV v).hom_inv_id
  have hm := congrArg (fun f => f ((eV v).hom z)) (hchart v)
  exact hm.trans ((congrArg (V.f v) he).trans hz)

private theorem diagram_open {R J : Type u} [CommRing R] [Category J]
    (N : J ⥤ CommAlgCat.{u} R)
    [∀ {s t} (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (N.map f).hom.toRingHom))]
    (D : Jᵒᵖ ⥤ Scheme.{u})
    (π : D ⟶ N.op ⋙ algSpec (.of R) ⋙ Over.forget (Spec (.of R)))
    (hπ : π.Equifibered) : ∀ {s t} (f : s ⟶ t), IsOpenImmersion (D.map f) := by
  intro s t f
  exact MorphismProperty.of_isPullback (hπ f).flip
    (inferInstanceAs (IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (N.map f.unop).hom.toRingHom))))

section Models

variable {K₀ : Type u} [kField : Field K₀] [kClosed : IsAlgClosed K₀] [kZero : CharZero K₀]
    {S₀ S : Subalgebra ℤ K₀} {G : ReductiveGroups.ReductiveGroupData K₀}
    {word : List G.rootBase.support} {i : G.rootBase.support}
    (hS₀ : S₀ ≤ S) (input : AppendChartData S₀ G word i)
    (context : AppendChartContext input)
    {X₁ : Scheme.{u}} {base₁ : X₁ ⟶ Spec (.of S)}
    {m₁ : bsdhScheme G (word ++ [i]) ⟶ X₁}
    (d : @AppendChartStage.{u} K₀ kField kClosed kZero S₀ G word i S hS₀ input context X₁ base₁ m₁)
    {T κ : Type u} [tComm : CommRing T] [κComm : CommRing κ] [sTAlg : Algebra S T] [tκAlg : Algebra
        T κ]

private abbrev fieldRings := fixedFibreDiagram (R := κ) (M := κ) (@terminalRings.{u} K₀ kField
    kClosed kZero S₀ S G word i hS₀ input T tComm sTAlg)
private abbrev fieldPolynomials (Q : ∀ j, Polynomial ((@terminalRings.{u} K₀ kField kClosed kZero S₀
    S G word i hS₀ input T tComm sTAlg).obj (singletonIndex j))) :=
  matchingScalarPolynomial (@terminalRings.{u} K₀ kField kClosed kZero S₀ S G word i hS₀ input T
      tComm sTAlg) (@fieldRings.{u} K₀ kField kClosed kZero S₀ S G word i hS₀ input T κ tComm κComm
      sTAlg tκAlg)
    (fixedScalarMap T κ (@terminalRings.{u} K₀ kField kClosed kZero S₀ S G word i hS₀ input T tComm
        sTAlg)) Q

private abbrev fieldNodeBase (s) : line ((@fieldRings.{u} K₀ kField kClosed kZero S₀ S G word i hS₀
    input T κ tComm κComm sTAlg tκAlg).obj s) ⟶ Spec (.of κ) :=
  nodeBase T κ ((@terminalRings.{u} K₀ kField kClosed kZero S₀ S G word i hS₀ input T tComm
      sTAlg).obj s)

private def scalarCoefficients : (AppendChartData.N input) ⋙ forget₂ (CommAlgCat S₀) CommRingCat ⟶
    @fieldRings.{u} K₀ kField kClosed kZero S₀ S G word i hS₀ input T κ tComm κComm sTAlg tκAlg ⋙
        forget₂ (CommAlgCat κ) CommRingCat :=
  let : Algebra S₀ S := (Subalgebra.inclusion hS₀).toAlgebra
  fixedScalarMap S₀ S ((AppendChartData.N input)) ≫
    fixedScalarMap S T (@stageRings.{u} K₀ kField kClosed kZero S₀ S G word i hS₀ input) ≫
        fixedScalarMap T κ (@terminalRings.{u} K₀ kField kClosed kZero S₀ S G word i hS₀ input T
        tComm sTAlg)

variable {XT Xκ : Scheme.{u}}
    (baseT : XT ⟶ Spec (.of T)) (qT : XT ⟶ X₁)
    (baseκ : Xκ ⟶ Spec (.of κ)) (qκ : Xκ ⟶ XT)
    (L : ℕ → XT.Modules) (sectionHom : ∀ n, unitModule XT ⟶ L n)
    (Q : ∀ j, Polynomial ((@terminalRings.{u} K₀ kField kClosed kZero S₀ S G word i hS₀ input T
        tComm sTAlg).obj (singletonIndex j)))
    {C : Type u} [Field C] [Algebra C κ] {p : ℕ} [ExpChar C p] [PerfectRing C p]
    [∀ {s t} (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom ((@fieldRings.{u} K₀ kField kClosed kZero S₀ S G word i hS₀ input
          T κ tComm κComm sTAlg tκAlg).map f).hom.toRingHom))]
    [(((@fieldRings.{u} K₀ kField kClosed kZero S₀ S G word i hS₀ input T κ tComm κComm sTAlg
        tκAlg).op ⋙ algSpec (.of κ) ⋙ Over.forget (Spec (.of κ))) ⋙
      Scheme.forget).IsLocallyDirected]
    (cN : Cocone ((@fieldRings.{u} K₀ kField kClosed kZero S₀ S G word i hS₀ input T κ tComm κComm
        sTAlg tκAlg).op ⋙ algSpec (.of κ))) (hcN : IsColimit cN)
    (delta : ∀ (s : {s : Finset ((AppendChartData.I input)) // s.Nonempty})
      (j : (AppendChartData.I input)) (_ : j ∈ s.val)
      (k : (AppendChartData.I input)) (_ : k ∈ s.val),
        ((@fieldRings.{u} K₀ kField kClosed kZero S₀ S G word i hS₀ input T κ tComm κComm sTAlg
            tκAlg).obj s)ˣ)
    (hco : ∀ s j hj k hk l hl, delta s j hj l hl = delta s k hk l hl * delta s j hj k hk)
    (hn : ∀ s t (f : s ⟶ t) j hj k hk,
      Units.map ((@fieldRings.{u} K₀ kField kClosed kZero S₀ S G word i hS₀ input T κ tComm κComm
          sTAlg tκAlg).map f).hom.toMonoidHom (delta s j hj k hk) =
        delta t j ((leOfHom f) hj) k ((leOfHom f) hk))
    (hP : ∀ j, (@fieldPolynomials.{u} K₀ kField kClosed kZero S₀ S G word i hS₀ input T κ tComm
        κComm sTAlg tκAlg Q j).natDegree ≤ 2)
    (hr : ∀ s j (hj : j ∈ s.val) k (hk : k ∈ s.val),
      ((@fieldRings.{u} K₀ kField kClosed kZero S₀ S G word i hS₀ input T κ tComm κComm sTAlg
          tκAlg).map (singletonArrow s j hj)).hom
          ((@fieldPolynomials.{u} K₀ kField kClosed kZero S₀ S G word i hS₀ input T κ tComm κComm
              sTAlg tκAlg Q j).coeff 2) =
        ((@fieldRings.{u} K₀ kField kClosed kZero S₀ S G word i hS₀ input T κ tComm κComm sTAlg
            tκAlg).map (singletonArrow s k hk)).hom
          ((@fieldPolynomials.{u} K₀ kField kClosed kZero S₀ S G word i hS₀ input T κ tComm κComm
              sTAlg tκAlg Q k).coeff 2) * (delta s j hj k hk : _))
    (basePrior : cN.pt.left ⟶ Spec (.of C))
    (Θ : frobeniusRestriction C p basePrior
      (matchingModule (@fieldRings.{u} K₀ kField kClosed kZero S₀ S G word i hS₀ input T κ tComm
          κComm sTAlg tκAlg) cN delta ((p - 1) / 2)) ⟶ unitModule cN.pt.left)
    (hnorm : Θ.app ⊤ ((Scheme.Modules.Hom.app
      (coefficientMatchingSection (@fieldRings.{u} K₀ kField kClosed kZero S₀ S G word i hS₀ input T
          κ tComm κComm sTAlg tκAlg) cN delta
        (fun j => (@fieldPolynomials.{u} K₀ kField kClosed kZero S₀ S G word i hS₀ input T κ tComm
            κComm sTAlg tκAlg Q j).coeff 2) hr ((p - 1) / 2)) ⊤).hom
          (1 : Γ(cN.pt.left, ⊤))) = (1 : Γ(cN.pt.left, ⊤)))

end Models

end SchubertGeometry.RetainedCharacter
