import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.MatchingWeightedTrace
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.ProjectiveOperatorMaps
import OrbitComplexity.SchubertGeometry.IntegralProjectiveLine.AffineFamilies
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Projective Cartier comparison on matching refinements

The coefficient refinement and affine coordinate change construct the
projective morphism. The full section equation then gives equality of the
determinant-inserted Cartier operators on the whole projective line.
-/

set_option autoImplicit false
noncomputable section
universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite Polynomial
open GroupActions FrobeniusSplitting FrobeniusSplitting.CharacterLine
open FrobeniusSplitting.RetainedCharacter

namespace SchubertGeometry.RetainedCharacter

open private projective_pullback
  from OrbitComplexity.GroupActions.Varieties.ProjectiveSpaceBaseChange
open private line indices sourceLine
  from OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeTwistedChartSource
open private sectionWeight
  from OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeCartierOperator
open private insertedInfinity
  from OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeTwistedSections
open private polynomialSection_weight
  from OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordCompatibleSplitting

private def affinePolynomialMap {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (a : Bˣ) (b : B) : Polynomial A →+* Polynomial B :=
  (Polynomial.algEquivCMulXAddC (a : B) b).toRingHom.comp (Polynomial.mapRingHom f)

private theorem affinePolynomialMap_apply {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (a : Bˣ) (b : B) (Q : Polynomial A) :
    affinePolynomialMap f a b Q = (Polynomial.map f Q).comp (C (a : B) * X + C b) := by
  change Polynomial.algEquivCMulXAddC (a : B) b (Polynomial.map f Q) = _
  exact Polynomial.algEquivCMulXAddC_apply _ _ _

private def projectiveRefinement {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (a : Bˣ) (b : B) : line B ⟶ line A :=
  (projectiveBaseChange (ULift.{u} (Fin 2)) f).hom ≫ (projectiveAffineFamily f a b).left

private theorem projectiveRefinement_open {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) [IsOpenImmersion (Spec.map (CommRingCat.ofHom f))]
    (a : Bˣ) (b : B) : IsOpenImmersion (projectiveRefinement f a b) := by
  let : IsOpenImmersion (projectiveCoeffMap (ULift.{u} (Fin 2)) f) :=
    MorphismProperty.of_isPullback (projective_pullback (ULift.{u} (Fin 2)) f).flip inferInstance
  have h : projectiveRefinement f a b =
      (projectiveLineScalingIso a).hom ≫ (projectiveLineTranslationIso b).hom ≫
        projectiveCoeffMap (ULift.{u} (Fin 2)) f := by
    change (projectiveBaseChange (ULift.{u} (Fin 2)) f).hom ≫
        (projectiveBaseChange (ULift.{u} (Fin 2)) f).inv ≫ _ = _
    exact Iso.hom_inv_id_assoc _ _
  rw [h]
  infer_instance

private def projectiveOperatorMapData {K A B : Type u} [Field K]
    [CommRing A] [CommRing B] [Algebra K A] [Algebra K B]
    {p : ℕ} [ExpChar K p] [PerfectRing K p]
    (ψA : FrobeniusLinearMap A p) (ψB : FrobeniusLinearMap B p)
    (f : A →+* B) (a : Bˣ) (b : B)
    (W : Polynomial A) (V : Polynomial B)
    (hW : W.natDegree ≤ p - 1) (hV : V.natDegree ≤ p - 1) : Prop :=
  ∃ (g : line B ⟶ line A) (hg : IsOpenImmersion g),
    g = projectiveRefinement f a b ∧
      Spec.map (CommRingCat.ofHom (affinePolynomialMap f a b)) ≫
          projectiveLinePolynomialChart A (⟨0⟩ : indices.{u}) =
        projectiveLinePolynomialChart B (⟨0⟩ : indices.{u}) ≫ g ∧
      let : IsOpenImmersion g := hg
      (ProjectiveCartier.relativeCartierOperator (K := K) ψA
        (insertedInfinity (ProjectiveLine.projectivePolynomialSection A (p - 1) W hW))).openPullback
            g =
        ProjectiveCartier.relativeCartierOperator (K := K) ψB
          (insertedInfinity (ProjectiveLine.projectivePolynomialSection B (p - 1) V hV))

private theorem polynomialCartier_map {K A B : Type u} [Field K]
    [CommRing A] [CommRing B] [Algebra K A] [Algebra K B]
    {p : ℕ} [ExpChar K p] [PerfectRing K p]
    (ψA : FrobeniusLinearMap A p) (ψB : FrobeniusLinearMap B p)
    (f : A →+* B) [IsOpenImmersion (Spec.map (CommRingCat.ofHom f))]
    (a : Bˣ) (b : B) (W : Polynomial A) (V : Polynomial B)
    (hW : W.natDegree ≤ p - 1) (hV : V.natDegree ≤ p - 1)
    (htrace : ∀ Q : Polynomial A,
      ((polynomialTraceOfOperator (K := K) ψB).weight V)
          ((Polynomial.map f Q).comp (C (a : B) * X + C b)) =
        (Polynomial.map f (((polynomialTraceOfOperator (K := K) ψA).weight W) Q)).comp
          (C (a : B) * X + C b)) :
    projectiveOperatorMapData (K := K) ψA ψB f a b W V hW hV := by
  let g := projectiveRefinement f a b
  let : IsOpenImmersion g := projectiveRefinement_open f a b
  have hchart : Spec.map (CommRingCat.ofHom (affinePolynomialMap f a b)) ≫
      projectiveLinePolynomialChart A (⟨0⟩ : indices.{u}) =
        projectiveLinePolynomialChart B (⟨0⟩ : indices.{u}) ≫ g :=
    (projectiveAffineFamily_chart f a b).symm
  let : IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (affinePolynomialMap f a b)) ≫
        projectiveLinePolynomialChart A (⟨0⟩ : indices.{u})) := by
    rw [hchart]
    infer_instance
  let : IsOpenImmersion (Spec.map (CommRingCat.ofHom (affinePolynomialMap f a b))) :=
    IsOpenImmersion.of_comp _ (projectiveLinePolynomialChart A (⟨0⟩ : indices.{u}))
  refine ⟨g, inferInstance, rfl, hchart, ?_⟩
  apply ProjectiveCartier.relativeCartierOperator_map (K := K) ψA ψB _ _
    (affinePolynomialMap f a b) g hchart
  intro Q
  simpa only [polynomialSection_weight, affinePolynomialMap_apply] using htrace Q

section Matching
variable {K R J : Type u} [Field K] [CommRing R] [Algebra K R]
    {p : ℕ} [ExpChar K p] [PerfectRing K p]
    (N : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} R)
    [hopen : ∀ {s t} (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (N.map f).hom.toRingHom))]
    [hdir : ((N.op ⋙ algSpec (.of R) ⋙ Over.forget (Spec (.of R))) ⋙
      Scheme.forget).IsLocallyDirected]
    (cN : Cocone (N.op ⋙ algSpec (.of R))) (hcN : IsColimit cN)
    (delta : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val)
      (k : J) (_ : k ∈ s.val), (N.obj s)ˣ) (n : ℕ)
    (hco : ∀ s j hj k hk l hl,
      delta s j hj l hl = delta s k hk l hl * delta s j hj k hk)
    (hn : ∀ s t (f : s ⟶ t) j hj k hk,
      Units.map (N.map f).hom.toMonoidHom (delta s j hj k hk) =
        delta t j ((leOfHom f) hj) k ((leOfHom f) hk))
    (base : cN.pt.left ⟶ Spec (.of K))
    (Θ : frobeniusRestriction K p base (matchingModule N cN delta n) ⟶
      SheafOfModules.unit cN.pt.left.ringCatSheaf)

/-- The full matching section equation identifies the determinant-inserted
Cartier operators on the projective refinement, including infinity. -/
theorem retainedCartier_refine
    {s t : {s : Finset J // s.Nonempty}} (f : s ⟶ t)
    (j : J) (hj : j ∈ s.val) (k : J) (hk : k ∈ t.val)
    (d : (N.obj s)ˣ) (e : (N.obj t)ˣ)
    (hp : 0 < p) (a : (N.obj t)ˣ) (b : N.obj t)
    (W : Polynomial (N.obj s)) (V : Polynomial (N.obj t))
    (hW : W.natDegree ≤ p - 1) (hV : V.natDegree ≤ p - 1)
    (hsection : V =
      C (((((delta t j ((leOfHom f) hj) k hk *
          Units.map (N.map f).hom.toMonoidHom d * e⁻¹) ^ n)⁻¹ :
            (N.obj t)ˣ) : N.obj t) * (↑(a⁻¹) : N.obj t) ^ (p - 1)) *
        (Polynomial.map (N.map f).hom.toRingHom W).comp (C (a : N.obj t) * X + C b)) :
    let : Algebra K (N.obj s) :=
      ((algebraMap R (N.obj s)).comp (algebraMap K R)).toAlgebra
    let : Algebra K (N.obj t) :=
      ((algebraMap R (N.obj t)).comp (algebraMap K R)).toAlgebra
    projectiveOperatorMapData (K := K)
      (ProjectiveCartier.retainedTwistedPriorOperator N cN hcN base
        (matchingModule N cN delta n) Θ s
        (retainedMatchingFrameSection N cN hcN delta n hco hn s j hj d))
      (ProjectiveCartier.retainedTwistedPriorOperator N cN hcN base
        (matchingModule N cN delta n) Θ t
        (retainedMatchingFrameSection N cN hcN delta n hco hn t k hk e))
      (N.map f).hom.toRingHom a b W V hW hV := by
  let : Algebra K (N.obj s) :=
    ((algebraMap R (N.obj s)).comp (algebraMap K R)).toAlgebra
  let : Algebra K (N.obj t) :=
    ((algebraMap R (N.obj t)).comp (algebraMap K R)).toAlgebra
  apply polynomialCartier_map (K := K) _ _ (N.map f).hom.toRingHom a b W V hW hV
  intro Q
  exact retainedWeightedTrace_refine N cN hcN delta n hco hn base Θ
    f j hj k hk d e hp a b W V hsection Q

end Matching
end SchubertGeometry.RetainedCharacter
