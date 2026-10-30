import OrbitComplexity.SchubertGeometry.IntegralProjectiveLine.Charts
import OrbitComplexity.FrobeniusSplitting.Splittings.UnivariateSections
import OrbitComplexity.FrobeniusSplitting.Splittings.ChartComparison
import OrbitComplexity.FrobeniusSplitting.Splittings.Laurent
import OrbitComplexity.FrobeniusSplitting.Compatible.Morphisms

/-! # A splitting of the polynomial projective line -/

namespace SchubertGeometry
open AlgebraicGeometry CategoryTheory Opposite GroupActions FrobeniusSplitting
noncomputable section
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

private abbrev lineIndex : Type u := ULift.{u} (Fin 2)
private abbrev lineOpen (R : Type u) [CommRing R] (j : lineIndex.{u}) :=
  Proj.basicOpen (MvPolynomial.homogeneousSubmodule lineIndex.{u} R) (MvPolynomial.X j)

variable {R : Type u} [CommRing R] {p : ℕ} [ExpChar R p]

private def lineChartSplitting (base : RingSplitting R p) (j : lineIndex.{u}) :
    SchemeSplitting (lineOpen R j).toScheme p :=
  (base.univariate.toSpec (expChar_pos R p)).pushforward
    (projectiveLinePolynomialIso R j).hom

private theorem lineChart_cross (base : RingSplitting R p)
    (V : (projectiveScheme R lineIndex.{u}).Opens)
    (hV : V ≤ lineOpen R ⟨0⟩) (hV' : V ≤ lineOpen R ⟨1⟩) :
    (lineChartSplitting base ⟨0⟩).onSubopen V hV =
      (lineChartSplitting base ⟨1⟩).onSubopen V hV' := by
  let a : Spec (.of (LaurentPolynomial R)) ⟶ Spec (.of (Polynomial R)) :=
    Spec.map (CommRingCat.ofHom Polynomial.toLaurent)
  let b : Spec (.of (LaurentPolynomial R)) ⟶ Spec (.of (Polynomial R)) :=
    Spec.map (CommRingCat.ofHom
      ((LaurentPolynomial.invert : LaurentPolynomial R ≃ₐ[R] LaurentPolynomial R).toRingHom.comp
        Polynomial.toLaurent))
  have : IsOpenImmersion a :=
    IsOpenImmersion.of_isLocalization (Polynomial.X : Polynomial R)
  have ha (W : (Spec (.of (Polynomial R))).Opens) (s : Γ(Spec (.of (Polynomial R)), W)) :
      (base.laurent.toSpec (expChar_pos R p)).onOpen (a ⁻¹ᵁ W) (a.app W s) =
        a.app W ((base.univariate.toSpec (expChar_pos R p)).onOpen W s) :=
    base.univariate.toSpec_naturality base.laurent (expChar_pos R p)
      Polynomial.toLaurent (base.laurent_toLaurent) W s
  have hb (W : (Spec (.of (Polynomial R))).Opens) (s : Γ(Spec (.of (Polynomial R)), W)) :
      (base.laurent.toSpec (expChar_pos R p)).onOpen (b ⁻¹ᵁ W) (b.app W s) =
        b.app W ((base.univariate.toSpec (expChar_pos R p)).onOpen W s) := by
    apply base.univariate.toSpec_naturality base.laurent (expChar_pos R p) _ _ W s
    intro f
    change base.laurent (LaurentPolynomial.invert f.toLaurent) =
      LaurentPolynomial.invert (base.univariate f).toLaurent
    rw [base.laurent_invert, base.laurent_toLaurent]
  apply SchemeSplitting.chartFormula_eq (lineOpen R ⟨0⟩) (lineOpen R ⟨1⟩)
    (projectiveLinePolynomialIso R ⟨0⟩) (projectiveLinePolynomialIso R ⟨1⟩)
    (base.univariate.toSpec (expChar_pos R p)) (base.univariate.toSpec (expChar_pos R p))
    (base.laurent.toSpec (expChar_pos R p)) a b ha hb
    (projectiveLinePolynomial_overlap R) V hV hV'
  exact (le_inf hV hV').trans (projectiveLinePolynomial_inter R).symm.le

private theorem lineChart_compatible (base : RingSplitting R p)
    (i j : lineIndex.{u}) (V : (projectiveScheme R lineIndex.{u}).Opens)
    (hi : V ≤ lineOpen R i) (hj : V ≤ lineOpen R j) :
    (lineChartSplitting base i).onSubopen V hi =
      (lineChartSplitting base j).onSubopen V hj := by
  rcases i with ⟨i⟩
  rcases j with ⟨j⟩
  fin_cases i <;> fin_cases j
  · rfl
  · exact lineChart_cross base V hi hj
  · exact (lineChart_cross base V hj hi).symm
  · rfl

private theorem lineOpen_cover : (⨆ j : lineIndex.{u}, lineOpen R j) = ⊤ :=
  Proj.iSup_basicOpen_eq_top (MvPolynomial.homogeneousSubmodule lineIndex.{u} R)
    (MvPolynomial.X : lineIndex.{u} → MvPolynomial lineIndex.{u} R)
      (projective_irrelevant_eq_span R lineIndex.{u}).le

/-- The coefficient splitting extends to the projective line through reciprocal affine charts. -/
def projectiveLineSplitting (base : RingSplitting R p) :
    SchemeSplitting (projectiveScheme R (ULift.{u} (Fin 2))) p :=
  SchemeSplitting.glue (lineOpen R) (lineChartSplitting base)
    (lineChart_compatible base) lineOpen_cover

private theorem projectiveLineSplitting_chart (base : RingSplitting R p) (j : lineIndex.{u}) :
    (projectiveLineSplitting base).restrict (lineOpen R j) = lineChartSplitting base j :=
  SchemeSplitting.glue_restrict _ _ _ _ j

private theorem restrict_natural {X : Scheme.{u}} (splitting : SchemeSplitting X p)
    (U V : X.Opens) (s : Γ(X, V)) :
    (splitting.restrict U).onOpen (U.ι ⁻¹ᵁ V) (U.ι.app V s) =
      U.ι.app V (splitting.onOpen V s) :=
  splitting.restrict_comm (Set.image_preimage_subset _ _) s

private theorem projectiveLineSplitting_natural (base : RingSplitting R p) (j : lineIndex.{u})
    (V : (projectiveScheme R lineIndex.{u}).Opens) (s : Γ(projectiveScheme R lineIndex.{u}, V)) :
    (base.univariate.toSpec (expChar_pos R p)).onOpen
      (projectiveLinePolynomialChart R j ⁻¹ᵁ V)
      ((projectiveLinePolynomialChart R j).app V s) =
        (projectiveLinePolynomialChart R j).app V ((projectiveLineSplitting base).onOpen V s) := by
  change (base.univariate.toSpec (expChar_pos R p)).onOpen
    ((projectiveLinePolynomialIso R j).hom ⁻¹ᵁ (lineOpen R j).ι ⁻¹ᵁ V)
      ((projectiveLinePolynomialIso R j).hom.app ((lineOpen R j).ι ⁻¹ᵁ V)
        ((lineOpen R j).ι.app V s)) =
    (projectiveLinePolynomialIso R j).hom.app ((lineOpen R j).ι ⁻¹ᵁ V)
      ((lineOpen R j).ι.app V ((projectiveLineSplitting base).onOpen V s))
  rw [← SchemeSplitting.pushforward_app]
  change (projectiveLinePolynomialIso R j).hom.app ((lineOpen R j).ι ⁻¹ᵁ V)
    ((lineChartSplitting base j).onOpen ((lineOpen R j).ι ⁻¹ᵁ V)
      ((lineOpen R j).ι.app V s)) = _
  rw [← projectiveLineSplitting_chart, restrict_natural]

/-- The zero coordinate in each standard chart gives a distinguished section of the line. -/
def projectiveLineSection (R : Type u) [CommRing R] (j : ULift.{u} (Fin 2)) :
    Spec (.of R) ⟶ projectiveScheme R (ULift.{u} (Fin 2)) :=
  Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R))) ≫
    projectiveLinePolynomialChart R j

private theorem projectiveLineSection_base (j : lineIndex.{u}) :
    projectiveLineSection R j ≫ projectiveToSpec R lineIndex.{u} = 𝟙 _ := by
  rw [projectiveLineSection, Category.assoc, projectiveLinePolynomialChart_base,
    ← Spec.map_comp]
  rw [show CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R) ≫
    CommRingCat.ofHom (Polynomial.evalRingHom 0) = 𝟙 (CommRingCat.of R) from by
      ext r
      simp]
  exact Spec.map_id _

private instance projectiveLineSection_closed (j : lineIndex.{u}) :
    IsClosedImmersion (projectiveLineSection R j) := by
  have : IsClosedImmersion (projectiveLineSection R j ≫ projectiveToSpec R lineIndex.{u}) := by
    rw [projectiveLineSection_base]
    infer_instance
  exact IsClosedImmersion.of_comp _ (projectiveToSpec R lineIndex.{u})

/-- Both distinguished sections are compatible with the projective-line splitting. -/
theorem projectiveLineSplitting_sections (base : RingSplitting R p) (j : ULift.{u} (Fin 2)) :
    (projectiveLineSplitting base).IsCompatible (projectiveLineSection R j).ker := by
  apply SchemeSplitting.isCompatible_ker (base.toSpec (expChar_pos R p))
    (projectiveLineSplitting base) (projectiveLineSection R j)
  intro V s
  change (base.toSpec (expChar_pos R p)).onOpen
    (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R))) ⁻¹ᵁ
      (projectiveLinePolynomialChart R j) ⁻¹ᵁ V)
    ((Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))).app
      ((projectiveLinePolynomialChart R j) ⁻¹ᵁ V)
      ((projectiveLinePolynomialChart R j).app V s)) =
    (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))).app
      ((projectiveLinePolynomialChart R j) ⁻¹ᵁ V)
      ((projectiveLinePolynomialChart R j).app V ((projectiveLineSplitting base).onOpen V s))
  rw [base.univariate.toSpec_naturality base (expChar_pos R p)
    (Polynomial.evalRingHom 0) (fun f => (base.univariate_eval_zero f).symm)]
  rw [projectiveLineSplitting_natural]

end
end SchubertGeometry
