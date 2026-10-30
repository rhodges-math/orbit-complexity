import OrbitComplexity.SchubertGeometry.IntegralProjectiveLine.Diagram
import OrbitComplexity.FrobeniusSplitting.Normality.CoordinateEquiv
import OrbitComplexity.SchubertGeometry.IntegralProjectiveLine.Charts

/-! # Polynomial and Laurent coordinates of the canonical projective-line diagram -/

open CategoryTheory AlgebraicGeometry Opposite MvPolynomial
open FrobeniusSplitting GroupActions
noncomputable section
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
namespace SchubertGeometry

/-- The intersection-diagram index of one standard homogeneous-coordinate chart. -/
def integralLineChartIndex (j : ULift.{u} (Fin 2)) : ProjectiveLineIndex.{u} :=
  ⟨{j}, Finset.singleton_nonempty j⟩

/-- The intersection-diagram index of both standard projective-line charts. -/
def integralLineOverlapIndex : ProjectiveLineIndex.{u} :=
  ⟨{⟨0⟩, ⟨1⟩}, by simp⟩

/-- The first standard chart restricts to the two-chart intersection. -/
def integralLineLeftRestriction :
    integralLineChartIndex ⟨0⟩ ⟶ integralLineOverlapIndex.{u} :=
  homOfLE (by
    intro i hi
    have h : i = ⟨0⟩ := by simpa only [integralLineChartIndex, Finset.mem_singleton] using hi
    subst i
    simp [integralLineOverlapIndex])

/-- The second standard chart restricts to the two-chart intersection. -/
def integralLineRightRestriction :
    integralLineChartIndex ⟨1⟩ ⟶ integralLineOverlapIndex.{u} :=
  homOfLE (by
    intro i hi
    have h : i = ⟨1⟩ := by simpa only [integralLineChartIndex, Finset.mem_singleton] using hi
    subst i
    simp [integralLineOverlapIndex])

variable (S : Type u) [CommRing S]

private def coordinateOpen (j : ULift.{u} (Fin 2)) :
    (projectiveScheme S (ULift.{u} (Fin 2))).Opens :=
  Proj.basicOpen (homogeneousSubmodule (ULift.{u} (Fin 2)) S) (X j)

private def coordinateRestrictions : ProjectiveLineIndex.{u}ᵒᵖ ⥤ Over (Spec (.of S)) :=
  intersectionOpens (coordinateOpen S) ⋙
    (projectiveScheme S (ULift.{u} (Fin 2))).restrictFunctor ⋙
      Over.map (projectiveToSpec S (ULift.{u} (Fin 2)))

private instance coordinate_affine (s : ProjectiveLineIndex.{u}) :
    IsAffine ((coordinateRestrictions S).obj (.op s)).left := by
  apply intersectionOpens_affine (coordinateOpen S) ?_ (.op s)
  intro j
  change IsAffineOpen (Proj.basicOpen (homogeneousSubmodule (ULift.{u} (Fin 2)) S) (X j))
  rw [← projectiveChartMap_range]
  exact isAffineOpen_opensRange (projectiveChartMap S (ULift.{u} (Fin 2)) j)

private def openPresentation (A : CommAlgCat.{u} S)
    (U : (projectiveScheme S (ULift.{u} (Fin 2))).Opens)
    (f : ((algSpec (.of S)).obj (.op A)).left ⟶ projectiveScheme S (ULift.{u} (Fin 2)))
    [IsOpenImmersion f] (hr : Set.range f = Set.range U.ι)
    (hb : f ≫ projectiveToSpec S (ULift.{u} (Fin 2)) = ((algSpec (.of S)).obj (.op A)).hom) :
    {e : (algSpec (.of S)).obj (.op A) ≅
      Over.mk (U.ι ≫ projectiveToSpec S (ULift.{u} (Fin 2))) // e.hom.left ≫ U.ι = f} := by
  let e := IsOpenImmersion.isoOfRangeEq f U.ι hr
  refine ⟨Over.isoMk e ?_, ?_⟩
  · change e.hom ≫ (U.ι ≫ projectiveToSpec S (ULift.{u} (Fin 2))) = _
    rw [← Category.assoc, IsOpenImmersion.isoOfRangeEq_hom_fac]
    exact hb
  · exact IsOpenImmersion.isoOfRangeEq_hom_fac f U.ι hr

private def chartData (j : ULift.{u} (Fin 2)) :
    {e : (algSpec (.of S)).obj (.op (CommAlgCat.of S (Polynomial S))) ≅
      (coordinateRestrictions S).obj (.op (integralLineChartIndex j)) //
        e.hom.left ≫ ((intersectionOpens (coordinateOpen S)).obj
          (.op (integralLineChartIndex j))).ι = projectiveLinePolynomialChart S j} := by
  let U := (intersectionOpens (coordinateOpen S)).obj (.op (integralLineChartIndex j))
  have hr : Set.range (projectiveLinePolynomialChart S j) = Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    change (↑(projectiveLinePolynomialChart S j).opensRange :
      Set (projectiveScheme S (ULift.{u} (Fin 2)))) = _
    rw [projectiveLinePolynomialChart_range]
    simp only [U, intersectionOpens, integralLineChartIndex, Finset.mem_singleton,
      iInf_iInf_eq_left, coordinateOpen]
  exact @openPresentation S _ (.of S (Polynomial S)) U (projectiveLinePolynomialChart S j)
    (projectiveLinePolynomialChart_open S j) hr (projectiveLinePolynomialChart_base S j)

private def laurentChart : Spec (.of (LaurentPolynomial S)) ⟶
    projectiveScheme S (ULift.{u} (Fin 2)) :=
  Spec.map (CommRingCat.ofHom (Polynomial.toLaurent : Polynomial S →+* LaurentPolynomial S)) ≫
    projectiveLinePolynomialChart S ⟨0⟩

private instance laurentChart_open : IsOpenImmersion (laurentChart S) := by
  have : IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (Polynomial.toLaurent : Polynomial S →+* LaurentPolynomial S))) :=
    IsOpenImmersion.of_isLocalization (Polynomial.X : Polynomial S)
  unfold laurentChart
  infer_instance

private def overlapData :
    {e : (algSpec (.of S)).obj (.op (CommAlgCat.of S (LaurentPolynomial S))) ≅
      (coordinateRestrictions S).obj (.op integralLineOverlapIndex) //
        e.hom.left ≫ ((intersectionOpens (coordinateOpen S)).obj (.op integralLineOverlapIndex)).ι =
          laurentChart S} := by
  let U := (intersectionOpens (coordinateOpen S)).obj (.op integralLineOverlapIndex)
  have hr : Set.range (laurentChart S) = Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    change (↑(laurentChart S).opensRange : Set (projectiveScheme S (ULift.{u} (Fin 2)))) = _
    rw [show (laurentChart S).opensRange = coordinateOpen S ⟨0⟩ ⊓ coordinateOpen S ⟨1⟩ from
      projectiveLinePolynomial_inter S]
    simp only [U, intersectionOpens, integralLineOverlapIndex, Finset.mem_insert,
      Finset.mem_singleton, iInf_or, iInf_inf_eq, iInf_iInf_eq_left]
  have hb : laurentChart S ≫ projectiveToSpec S (ULift.{u} (Fin 2)) =
      ((algSpec (.of S)).obj (.op (CommAlgCat.of S (LaurentPolynomial S)))).hom := by
    rw [algSpec_obj_hom]
    change laurentChart S ≫ projectiveToSpec S (ULift.{u} (Fin 2)) =
      Spec.map (CommRingCat.ofHom (algebraMap S (LaurentPolynomial S)))
    rw [laurentChart, Category.assoc, projectiveLinePolynomialChart_base, ← Spec.map_comp]
    congr 1
    ext s
    simp
  exact @openPresentation S _ (.of S (LaurentPolynomial S)) U (laurentChart S)
    (laurentChart_open S) hr hb

/-- A singleton node of the canonical projective-line diagram is a polynomial algebra. -/
@[irreducible] def integralLineChartEquiv (j : ULift.{u} (Fin 2)) :
    Polynomial S ≃ₐ[S] ((projectiveLineDiagram S).obj (integralLineChartIndex j)) :=
  coordinateEquivOfSpecIso S (.of S (Polynomial S))
    ((coordinateRestrictions S).obj (.op (integralLineChartIndex j))) (chartData S j).val

/-- The double node of the canonical projective-line diagram is a Laurent polynomial algebra. -/
@[irreducible] def integralLineOverlapEquiv :
    LaurentPolynomial S ≃ₐ[S] ((projectiveLineDiagram S).obj integralLineOverlapIndex) :=
  coordinateEquivOfSpecIso S (.of S (LaurentPolynomial S))
    ((coordinateRestrictions S).obj (.op integralLineOverlapIndex)) (overlapData S).val

set_option backward.isDefEq.respectTransparency.types false in
private theorem coordinateRestriction (j : ULift.{u} (Fin 2))
    (f : integralLineChartIndex j ⟶ integralLineOverlapIndex)
    (g : Polynomial S →ₐ[S] LaurentPolynomial S)
    (h : laurentChart S = Spec.map (CommRingCat.ofHom g.toRingHom) ≫
      projectiveLinePolynomialChart S j) (p : Polynomial S) :
    ((projectiveLineDiagram S).map f).hom (integralLineChartEquiv S j p) =
      integralLineOverlapEquiv S (g p) := by
  let E := (coordinateRestrictions S).obj (.op (integralLineChartIndex j))
  let F := (coordinateRestrictions S).obj (.op integralLineOverlapIndex)
  let e := (chartData S j).val
  let d := (overlapData S).val
  let m := (coordinateRestrictions S).map f.op
  let γ := CommAlgCat.ofHom g
  have hs : d.hom ≫ m = (algSpec (.of S)).map γ.op ≫ e.hom := by
    ext1
    simp only [Over.comp_left]
    let U := (intersectionOpens (coordinateOpen S)).obj (.op (integralLineChartIndex j))
    let V := (intersectionOpens (coordinateOpen S)).obj (.op integralLineOverlapIndex)
    let dl : Spec (.of (LaurentPolynomial S)) ⟶ V.toScheme := d.hom.left
    let ml : V.toScheme ⟶ U.toScheme := m.left
    let el : Spec (.of (Polynomial S)) ⟶ U.toScheme := e.hom.left
    let gl : Spec (.of (LaurentPolynomial S)) ⟶ Spec (.of (Polynomial S)) :=
      ((algSpec (.of S)).map γ.op).left
    have hd : dl ≫ V.ι = laurentChart S := (overlapData S).property
    have he : el ≫ U.ι = projectiveLinePolynomialChart S j := (chartData S j).property
    have hm : ml ≫ U.ι = V.ι := by
      let hVU : V ≤ U := leOfHom ((intersectionOpens (coordinateOpen S)).map f.op)
      change (projectiveScheme S (ULift.{u} (Fin 2))).homOfLE hVU ≫ U.ι = V.ι
      exact Scheme.homOfLE_ι _ hVU
    have hplain : dl ≫ ml = gl ≫ el := by
      apply (cancel_mono U.ι).mp
      rw [Category.assoc, hm, hd, Category.assoc, he]
      exact h
    exact hplain
  have hm := coordinateEquivOfSpecIso_map S (CommAlgCat.of S (Polynomial S))
    (CommAlgCat.of S (LaurentPolynomial S)) E F e d m γ hs p
  unfold integralLineChartEquiv integralLineOverlapEquiv
  exact hm

/-- The first chart restriction is the usual inclusion into Laurent polynomials. -/
theorem integralLineRestriction_left (p : Polynomial S) :
    ((projectiveLineDiagram S).map integralLineLeftRestriction).hom
        (integralLineChartEquiv S ⟨0⟩ p) =
      integralLineOverlapEquiv S (Polynomial.toLaurent p) :=
  coordinateRestriction S ⟨0⟩ integralLineLeftRestriction Polynomial.toLaurentAlg rfl p

/-- The second chart restriction substitutes the inverse Laurent coordinate. -/
theorem integralLineRestriction_right (p : Polynomial S) :
    ((projectiveLineDiagram S).map integralLineRightRestriction).hom
        (integralLineChartEquiv S ⟨1⟩ p) =
      integralLineOverlapEquiv S (LaurentPolynomial.invert (Polynomial.toLaurent p)) :=
  coordinateRestriction S ⟨1⟩ integralLineRightRestriction
    ((LaurentPolynomial.invert : LaurentPolynomial S ≃ₐ[S] LaurentPolynomial S).toAlgHom.comp
      Polynomial.toLaurentAlg) (projectiveLinePolynomial_overlap S) p

end SchubertGeometry
