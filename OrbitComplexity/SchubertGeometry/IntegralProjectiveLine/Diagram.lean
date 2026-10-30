import OrbitComplexity.GroupActions.Varieties.ProjectiveChartsSmooth
import OrbitComplexity.FrobeniusSplitting.Normality.CoordinateCocones
import OrbitComplexity.FrobeniusSplitting.Normality.IntersectionSquares
import OrbitComplexity.FrobeniusSplitting.Normality.DirectedSpectra
import Mathlib.RingTheory.Smooth.Flat

/-! # The integral affine-intersection diagram of a projective line

The two homogeneous coordinate charts and their intersection form a finite thin diagram.
Their coordinate spectra have a specified colimit over the coefficient ring.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite MvPolynomial
open FrobeniusSplitting GroupActions
noncomputable section
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
namespace SchubertGeometry

private abbrev P1Index := ULift.{u} (Fin 2)

/-- The three nonempty subsets of the two homogeneous coordinate indices. -/
abbrev ProjectiveLineIndex := {s : Finset (ULift.{u} (Fin 2)) // s.Nonempty}

variable (S : Type u) [CommRing S]

private def chartOpen (j : P1Index) : (projectiveScheme S P1Index).Opens :=
  Proj.basicOpen (homogeneousSubmodule P1Index S) (X j)

private theorem chart_affine (j : P1Index) : IsAffineOpen (chartOpen S j) := by
  rw [chartOpen, ← projectiveChartMap_range S P1Index j]
  exact isAffineOpen_opensRange (projectiveChartMap S P1Index j)

private theorem chart_cover : (⨆ j, chartOpen S j) = ⊤ := by
  have h := (projectiveChartCover S P1Index).iSup_opensRange
  simpa only [projectiveChartCover, projectiveChartMap_range, chartOpen] using h

/-- The projective-line coordinate diagram consists of its two charts and their intersection. -/
def projectiveLineDiagram : ProjectiveLineIndex ⥤ CommAlgCat.{u} S :=
  @intersectionCoordinates.{u,u,u} S (inferInstanceAs (CommRing S))
    (projectiveScheme S P1Index) (projectiveToSpec S P1Index)
    ProjectiveLineIndex (inferInstanceAs (Category ProjectiveLineIndex))
    (intersectionOpens (chartOpen S))

private theorem node_smooth (s : ProjectiveLineIndex) :
    Algebra.Smooth S ((projectiveLineDiagram S).obj s) := by
  let D := intersectionOpens (chartOpen S) ⋙
    (projectiveScheme S P1Index).restrictFunctor ⋙ Over.map (projectiveToSpec S P1Index)
  have : IsAffine (D.obj (.op s)).left :=
    intersectionOpens_affine (chartOpen S) (chart_affine S) (.op s)
  have hsm : Smooth (D.obj (.op s)).hom := by
    change Smooth (((intersectionOpens (chartOpen S)).obj (.op s)).ι ≫
      projectiveToSpec S P1Index)
    infer_instance
  change ((D.obj (.op s)).hom.appTop.hom.comp (Scheme.ΓSpecIso (.of S)).inv.hom).Smooth
  exact (RingHom.Smooth.of_bijective (ConcreteCategory.bijective_of_isIso
    (Scheme.ΓSpecIso (.of S)).inv)).comp
      (HasRingHomProperty.appTop (P := @Smooth) (D.obj (.op s)).hom hsm)

/-- Every coordinate node of the projective-line diagram is finitely presented over its base. -/
instance projectiveLineDiagram_finite (s : ProjectiveLineIndex) :
    Algebra.FinitePresentation S ((projectiveLineDiagram S).obj s) := by
  let := node_smooth S s
  infer_instance

/-- Every coordinate node of the projective-line diagram is flat over its base. -/
instance projectiveLineDiagram_flat (s : ProjectiveLineIndex) :
    Module.Flat S ((projectiveLineDiagram S).obj s) := by
  let := node_smooth S s
  infer_instance

/-- Every restriction in the projective-line coordinate diagram induces an open immersion. -/
instance projectiveLineDiagram_open {i j : ProjectiveLineIndex} (f : i ⟶ j) :
    IsOpenImmersion
      (Spec.map (CommRingCat.ofHom ((projectiveLineDiagram S).map f).hom.toRingHom)) := by
  let D := intersectionOpens (chartOpen S) ⋙
    (projectiveScheme S P1Index).restrictFunctor ⋙ Over.map (projectiveToSpec S P1Index)
  have (s : ProjectiveLineIndexᵒᵖ) : IsAffine (D.obj s).left :=
    intersectionOpens_affine (chartOpen S) (chart_affine S) s
  change IsOpenImmersion ((D ⋙ algΓ (.of S) ⋙ algSpec (.of S)).map f.op).left
  apply coordinateMaps_open
  intro a b g
  change IsOpenImmersion ((projectiveScheme S P1Index).homOfLE
    (leOfHom ((intersectionOpens (chartOpen S)).map g)))
  infer_instance

/-- Union of chart indices makes the projective-line spectrum diagram locally directed. -/
instance projectiveLineDiagram_directed :
    ((projectiveLineDiagram S).op ⋙ algSpec (.of S) ⋙ Over.forget (Spec (.of S)) ⋙
      Scheme.forget).IsLocallyDirected := by
  apply specs_locallyDirected
  intro i j k fi fj
  obtain ⟨l, gi, gj, h⟩ := intersectionCoordinates_refine
    (projectiveToSpec S P1Index) (chartOpen S) (chart_affine S)
      (.op i) (.op j) (.op k) fi.op fj.op
  exact ⟨l.unop, gi.unop, gj.unop, h⟩

/-- The coordinate spectrum charts map to the projective line over their coefficient ring. -/
def projectiveLineCocone : Cocone ((projectiveLineDiagram S).op ⋙ algSpec (.of S)) :=
  intersectionCoordinateCocone (projectiveToSpec S P1Index) (chartOpen S) (chart_affine S)

/-- The projective line is the colimit of its three coordinate spectra over the base ring. -/
def projectiveLineCoconeIsColimit : IsColimit (projectiveLineCocone S) :=
  coordinateCoconeIsColimit (projectiveToSpec S P1Index) (chartOpen S)
    (chart_affine S) (chart_cover S)

/-- The specified coordinate colimit is the given projective-line structure morphism. -/
def projectiveLineCoconeIso :
    (projectiveLineCocone S).pt ≅ Over.mk (projectiveToSpec S (ULift.{u} (Fin 2))) := Iso.refl _

private theorem integerLift_smooth : Algebra.Smooth ℤ (ULift.{u} ℤ) := by
  apply RingHom.smooth_algebraMap.mp
  apply RingHom.Smooth.of_bijective
  change Function.Bijective (ULift.up : ℤ → ULift.{u} ℤ)
  exact Equiv.ulift.symm.bijective

private theorem integer_scalarTower (A B : Type*) [CommRing A] [CommRing B] [Algebra A B] :
    IsScalarTower ℤ A B := by
  apply IsScalarTower.of_algebraMap_eq'
  exact Subsingleton.elim _ _

/-- The integral projective-line coordinates are finitely presented over the integers. -/
instance projectiveLineDiagram_intFinite (s : ProjectiveLineIndex.{u}) :
    Algebra.FinitePresentation ℤ ((projectiveLineDiagram (ULift.{u} ℤ)).obj s) := by
  let := integerLift_smooth.{u}
  let := node_smooth (ULift.{u} ℤ) s
  let := integer_scalarTower (ULift.{u} ℤ) ((projectiveLineDiagram (ULift.{u} ℤ)).obj s)
  let := Algebra.Smooth.comp ℤ (ULift.{u} ℤ)
    ((projectiveLineDiagram (ULift.{u} ℤ)).obj s)
  infer_instance

/-- The integral projective-line coordinates are flat over the integers. -/
instance projectiveLineDiagram_intFlat (s : ProjectiveLineIndex.{u}) :
    Module.Flat ℤ ((projectiveLineDiagram (ULift.{u} ℤ)).obj s) := by
  let := integerLift_smooth.{u}
  let := node_smooth (ULift.{u} ℤ) s
  let := integer_scalarTower (ULift.{u} ℤ) ((projectiveLineDiagram (ULift.{u} ℤ)).obj s)
  let := Algebra.Smooth.comp ℤ (ULift.{u} ℤ)
    ((projectiveLineDiagram (ULift.{u} ℤ)).obj s)
  infer_instance

end SchubertGeometry
