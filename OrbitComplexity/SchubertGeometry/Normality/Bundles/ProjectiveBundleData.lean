import OrbitComplexity.FrobeniusSplitting.Normality.ComponentBundles
import Mathlib.AlgebraicGeometry.Group.Affine
import OrbitComplexity.GroupActions.Varieties.ProjectiveConnected
import OrbitComplexity.GroupActions.Varieties.ProjectiveChartsSmooth

/-! # Projective bundles over specified covered models -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
noncomputable section
universe u
namespace SchubertGeometry

/-- The glued total space retains its component squares and covers after every base change. -/
def projectiveBundleSpec {J R : Type u} [Category.{u} J] [CommRing R]
    (N : J ⥤ CommAlgCat.{u} R) (D : Jᵒᵖ ⥤ Scheme.{u})
    (π : D ⟶ N.op ⋙ algSpec (.of R) ⋙ Over.forget (Spec (.of R)))
    (cG : Cocone (N.op ⋙ algSpec (.of R))) : Prop :=
  ∃ (cD : Cocone D) (q : cD.pt ⟶ cG.pt.left),
    Nonempty (IsColimit cD) ∧
    (∀ j, cD.ι.app j ≫ q = π.app j ≫ (cG.ι.app j).left) ∧
    (∀ j, IsPullback (π.app j) (cD.ι.app j) (cG.ι.app j).left q) ∧
    IsProper q ∧ Smooth q ∧ GeometricallyConnected q ∧
    (∀ j, IsOpenImmersion (cD.ι.app j)) ∧
    ∀ (T : Scheme.{u}) (f : T ⟶ cD.pt) (y : T),
      ∃ j, ∃ z : (pullback f (cD.ι.app j) : Scheme.{u}),
        (pullback.fst f (cD.ι.app j)) z = y

end SchubertGeometry
