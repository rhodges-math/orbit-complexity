import OrbitComplexity.SchubertGeometry.Normality.Bundles.ProjectiveBundleData
import OrbitComplexity.SchubertGeometry.Frobenius.ProjectiveLine

/-! # Infinity sections of specified projective diagrams -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroupActions
noncomputable section
universe u
namespace SchubertGeometry

/-- The same distinguished infinity points form an section of the diagram. -/
def infinityDiagramSpec {J R : Type u} [Category.{u} J] [CommRing R]
    (N : J ⥤ CommAlgCat.{u} R) (D : Jᵒᵖ ⥤ Scheme.{u})
    (π : D ⟶ N.op ⋙ algSpec (.of R) ⋙ Over.forget (Spec (.of R)))
    (e : ∀ j, D.obj j ≅ projectiveScheme (N.obj j.unop) (ULift.{u} (Fin 2))) : Prop :=
  ∃ s : (N.op ⋙ algSpec (.of R) ⋙ Over.forget (Spec (.of R))) ⟶ D,
    s ≫ π = 𝟙 _ ∧
    ∀ j, s.app j ≫ (e j).hom = projectiveLineSection (N.obj j.unop) ⟨1⟩

end SchubertGeometry
