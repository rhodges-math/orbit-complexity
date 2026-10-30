import OrbitComplexity.SchubertGeometry.IntegralProjectiveLine.Automorphisms
import OrbitComplexity.GroupActions.Varieties.ProjectiveSpaceBaseChange
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.AlgebraicGeometry.Group.Affine

/-! # Projective-line diagrams with specified affine transitions -/

open CategoryTheory AlgebraicGeometry GroupActions
noncomputable section
universe u
namespace SchubertGeometry

/-- Projective-line pieces retain their chosen coefficient maps and every affine transition. -/
def projectiveTransitionSpec {I R : Type u} [CommRing R]
    (N : {s : Finset I // s.Nonempty} ⥤ CommAlgCat.{u} R)
    (sel : ∀ s : {s : Finset I // s.Nonempty}, {j : I // j ∈ s.val})
    (c : ∀ (s : {s : Finset I // s.Nonempty}) (j : I) (_ : j ∈ s.val)
      (k : I) (_ : k ∈ s.val), (N.obj s)ˣ)
    (a : ∀ (s : {s : Finset I // s.Nonempty}) (j : I) (_ : j ∈ s.val)
      (k : I) (_ : k ∈ s.val), N.obj s) : Prop :=
  let C := {s : Finset I // s.Nonempty}
  let B := N.op ⋙ algSpec (.of R) ⋙ Over.forget (Spec (.of R))
  ∃ (D : Cᵒᵖ ⥤ Scheme.{u})
    (e : ∀ s : C, D.obj (.op s) ≅ projectiveScheme (N.obj s) (ULift.{u} (Fin 2)))
    (π : D ⟶ B),
    (∀ s, π.app (.op s) = (e s).hom ≫
      projectiveToSpec (N.obj s) (ULift.{u} (Fin 2))) ∧
    (∀ (s t : C) (f : s ⟶ t), D.map f.op ≫ (e s).hom =
      (e t).hom ≫
        (projectiveLineScalingIso
          (c t (sel t).val (sel t).property (sel s).val ((leOfHom f) (sel s).property))).hom ≫
        (projectiveLineTranslationIso
          (a t (sel t).val (sel t).property (sel s).val ((leOfHom f) (sel s).property))).hom ≫
        projectiveCoeffMap (ULift.{u} (Fin 2)) (N.map f).hom.toRingHom) ∧
    π.Equifibered

end SchubertGeometry
