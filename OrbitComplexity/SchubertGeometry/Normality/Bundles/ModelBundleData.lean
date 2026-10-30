import OrbitComplexity.SchubertGeometry.Normality.Bundles.ProjectiveModelData
import OrbitComplexity.SchubertGeometry.Normality.Bundles.ProjectiveBundleData

/-! # Projective bundles retaining their arithmetic transition data -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroupActions
open scoped TensorProduct
noncomputable section
universe u
namespace SchubertGeometry

/-- The original parameter values and all transition arrows remain in the glued bundle. -/
def modelBundleSpec {I R K : Type u} [CommRing R] [CommRing K] [Algebra R K]
    (N : {s : Finset I // s.Nonempty} ⥤ CommAlgCat.{u} R)
    (F : {s : Finset I // s.Nonempty} ⥤ CommAlgCat.{u} K)
    (e : ∀ s, K ⊗[R] N.obj s ≃ₐ[K] F.obj s)
    (sel : ∀ s : {s : Finset I // s.Nonempty}, {j : I // j ∈ s.val})
    (c : ∀ (s : {s : Finset I // s.Nonempty}) (j : I) (_ : j ∈ s.val)
      (k : I) (_ : k ∈ s.val), (F.obj s)ˣ)
    (a : ∀ (s : {s : Finset I // s.Nonempty}) (j : I) (_ : j ∈ s.val)
      (k : I) (_ : k ∈ s.val), F.obj s)
    (cG : Cocone (N.op ⋙ algSpec (.of R))) : Prop :=
  let C := {s : Finset I // s.Nonempty}
  ∃ (c₀ : ∀ (s : C) (j : I) (_ : j ∈ s.val) (k : I) (_ : k ∈ s.val), (N.obj s)ˣ)
    (a₀ : ∀ (s : C) (j : I) (_ : j ∈ s.val) (k : I) (_ : k ∈ s.val), N.obj s),
    (∀ s j hj k hk, e s ((1 : K) ⊗ₜ[R] (c₀ s j hj k hk : N.obj s)) = (c s j hj k hk : F.obj s)) ∧
    (∀ s j hj k hk, e s ((1 : K) ⊗ₜ[R] a₀ s j hj k hk) = a s j hj k hk) ∧
    (∀ s j hj k hk l hl,
      c₀ s j hj l hl = c₀ s k hk l hl * c₀ s j hj k hk ∧
      a₀ s j hj l hl = (c₀ s k hk l hl : N.obj s) * a₀ s j hj k hk + a₀ s k hk l hl) ∧
    (∀ (s t : C) (f : s ⟶ t) j hj k hk,
      Units.map (N.map f).hom.toRingHom.toMonoidHom (c₀ s j hj k hk) =
        c₀ t j ((leOfHom f) hj) k ((leOfHom f) hk) ∧
      (N.map f).hom (a₀ s j hj k hk) = a₀ t j ((leOfHom f) hj) k ((leOfHom f) hk)) ∧
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
          (c₀ t (sel t).val (sel t).property (sel s).val ((leOfHom f) (sel s).property))).hom ≫
        (projectiveLineTranslationIso
          (a₀ t (sel t).val (sel t).property (sel s).val ((leOfHom f) (sel s).property))).hom ≫
        projectiveCoeffMap (ULift.{u} (Fin 2)) (N.map f).hom.toRingHom) ∧
    π.Equifibered ∧ projectiveBundleSpec N D π cG


end SchubertGeometry
