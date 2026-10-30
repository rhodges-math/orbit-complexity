import Batteries.Tactic.Lint
import OrbitComplexity.FrobeniusSplitting.Normality.TensorSchemeIso
import Mathlib.CategoryTheory.Limits.Over

/-!
# TensorBaseComp

Fixed-fibre coefficient models and their arithmetic scheme comparisons.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

namespace FrobeniusSplitting

universe u v w

/-- The base projection read from fixed-fibre chart coordinates is a morphism
over the coefficient ring. -/
theorem tensor_base_comp {J : Type v} [Category.{w} J]
    {S R M : Type u} [CommRing S] [CommRing R] [CommRing M]
    [Algebra S R] [Algebra R M] [Algebra S M] [IsScalarTower S R M]
    (G : J ⥤ CommAlgCat.{u} S) (D : J ⥤ CommAlgCat.{u} R)
    (iso : D ≅ fixedFibreDiagram (R := R) (M := M) G)
    (cD : Cocone (D.op ⋙ algSpec (.of R))) (hcD : IsColimit cD)
    (base : cD.pt.left ⟶ Spec (.of M))
    (hbase : ∀ i, (cD.ι.app i).left ≫ base =
      Spec.map (CommRingCat.ofHom
        ((iso.inv.app i.unop).hom.toRingHom.comp
          (Algebra.TensorProduct.includeLeft :
            M →ₐ[M] M ⊗[S] G.obj i.unop).toRingHom))) :
    base ≫ Spec.map (CommRingCat.ofHom (algebraMap R M)) = cD.pt.hom := by
  let hD := isColimitOfPreserves (Over.forget (Spec (.of R))) hcD
  apply hD.hom_ext
  intro i
  change (cD.ι.app i).left ≫
    (base ≫ Spec.map (CommRingCat.ofHom (algebraMap R M))) =
      (cD.ι.app i).left ≫ cD.pt.hom
  rw [← Category.assoc, hbase]
  refine Eq.trans ?_ (Over.w (cD.ι.app i)).symm
  change Spec.map (CommRingCat.ofHom
    ((iso.inv.app i.unop).hom.toRingHom.comp
      (Algebra.TensorProduct.includeLeft :
        M →ₐ[M] M ⊗[S] G.obj i.unop).toRingHom)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R M)) = _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  apply congrArg Spec.map
  apply congrArg CommRingCat.ofHom
  ext r
  exact (iso.inv.app i.unop).hom.commutes r

end FrobeniusSplitting
