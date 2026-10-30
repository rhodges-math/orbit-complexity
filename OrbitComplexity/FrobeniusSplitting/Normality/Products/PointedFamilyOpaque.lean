import OrbitComplexity.FrobeniusSplitting.Normality.Products.PointedFamilyHelpers
import OrbitComplexity.FrobeniusSplitting.Normality.Products.PointedFamilyData

/-! # A pointed factor for a finite model diagram

The coefficient data and auxiliary pointed factor preserve the specified nodes, arrows
and comparisons.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct
namespace FrobeniusSplitting
noncomputable section

/-- A specified finite flat model diagram admits one common coefficient
extension and one shared pointed smooth factor, with every clause of the
independent full diagram target. -/
theorem exists_pointed_family : FrobeniusSplitting.PointedFamilies.pointedFamily := by
  intro J _ _ K B _ _ _ S hS P F _ _ _ _ e he eps
  have (i : J) : Algebra.FinitePresentation K (F.obj i) :=
    Algebra.FinitePresentation.equiv (e i)
  have (i : J) : Algebra.Smooth K (F.obj i) :=
    smooth_of_pointed_product K (F.obj i) B eps
  obtain ⟨R, hSR, H0, ringH0, algH0, eH, eps0, hR, hH0, hC, hprod, hpoint⟩ :=
    exists_pointed_smooth_family S hS (fun i => P.obj i) (fun i => F.obj i) e eps
  let : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
  have : IsScalarTower S R K := Subalgebra.inclusion.isScalarTower_right hSR K
  let : CommRing H0 := ringH0
  let : Algebra R H0 := algH0
  have : Algebra.Smooth R H0 := hH0
  let N := fixedFibreDiagram (R := R) (M := R) P
  let eR (i : J) : K ⊗[R] N.obj i ≃ₐ[K] F.obj i :=
    (Algebra.TensorProduct.cancelBaseChange S R K K (P.obj i)).trans (e i)
  have hNode (i : J) : Algebra.Smooth R (N.obj i) := hC i
  have hProd (i : J) : Algebra.Smooth R (N.obj i ⊗[R] H0) := hprod i
  refine ⟨R, hSR, H0, ringH0, algH0, eH, eps0, hR, hH0, hNode, hProd,
    (fun _ => pointedProductRetraction_section eps0),
    extendedComparison_natural (S := S) (R := R) (K := K) P F e he, hpoint,
    (fun i => productModelEquiv_projection (eR i) eH),
    (fun i => productModelEquiv_retraction (eR i) eH eps eps0 hpoint),
    (fun _ _ f => pointedProductRetraction_natural (N.map f).hom eps0), ?_⟩
  intro i L ringL f
  let : Field L := ringL
  exact pointed_affine_fibre_stalks R (N.obj i) H0 eps0 L f

end
end FrobeniusSplitting
