import OrbitComplexity.SchubertGeometry.Deodhar.RankOneRoots
import OrbitComplexity.SchubertGeometry.Cells.CellChart
import OrbitComplexity.GroupActions.Varieties.RootProductPoints

/-! # Cell projections for increasing simple extensions

Ordered multiplication separates the preceding inversion subgroup from the added root line.
The first factor gives a morphism from the extended cell to the preceding cell.
-/

open CategoryTheory AlgebraicGeometry ReductiveGroups
open scoped TensorProduct
namespace SchubertGeometry
noncomputable section
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K) (w : G.weylGroup) (i : G.rootBase.support)
  (hw : G.rootBase.IsPos (G.rootSystem.weylGroupToPerm w i))

/-- The product of the preceding inversion subgroup and its added root subgroup. -/
abbrev rankOneProductVariety : GroupActions.Variety K :=
  GroupActions.rootProductVariety G (leftRootInversionIndices G.rootBase w)
    (rankOneRootSet G w i) (LeftRootInversionIndices.isPositiveRootClosed G.rootBase w)
    (rankOneRoot_closed G w i hw)

/-- Root multiplication identifies the product with the extended Schubert cell. -/
def rankOneCellIso : (rankOneProductVariety G w i hw).toOver ≅
    (schubertCell G (w * RootPairing.weylGroup.ofIdx G.rootSystem i)).toOver :=
  GroupActions.rootProductIso G _ _ _
    (LeftRootInversionIndices.isPositiveRootClosed G.rootBase _)
    (LeftRootInversionIndices.isPositiveRootClosed G.rootBase w)
    (rankOneRoot_closed G w i hw) (rankOneRoot_union G w i hw)
    (rankOneRoot_disjoint G w i) ≪≫ schubertCellIso G _

/-- Projection from a rank-one product to its preceding inversion subgroup. -/
def rankOneFirst : (rankOneProductVariety G w i hw).toOver ⟶
    (schubertUnipotent G w).toOver :=
  (algSpec (CommRingCat.of K)).map (CommAlgCat.ofHom
    (Algebra.TensorProduct.includeLeft : G.rootSubsetAlgebra
      (leftRootInversionIndices G.rootBase w)
      (LeftRootInversionIndices.isPositiveRootClosed G.rootBase w) →ₐ[K]
      G.rootSubsetAlgebra (leftRootInversionIndices G.rootBase w)
        (LeftRootInversionIndices.isPositiveRootClosed G.rootBase w) ⊗[K]
        G.rootSubsetAlgebra (rankOneRootSet G w i) (rankOneRoot_closed G w i hw))).op

/-- The cell projection removes the final increasing simple step. -/
def rankOneCellProjection :
    (schubertCell G (w * RootPairing.weylGroup.ofIdx G.rootSystem i)).toOver ⟶
      (schubertCell G w).toOver :=
  (rankOneCellIso G w i hw).inv ≫ rankOneFirst G w i hw ≫ (schubertCellIso G w).hom

/-- Under the product chart, the cell projection is first-factor projection. -/
theorem rankOneCellProjection_comp :
    (rankOneCellIso G w i hw).hom ≫ rankOneCellProjection G w i hw =
      rankOneFirst G w i hw ≫ (schubertCellIso G w).hom := by
  simp only [rankOneCellProjection, Iso.hom_inv_id_assoc]


end
end SchubertGeometry
