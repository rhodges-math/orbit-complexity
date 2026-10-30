import OrbitComplexity.SchubertGeometry.Deodhar.CellTrivialization
import OrbitComplexity.GroupActions.Varieties.AffineTensorProduct

/-! # Product charts for increasing cell projections

The affine additive chart is the categorical product of the preceding cell and Ga.
Under this isomorphism the increasing-cell projection is the first product projection.
-/

open CategoryTheory AlgebraicGeometry ReductiveGroups CartesianMonoidalCategory MonoidalCategory
open scoped TensorProduct
namespace SchubertGeometry
noncomputable section
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K) (w : G.weylGroup) (i : G.rootBase.support)
  (hw : G.rootBase.IsPos (G.rootSystem.weylGroupToPerm w i))

private abbrev cellAlgebra := G.rootSubsetAlgebra (leftRootInversionIndices G.rootBase w)
  (LeftRootInversionIndices.isPositiveRootClosed G.rootBase w)
private theorem tensorDomain : IsDomain (cellAlgebra G w ⊗[K] SymmetricAlgebra K K) :=
  GroupActions.isDomain_tensorProduct
attribute [local instance] tensorDomain
private theorem tensorFinite :
    Algebra.FiniteType K (cellAlgebra G w ⊗[K] SymmetricAlgebra K K) :=
  Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType K (cellAlgebra G w))
    (inferInstance : Algebra.FiniteType (cellAlgebra G w)
      (cellAlgebra G w ⊗[K] SymmetricAlgebra K K))
attribute [local instance] tensorFinite

/-- The affine additive-product variety is the product of its two factors over the field. -/
def rankOneGaTensorIso : (rankOneGaProductVariety G w).toOver ≅
    (schubertUnipotent G w).toOver ⊗ (GroupActions.additiveVariety K).toOver :=
  GroupActions.affineTensorIso K (cellAlgebra G w) (SymmetricAlgebra K K)

/-- The tensor-product comparison preserves the preceding root-subgroup projection. -/
theorem rankOneGaTensorIso_fst : (rankOneGaTensorIso G w).hom ≫
    fst (schubertUnipotent G w).toOver (GroupActions.additiveVariety K).toOver =
      rankOneGaFirst G w :=
  GroupActions.affineTensorIso_fst K (cellAlgebra G w) (SymmetricAlgebra K K)

/-- The tensor-product comparison preserves the two rational coordinate points. -/
theorem rankOneGaTensorIso_points (x : (rankOneGaProductVariety G w).points) :
    (rankOneGaProductVariety G w).pointsEquivOverHom x ≫ (rankOneGaTensorIso G w).hom =
      lift ((schubertUnipotent G w).pointsEquivOverHom
        (rankOneGaProductPointsEquiv G w x).1)
        ((GroupActions.additiveVariety K).pointsEquivOverHom
          (rankOneGaProductPointsEquiv G w x).2) :=
  GroupActions.affineTensorIso_points K (cellAlgebra G w) (SymmetricAlgebra K K) x

/-- The inversion subgroup times Ga is the increasing simple-extension cell. -/
def rankOneTensorCellIso :
    (schubertUnipotent G w).toOver ⊗ (GroupActions.additiveVariety K).toOver ≅
      (schubertCell G (w * RootPairing.weylGroup.ofIdx G.rootSystem i)).toOver :=
  (rankOneGaTensorIso G w).symm ≪≫ rankOneGaCellIso G w i hw

private theorem tensorCellIso_hom : (rankOneTensorCellIso G w i hw).hom =
    (rankOneGaTensorIso G w).inv ≫ (rankOneGaCellIso G w i hw).hom := rfl

/-- The increasing-cell projection is first-factor projection in inversion-root coordinates. -/
theorem rankOneTensorCellIso_projection :
    (rankOneTensorCellIso G w i hw).hom ≫ rankOneCellProjection G w i hw =
      fst (schubertUnipotent G w).toOver (GroupActions.additiveVariety K).toOver ≫
        (schubertCellIso G w).hom := by
  rw [tensorCellIso_hom, Category.assoc, rankOneGaCellIso_projection]
  simp only [← rankOneGaTensorIso_fst, Category.assoc, Iso.inv_hom_id_assoc]

/-- The preceding Schubert cell times Ga is its increasing simple-extension cell. -/
def rankOneCellProductIso :
    (schubertCell G w).toOver ⊗ (GroupActions.additiveVariety K).toOver ≅
      (schubertCell G (w * RootPairing.weylGroup.ofIdx G.rootSystem i)).toOver :=
  tensorIso (schubertCellIso G w).symm (Iso.refl _) ≪≫ rankOneTensorCellIso G w i hw

private theorem cellProductIso_hom : (rankOneCellProductIso G w i hw).hom =
    ((schubertCellIso G w).inv ⊗ₘ 𝟙 (GroupActions.additiveVariety K).toOver) ≫
      (rankOneTensorCellIso G w i hw).hom := rfl

/-- The product-cell isomorphism identifies the cell projection with the first projection. -/
theorem rankOneCellProductIso_projection :
    (rankOneCellProductIso G w i hw).hom ≫ rankOneCellProjection G w i hw =
      fst (schubertCell G w).toOver (GroupActions.additiveVariety K).toOver := by
  rw [cellProductIso_hom, Category.assoc, rankOneTensorCellIso_projection,
    tensorHom_fst_assoc, Iso.inv_hom_id, Category.comp_id]

end
end SchubertGeometry
