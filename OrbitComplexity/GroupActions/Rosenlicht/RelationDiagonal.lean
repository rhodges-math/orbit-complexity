import OrbitComplexity.GroupActions.Rosenlicht.RelationStabilizers
import OrbitComplexity.GroupActions.Rosenlicht.RelationProjections

/-!
# RelationDiagonal
-/

open CategoryTheory AlgebraicGeometry CartesianMonoidalCategory

namespace GroupActions.Variety

noncomputable section

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] (H X : GroupActions.Variety K)
variable [GrpObj H.toOver] [ModObj H.toOver X.toOver]
variable [IrreducibleSpace H.scheme] [IrreducibleSpace X.scheme]

/-- The first projection of the diagonal relation point is its defining point. -/
theorem relationDiagonalPoint_first (x : X.points) :
    mapPoints (orbitRelationProjection H X) (relationDiagonalPoint H X x) = x := by
  let s : H.toOver ⟶ (productVariety H X).toOver :=
    lift (𝟙 H.toOver) (toUnit H.toOver ≫ X.pointsEquivOverHom x)
  change mapPoints (orbitRelationProjection H X)
    (mapPoints (s ≫ orbitRelationFactor H X) 1) = x
  rw [← mapPoints_comp, Category.assoc, orbitRelationProjection_fac]
  have hs : s ≫ snd H.toOver X.toOver = toUnit H.toOver ≫ X.pointsEquivOverHom x := by
    simp only [s, lift_snd]
  rw [hs]
  apply X.pointMap_injective
  rw [pointMap_mapPoints]
  change x.val ((toUnit H.toOver).left (H.pointMap 1)) = x.val (IsLocalRing.closedPoint K)
  exact congrArg x.val (Subsingleton.elim _ _)

/-- The second projection of the diagonal relation point is its defining point. -/
theorem relationDiagonalPoint_second (x : X.points) :
    mapPoints (orbitRelationSecond H X) (relationDiagonalPoint H X x) = x := by
  let s : H.toOver ⟶ (productVariety H X).toOver :=
    lift (𝟙 H.toOver) (toUnit H.toOver ≫ X.pointsEquivOverHom x)
  change mapPoints (orbitRelationSecond H X)
    (mapPoints (s ≫ orbitRelationFactor H X) 1) = x
  rw [← mapPoints_comp, Category.assoc, orbitRelationSecond_fac]
  change mapPoints (orbitMorphism H X x) 1 = x
  rw [mapPoints_orbitMorphism, one_smul]

end

end GroupActions.Variety
