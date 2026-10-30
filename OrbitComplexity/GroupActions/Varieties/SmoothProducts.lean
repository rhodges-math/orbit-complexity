import OrbitComplexity.GroupActions.Varieties.Noetherian
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.GeometricallyReduced

/-! # Products with a smooth variety

The product of a smooth variety with a reduced variety is reduced. Smoothness gives flat,
geometrically reduced fibres, and the second factor is locally Noetherian.

## Main definitions

* `GroupActions.Variety.smoothProductVariety`: the product variety with a smooth first factor.
-/

open CategoryTheory AlgebraicGeometry MonoidalCategory

namespace GroupActions.Variety

noncomputable section

universe u

variable {K : Type u} [Field K]

/-- The product with a smooth first factor is reduced and of finite type. -/
abbrev smoothProductVariety (A B : GroupActions.Variety K) [Smooth A.toSpec] :
    GroupActions.Variety K where
  scheme := (A.toOver ⊗ B.toOver).left
  toSpec := (A.toOver ⊗ B.toOver).hom
  reduced := by
    change IsReduced (Limits.pullback A.toSpec B.toSpec)
    infer_instance
  separated := by
    change IsSeparated (Limits.pullback.fst A.toSpec B.toSpec ≫ A.toSpec)
    infer_instance
  locallyOfFiniteType := by
    change LocallyOfFiniteType (Limits.pullback.fst A.toSpec B.toSpec ≫ A.toSpec)
    infer_instance
  quasiCompact := by
    change QuasiCompact (Limits.pullback.fst A.toSpec B.toSpec ≫ A.toSpec)
    infer_instance

end

end GroupActions.Variety
