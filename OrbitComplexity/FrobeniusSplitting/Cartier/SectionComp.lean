import OrbitComplexity.FrobeniusSplitting.Cartier.ModuleGluing

/-! # Components of scalar-section frame composites -/

open AlgebraicGeometry CategoryTheory Opposite
noncomputable section
universe u

namespace FrobeniusSplitting.OperatorSheaf

/-- Compose a local coefficient morphism with the scalar map of a local section. -/
theorem localSection_comp_apply {X : Scheme.{u}} {M N : X.Modules} {U : X.Opens}
    (a : M.over U ⟶ (SheafOfModules.unit X.ringCatSheaf).over U)
    (s : N.val.obj (op U)) (V : Over U) (r : M.val.obj (op V.left)) :
    ((a ≫ localSectionHom (X := X) N U s).val.app (op V)).hom r =
      (N.smul (X := X) (U := V.left)
        (((a.val.app (op V)).hom r) : Γ(X, V.left))).hom
          ((N.val.map V.hom.op).hom s) := by
  rfl

end FrobeniusSplitting.OperatorSheaf
