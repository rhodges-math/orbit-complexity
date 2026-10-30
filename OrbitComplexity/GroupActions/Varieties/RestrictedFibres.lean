import OrbitComplexity.GroupActions.Varieties.FibreIsomorphisms

/-! # Fibres over an open part of the base

Restricting a morphism to the inverse image of an open subset of its base preserves
the topological space and dimension of each fibre over that open subset.
-/

open CategoryTheory AlgebraicGeometry Topology

namespace GroupActions

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency.types false in
private def preimageFibreHomeomorph {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (y : U) :
    ((f ∣_ U) ⁻¹' {y}) ≃ₜ (f ⁻¹' {(y : Y)}) where
  toEquiv :=
    { toFun := fun x ↦ ⟨x.1.1, by
        have hx : (f ∣_ U) x.1 = y := x.2
        change f x.1.1 = (y : Y)
        simpa only [morphismRestrict_base_coe] using congrArg Subtype.val hx⟩
      invFun := fun x ↦ ⟨⟨x.1, by
        change f x.1 ∈ U
        rw [show f x.1 = (y : Y) from x.2]
        exact y.2⟩, Subtype.ext (by
        rw [morphismRestrict_base_coe]
        exact x.2)⟩
      left_inv := fun _ ↦ Subtype.ext (Subtype.ext rfl)
      right_inv := fun _ ↦ Subtype.ext rfl }
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

/-- Restricting the base to an open subset preserves each fibre above that open subset. -/
def fiberRestrictHomeomorph {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (y : U) :
    (f ∣_ U).fiber y ≃ₜ f.fiber (y : Y) :=
  ((f ∣_ U).fiberHomeo y).trans
    ((preimageFibreHomeomorph f U y).trans (f.fiberHomeo (y : Y)).symm)

/-- Restricting a morphism over an open subset preserves the dimensions of its fibres. -/
theorem fibre_dim_restrict {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (y : U) :
    topologicalKrullDim ((f ∣_ U).fiber y) = topologicalKrullDim (f.fiber (y : Y)) :=
  (fiberRestrictHomeomorph f U y).isHomeomorph.topologicalKrullDim_eq

end

end GroupActions
