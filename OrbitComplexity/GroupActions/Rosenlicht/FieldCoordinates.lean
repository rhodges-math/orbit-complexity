import OrbitComplexity.GroupActions.Rosenlicht.FunctionFields

/-!
# Regular coordinates in function fields

Pulling back a global regular function agrees with pulling back its function-field
germ. For affine spectra, the coordinate-ring map is the germ of the canonical
global section.
-/

open CategoryTheory AlgebraicGeometry

namespace GroupActions

noncomputable section

universe u

private instance top_nonempty {X : Scheme.{u}} [Nonempty X] : Nonempty (⊤ : X.Opens) :=
  ⟨⟨Classical.choice inferInstance, trivial⟩⟩

/-- Equal dominant morphisms induce the same function-field pullback. -/
theorem functionFieldMap_congr {X Y : Scheme.{u}}
    [IrreducibleSpace X] [IrreducibleSpace Y] (f g : X ⟶ Y)
    [IsDominant f] [IsDominant g] (h : f = g) : functionFieldMap f = functionFieldMap g := by
  subst g
  rfl

/-- Function-field pullback agrees with pullback of global sections. -/
theorem functionFieldMap_appTop {X Y : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) [IsDominant f] (s : Γ(Y, ⊤)) :
    functionFieldMap f (Y.germToFunctionField ⊤ s) =
      X.germToFunctionField ⊤ (f.appTop s) := by
  have : Nonempty (f ⁻¹ᵁ (⊤ : Y.Opens)) := ⟨⟨genericPoint X, trivial⟩⟩
  calc
    _ = X.germToFunctionField (f ⁻¹ᵁ ⊤) (f.app ⊤ s) := functionFieldMap_germ f ⊤ s
    _ = _ := by
      change (f.app ⊤ ≫ X.germToFunctionField (f ⁻¹ᵁ ⊤)) s =
        (f.appTop ≫ X.germToFunctionField ⊤) s
      simp only [Scheme.Hom.appTop]
      rfl

/-- An affine coordinate enters the function field as the germ of its global section. -/
theorem affineField_algebraMap (R : CommRingCat.{u}) [IsDomain R] (r : R) :
    algebraMap R (Spec R).functionField r =
      (Spec R).germToFunctionField ⊤ ((Scheme.ΓSpecIso R).inv r) := by
  rfl

/-- The canonical affine-spectrum isomorphism preserves regular function-field coordinates. -/
theorem affineField_isoSpec (X : Scheme.{u}) [IsIntegral X] [IsAffine X] (s : Γ(X, ⊤)) :
    functionFieldMap X.isoSpec.hom
      (algebraMap Γ(X, ⊤) (Spec Γ(X, ⊤)).functionField s) = X.germToFunctionField ⊤ s := by
  rw [affineField_algebraMap, functionFieldMap_appTop]
  change X.germToFunctionField ⊤ (X.toSpecΓ.appTop ((Scheme.ΓSpecIso Γ(X, ⊤)).inv s)) = _
  rw [Scheme.toSpecΓ_appTop]
  simp only [← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply]

end

end GroupActions
