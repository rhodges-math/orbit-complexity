import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap

/-!
# Pullback on function fields

A dominant morphism sends the generic point of an irreducible scheme to the generic point.
Its map on stalks therefore gives pullback on function fields. For an open immersion this
pullback is an isomorphism.

## Main definitions

* `functionFieldMap`: the pullback homomorphism of a dominant morphism.
* `openFunctionFieldEquiv`: the function-field isomorphism of a dominant open immersion.

## Main results

* `map_genericPoint`: dominant morphisms preserve generic points.
* `functionFieldMap_comp`: pullbacks on function fields compose contravariantly.
* `functionFieldMap_germ`: pullback of a regular function agrees with pullback on sections.
-/

namespace GroupActions

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} [IrreducibleSpace X] [IrreducibleSpace Y]

/-- A dominant morphism between irreducible schemes sends generic point to generic point. -/
theorem map_genericPoint (f : X ⟶ Y) [IsDominant f] :
    f (genericPoint X) = genericPoint Y := by
  apply ((genericPoint_spec Y).eq _).symm
  simpa only [Set.image_univ, f.denseRange.closure_range] using
    (genericPoint_spec X).image f.continuous

/-- The pullback on function fields induced by a dominant morphism of irreducible schemes. -/
def functionFieldMap (f : X ⟶ Y) [IsDominant f] :
    Y.functionField →+* X.functionField :=
  ((Y.presheaf.stalkCongr (.of_eq (map_genericPoint f).symm)).hom ≫
    f.stalkMap (genericPoint X)).hom

omit [IrreducibleSpace X] [IrreducibleSpace Y] in
private lemma stalkMap_comp_congr {Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (x : X) (y : Y) (z : Z) (hxy : f x = y) (hyz : g y = z) :
    (Z.presheaf.stalkCongr (.of_eq (hxy ▸ hyz).symm)).hom ≫
      (f ≫ g).stalkMap x =
    (Z.presheaf.stalkCongr (.of_eq hyz.symm)).hom ≫ g.stalkMap y ≫
      (Y.presheaf.stalkCongr (.of_eq hxy.symm)).hom ≫ f.stalkMap x := by
  subst y
  subst z
  change Z.presheaf.stalkSpecializes (specializes_refl (g (f x))) ≫
      (f ≫ g).stalkMap x =
    Z.presheaf.stalkSpecializes (specializes_refl (g (f x))) ≫ g.stalkMap (f x) ≫
      Y.presheaf.stalkSpecializes (specializes_refl (f x)) ≫ f.stalkMap x
  simp only [TopCat.Presheaf.stalkSpecializes_refl, Category.id_comp,
    Scheme.Hom.stalkMap_comp]

/-- Pullback on function fields sends composition of dominant morphisms to composition
in the reverse order. -/
theorem functionFieldMap_comp {Z : Scheme.{u}} [IrreducibleSpace Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [IsDominant f] [IsDominant g] :
    functionFieldMap (f ≫ g) = (functionFieldMap f).comp (functionFieldMap g) := by
  change (_ ≫ (f ≫ g).stalkMap (genericPoint X)).hom =
    ((_ ≫ g.stalkMap (genericPoint Y)) ≫
      (_ ≫ f.stalkMap (genericPoint X))).hom
  congr 1
  simpa only [Category.assoc] using
    stalkMap_comp_congr f g (genericPoint X) (genericPoint Y) (genericPoint Z)
      (map_genericPoint f) (map_genericPoint g)

/-- The identity morphism induces the identity on the function field. -/
theorem functionFieldMap_id : functionFieldMap (𝟙 X) = RingHom.id X.functionField := by
  unfold functionFieldMap
  change (X.presheaf.stalkSpecializes (specializes_refl (genericPoint X)) ≫
    (𝟙 X : X ⟶ X).stalkMap (genericPoint X)).hom = _
  simp only [Scheme.Hom.stalkMap_id, TopCat.Presheaf.stalkSpecializes_refl,
    Category.id_comp, CommRingCat.hom_id]

omit [IrreducibleSpace X] [IrreducibleSpace Y] in
private lemma stalkMap_germ_congr (f : X ⟶ Y) (x : X) (y : Y) (hxy : f x = y)
    (U : Y.Opens) (hy : y ∈ U) :
    Y.presheaf.germ U y hy ≫ (Y.presheaf.stalkCongr (.of_eq hxy.symm)).hom ≫
      f.stalkMap x =
    f.app U ≫ X.presheaf.germ (f ⁻¹ᵁ U) x (by
      change f x ∈ U
      rw [hxy]
      exact hy) := by
  subst y
  change Y.presheaf.germ U (f x) hy ≫
      Y.presheaf.stalkSpecializes (specializes_refl (f x)) ≫ f.stalkMap x = _
  simpa only [TopCat.Presheaf.stalkSpecializes_refl, Category.id_comp] using
    f.germ_stalkMap U x hy

/-- Pullback on function fields sends the germ of a regular function to the germ
of its pullback on sections. -/
theorem functionFieldMap_germ (f : X ⟶ Y) [IsDominant f] (U : Y.Opens) [Nonempty U]
    [Nonempty (f ⁻¹ᵁ U)] (s : Γ(Y, U)) :
    functionFieldMap f (Y.germToFunctionField U s) =
      X.germToFunctionField (f ⁻¹ᵁ U) (f.app U s) := by
  have hy : genericPoint Y ∈ U :=
    ((genericPoint_spec Y).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›)
  exact congrArg (fun h : Γ(Y, U) ⟶ X.functionField ↦ h s)
    (stalkMap_germ_congr f (genericPoint X) (genericPoint Y) (map_genericPoint f) U hy)

/-- A dominant open immersion induces an isomorphism on function fields. -/
def openFunctionFieldEquiv (f : X ⟶ Y) [IsDominant f] [IsOpenImmersion f] :
    Y.functionField ≃+* X.functionField :=
  (asIso ((Y.presheaf.stalkCongr (.of_eq (map_genericPoint f).symm)).hom ≫
    f.stalkMap (genericPoint X))).commRingCatIsoToRingEquiv

end

end GroupActions
