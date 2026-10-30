import OrbitComplexity.FrobeniusSplitting.Cartier.ModuleGluing

/-! # Restriction of local module morphisms -/

open AlgebraicGeometry CategoryTheory Opposite
noncomputable section
universe u

namespace FrobeniusSplitting.OperatorSheaf

/-- Restrict a local module morphism through the Hom sheaf. -/
def restrictModuleHom {X : Scheme.{u}} (M N : X.Modules) {U V : X.Opens}
    (h : V ≤ U) (k : M.over U ⟶ N.over U) : M.over V ⟶ N.over V :=
  SheafOfModules.linearHomObjEquiv M N V
    ((SheafOfModules.linearHom M N).obj.map (homOfLE h).op
      ((SheafOfModules.linearHomObjEquiv M N U).symm k))

/-- Restriction keeps each component map on the corresponding ambient open. -/
theorem restrictModuleHom_apply {X : Scheme.{u}} (M N : X.Modules) {U V : X.Opens}
    (h : V ≤ U) (k : M.over U ⟶ N.over U) (W : Over V)
    (r : M.val.obj (op W.left)) :
    ((restrictModuleHom M N h k).val.app (op W)).hom r =
      (k.val.app (op (Over.mk (W.hom ≫ homOfLE h)))).hom r := by
  rcases W with ⟨W, ⟨⟨⟩⟩, g⟩
  change (((SheafOfModules.linearHomObjEquiv M N V)
      ((SheafOfModules.linearHom M N).obj.map (homOfLE h).op
        ((SheafOfModules.linearHomObjEquiv M N U).symm k))).val.app (op (Over.mk g))).hom r =
    (k.val.app (op (Over.mk (g ≫ homOfLE h)))).hom r
  have ht := SheafOfModules.linearHomObjEquiv_map_app M N (homOfLE h) g
    ((SheafOfModules.linearHomObjEquiv M N U).symm k) r
  have hk := (SheafOfModules.linearHomObjEquiv M N U).apply_symm_apply k
  exact ht.trans (congrArg
    (fun q : M.over U ⟶ N.over U =>
      (q.val.app (op (Over.mk (g ≫ homOfLE h)))).hom r) hk)

/-- Restriction of a section morphism uses the restricted section. -/
theorem restrictModuleHom_localSection {X : Scheme.{u}} (N : X.Modules)
    {U V : X.Opens} (h : V ≤ U) (s : N.val.obj (op U)) :
    restrictModuleHom (SheafOfModules.unit X.ringCatSheaf) N h (localSectionHom N U s) =
      localSectionHom N V ((N.val.map (homOfLE h).op).hom s) := by
  ext W
  have hl := restrictModuleHom_apply (SheafOfModules.unit X.ringCatSheaf) N h
    (localSectionHom N U s) W.unop (1 : Γ(X, W.unop.left))
  have ht := congrArg (N.smul (1 : Γ(X, W.unop.left))).hom
    (N.val.map_comp_apply (homOfLE h).op W.unop.hom.op s)
  exact hl.trans ht

end FrobeniusSplitting.OperatorSheaf
