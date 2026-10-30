import OrbitComplexity.FrobeniusSplitting.Cartier.ModuleGluing

/-! # Detecting scalar-section frame isomorphisms -/

open AlgebraicGeometry CategoryTheory Opposite
noncomputable section
universe u v

namespace FrobeniusSplitting.OperatorSheaf

private theorem isIsoOfComponents {D : Type u} [Category.{v} D]
    {J : GrothendieckTopology D} {R : Sheaf J RingCat.{u}}
    {M N : SheafOfModules.{u} R} (t : M ⟶ N)
    (h : ∀ V, IsIso (t.val.app V)) : IsIso t := by
  let e : M.val ≅ N.val := PresheafOfModules.isoMk
    (fun V => @asIso _ _ _ _ (t.val.app V) (h V)) (fun {_ _} f => t.val.naturality f)
  have he : e.hom = t.val := by ext V; rfl
  let q : M ≅ N := (SheafOfModules.fullyFaithfulForget R).preimageIso e
  have hq : q.hom = t :=
    (SheafOfModules.fullyFaithfulForget R).map_injective (X := M) (Y := N)
      (((SheafOfModules.fullyFaithfulForget R).map_preimage (X := M) (Y := N) e.hom).trans he)
  exact hq ▸ q.isIso_hom

/-- A section is a local frame if multiplication by it is bijective on every smaller open. -/
theorem localSectionHom_isIso {X : Scheme.{u}} (N : X.Modules) (U : X.Opens)
    (s : N.val.obj (op U))
    (h : ∀ V : Over U, Function.Bijective (fun r : Γ(X, V.left) =>
      (N.smul (X := X) (U := V.left) r).hom ((N.val.map V.hom.op).hom s))) :
    IsIso (localSectionHom N U s) := by
  apply isIsoOfComponents
  intro V
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  exact h V.unop

end FrobeniusSplitting.OperatorSheaf
