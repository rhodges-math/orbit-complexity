import OrbitComplexity.FrobeniusSplitting.Cartier.ModuleGluing
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Batteries.Tactic.Lint

/-!
# Gluing coframes of a line module

Compatible local coframes and their inverses give an isomorphism of the
original module with the structure module.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Opposite
open TopologicalSpace.Opens

namespace FrobeniusSplitting.OperatorSheaf

private abbrev unitModule (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

private theorem hom_ext_on_cover {X : Scheme.{u}} {I : Type u}
    (U : I → X.Opens) (hcover : iSup U = ⊤) (M N : X.Modules)
    (f g : M ⟶ N) (h : ∀ i, f.over (U i) = g.over (U i)) : f = g := by
  apply Scheme.Modules.hom_ext
  intro V
  ext m
  let W : I → X.Opens := fun i => V ⊓ U i
  have hW : V ≤ iSup W := by
    dsimp [W]
    rw [← inf_iSup_eq, hcover, inf_top_eq]
  refine TopCat.Sheaf.eq_of_locally_eq'
    ((SheafOfModules.toSheaf X.ringCatSheaf).obj N) W V
    (fun i => infLELeft V (U i)) hW _ _ ?_
  intro i
  have hf : f.app (W i) (M.presheaf.map (infLELeft V (U i)).op m) =
      N.presheaf.map (infLELeft V (U i)).op (f.app V m) :=
    ConcreteCategory.congr_hom (f.mapPresheaf.naturality (infLELeft V (U i)).op) m
  have hg : g.app (W i) (M.presheaf.map (infLELeft V (U i)).op m) =
      N.presheaf.map (infLELeft V (U i)).op (g.app V m) :=
    ConcreteCategory.congr_hom (g.mapPresheaf.naturality (infLELeft V (U i)).op) m
  have hl : f.app (W i) (M.presheaf.map (infLELeft V (U i)).op m) =
      g.app (W i) (M.presheaf.map (infLELeft V (U i)).op m) := by
    exact congrArg
      (fun k : M.over (U i) ⟶ N.over (U i) =>
        (k.val.app (op (Over.mk (infLERight V (U i))))).hom
          (M.presheaf.map (infLELeft V (U i)).op m))
      (h i)
  exact hf.symm.trans (hl.trans hg)

/-- Compatible coframes and inverses on an open cover glue on the same module. -/
theorem glueModuleCoframes {X : Scheme.{u}} {I : Type u} (U : I → X.Opens)
    (hcover : iSup U = ⊤) (L : X.Modules)
    (E : ∀ i, L.over (U i) ≅ (unitModule X).over (U i))
    (hHom : TopCat.Presheaf.IsCompatible
      (SheafOfModules.linearHom L (unitModule X)).obj U
      (fun i => (SheafOfModules.linearHomObjEquiv L (unitModule X) (U i)).symm
        (E i).hom))
    (hInv : TopCat.Presheaf.IsCompatible
      (SheafOfModules.linearHom (unitModule X) L).obj U
      (fun i => (SheafOfModules.linearHomObjEquiv (unitModule X) L (U i)).symm
        (E i).inv)) :
    ∃ F : L ≅ unitModule X, ∀ i,
      F.hom.over (U i) = (E i).hom ∧ F.inv.over (U i) = (E i).inv := by
  obtain ⟨f, hf⟩ := glueModuleMorphisms U hcover L (unitModule X)
    (fun i => (E i).hom) hHom
  obtain ⟨g, hg⟩ := glueModuleMorphisms U hcover (unitModule X) L
    (fun i => (E i).inv) hInv
  have hfg : f ≫ g = 𝟙 L := by
    apply hom_ext_on_cover U hcover L L
    intro i
    change f.over (U i) ≫ g.over (U i) = 𝟙 (L.over (U i))
    rw [hf i, hg i]
    exact (E i).hom_inv_id
  have hgf : g ≫ f = 𝟙 (unitModule X) := by
    apply hom_ext_on_cover U hcover (unitModule X) (unitModule X)
    intro i
    change g.over (U i) ≫ f.over (U i) = 𝟙 ((unitModule X).over (U i))
    rw [hg i, hf i]
    exact (E i).inv_hom_id
  exact ⟨⟨f, g, hfg, hgf⟩, fun i => ⟨hf i, hg i⟩⟩

end FrobeniusSplitting.OperatorSheaf
