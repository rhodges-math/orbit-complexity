import OrbitComplexity.FrobeniusSplitting.Cartier.CoframeGluing
import OrbitComplexity.FrobeniusSplitting.Cartier.HomRestriction
import Batteries.Tactic.Lint

/-! # Gluing coframes from overlap equalities

Restriction of a module isomorphism retains both inverse identities.
Equality of the restricted coframes therefore gives compatibility of both
module maps required to glue one coframe.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Opposite

namespace FrobeniusSplitting.OperatorSheaf

private abbrev unitModule (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

/-- Restrict an isomorphism of local module sheaves to a smaller ambient open. -/
def restrictModuleIso {X : Scheme.{u}} (M N : X.Modules) {U V : X.Opens}
    (h : V ≤ U) (E : M.over U ≅ N.over U) : M.over V ≅ N.over V :=
  ((SheafOfModules.overFunctorMap X.ringCatSheaf (homOfLE h)).app M).symm ≪≫
    (SheafOfModules.overMap X.ringCatSheaf (homOfLE h)).mapIso E ≪≫
      (SheafOfModules.overFunctorMap X.ringCatSheaf (homOfLE h)).app N

private theorem restrictModuleIso_hom {X : Scheme.{u}} (M N : X.Modules)
    {U V : X.Opens} (h : V ≤ U) (E : M.over U ≅ N.over U) :
    (restrictModuleIso M N h E).hom = restrictModuleHom M N h E.hom := by
  ext W r
  change ((E.hom.val.app (op (Over.mk (W.unop.hom ≫ homOfLE h)))).hom r) =
    ((restrictModuleHom M N h E.hom).val.app W).hom r
  exact (restrictModuleHom_apply M N h E.hom W.unop r).symm

private theorem restrictModuleIso_inv {X : Scheme.{u}} (M N : X.Modules)
    {U V : X.Opens} (h : V ≤ U) (E : M.over U ≅ N.over U) :
    (restrictModuleIso M N h E).inv = restrictModuleHom N M h E.inv := by
  ext W r
  change ((E.inv.val.app (op (Over.mk (W.unop.hom ≫ homOfLE h)))).hom r) =
    ((restrictModuleHom N M h E.inv).val.app W).hom r
  exact (restrictModuleHom_apply N M h E.inv W.unop r).symm

/-- Equal restricted coframe isomorphisms glue with their specified inverses. -/
theorem glueCoframes_of_overlap_eq {X : Scheme.{u}} {I : Type u}
    (U : I → X.Opens) (hcover : iSup U = ⊤) (L : X.Modules)
    (E : ∀ i, L.over (U i) ≅ (unitModule X).over (U i))
    (hover : ∀ i j,
      restrictModuleIso L (unitModule X) (inf_le_left : U i ⊓ U j ≤ U i) (E i) =
        restrictModuleIso L (unitModule X) (inf_le_right : U i ⊓ U j ≤ U j) (E j)) :
    ∃ F : L ≅ unitModule X, ∀ i,
      F.hom.over (U i) = (E i).hom ∧ F.inv.over (U i) = (E i).inv := by
  apply glueModuleCoframes U hcover L E
  · intro i j
    apply (SheafOfModules.linearHomObjEquiv L (unitModule X) (U i ⊓ U j)).injective
    change restrictModuleHom L (unitModule X) inf_le_left (E i).hom =
      restrictModuleHom L (unitModule X) inf_le_right (E j).hom
    rw [← restrictModuleIso_hom, ← restrictModuleIso_hom]
    exact congrArg Iso.hom (hover i j)
  · intro i j
    apply (SheafOfModules.linearHomObjEquiv (unitModule X) L (U i ⊓ U j)).injective
    change restrictModuleHom (unitModule X) L inf_le_left (E i).inv =
      restrictModuleHom (unitModule X) L inf_le_right (E j).inv
    rw [← restrictModuleIso_inv, ← restrictModuleIso_inv]
    exact congrArg Iso.inv (hover i j)

end FrobeniusSplitting.OperatorSheaf
