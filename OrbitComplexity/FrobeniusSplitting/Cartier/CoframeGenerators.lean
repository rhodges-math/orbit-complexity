import OrbitComplexity.FrobeniusSplitting.Cartier.CoframeOverlaps
import OrbitComplexity.FrobeniusSplitting.Cartier.HomRestriction
import Batteries.Tactic.Lint

/-!
# Generators of coframes on open subsets

An inverse coframe is determined by its value on the unit section.
These generators commute with restriction to smaller open subsets.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Opposite
open AlgebraicGeometry.Scheme.Modules

namespace FrobeniusSplitting.OperatorSheaf

private abbrev unitModule (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

/-- The section of a line given by the inverse of a coframe on an open subset. -/
def coframeGenerator {X : Scheme.{u}} (L : X.Modules) (U : X.Opens)
    (E : L.over U ≅ (unitModule X).over U) : L.val.obj (op U) :=
  ((E.inv.val.app (op (Over.mk (𝟙 U)))).hom) (1 : Γ(X, U))

private theorem unit_hom_eq_of_top {X : Scheme.{u}} (L : X.Modules) (U : X.Opens)
    (f g : (unitModule X).over U ⟶ L.over U)
    (h : ((f.val.app (op (Over.mk (𝟙 U)))).hom) (1 : Γ(X, U)) =
      ((g.val.app (op (Over.mk (𝟙 U)))).hom) (1 : Γ(X, U))) : f = g := by
  apply (L.over U).unitHomEquiv.injective
  apply Subtype.ext
  funext V
  let hV : V.unop ⟶ Over.mk (𝟙 U) :=
    Over.homMk V.unop.hom (by simp)
  have hf := ((L.over U).unitHomEquiv f).property hV.op
  have hg := ((L.over U).unitHomEquiv g).property hV.op
  change (f.val.app V).hom (1 : Γ(X, V.unop.left)) =
    (g.val.app V).hom (1 : Γ(X, V.unop.left))
  exact hf.symm.trans ((congrArg (fun z => (L.over U).val.map hV.op z) h).trans hg)

/-- Two coframes on an open subset agree when their generators agree. -/
theorem coframe_eq_of_generator {X : Scheme.{u}} (L : X.Modules) (U : X.Opens)
    (E F : L.over U ≅ (unitModule X).over U)
    (h : coframeGenerator L U E = coframeGenerator L U F) : E = F := by
  have he : E.inv = F.inv := unit_hom_eq_of_top L U E.inv F.inv h
  exact Iso.ext_inv he

/-- Restricting a coframe restricts its generator section. -/
theorem coframeGenerator_restrict {X : Scheme.{u}} (L : X.Modules)
    {U V : X.Opens} (h : V ≤ U)
    (E : L.over U ≅ (unitModule X).over U) :
    coframeGenerator L V (restrictModuleIso L (unitModule X) h E) =
      (L.val.map (homOfLE h).op).hom (coframeGenerator L U E) := by
  change ((E.inv.val.app (op (Over.mk (homOfLE h)))).hom) (1 : Γ(X, V)) =
    (L.val.map (homOfLE h).op).hom
      (((E.inv.val.app (op (Over.mk (𝟙 U)))).hom) (1 : Γ(X, U)))
  let hV : Over.mk (homOfLE h) ⟶ Over.mk (𝟙 U) :=
    Over.homMk (homOfLE h) (by simp)
  exact (((L.over U).unitHomEquiv E.inv).property hV.op).symm

end FrobeniusSplitting.OperatorSheaf
