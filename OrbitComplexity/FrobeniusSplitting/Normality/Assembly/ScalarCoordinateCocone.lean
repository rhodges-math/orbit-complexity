import OrbitComplexity.FrobeniusSplitting.Normality.Coordinates.FixedCoordinateCocone
import OrbitComplexity.FrobeniusSplitting.Normality.Models.FixedDiagramIsos
import Batteries.Tactic.Lint

/-!
# Coordinate cocones through two coefficient extensions

The nested tensor extension of a fixed intersection diagram has the same
geometric base-extension point as its single tensor extension. Natural
coefficient comparisons also determine the map between the two cocone points.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

noncomputable section

universe u v w

namespace FrobeniusSplitting

private theorem reindex_coordinates {I C D : Type*} [Category I] [Category C] [Category D]
    (L : Cᵒᵖ ⥤ D) {P N A : I ⥤ C} (e : P ≅ N)
    {H : Sort*} (a : H → Cocone (A.op ⋙ L))
    (h : ∃ z : H, ∃ d : N ≅ A, ∃ c : Cocone (N.op ⋙ L),
      ∃ hp : c.pt = (a z).pt, Nonempty (IsColimit c) ∧
        ∀ j : Iᵒᵖ, c.ι.app j ≫ eqToHom hp =
          L.map (d.inv.app j.unop).op ≫ (a z).ι.app j) :
    ∃ z : H, ∃ d : P ≅ A, ∃ c : Cocone (P.op ⋙ L),
      ∃ hp : c.pt = (a z).pt, Nonempty (IsColimit c) ∧
        ∀ j : Iᵒᵖ, c.ι.app j ≫ eqToHom hp =
          L.map (d.inv.app j.unop).op ≫ (a z).ι.app j := by
  obtain ⟨z, d, c, hp, ⟨hc⟩, hleg⟩ := h
  let alpha : P.op ⋙ L ≅ N.op ⋙ L :=
    Functor.isoWhiskerRight (NatIso.op e.symm) L
  have hc' : IsColimit ((Cocone.precompose alpha.hom).obj c) :=
    (IsColimit.precomposeHomEquiv alpha c).symm hc
  refine ⟨z, e ≪≫ d, (Cocone.precompose alpha.hom).obj c, hp, ⟨hc'⟩, ?_⟩
  intro j
  change (L.map (e.inv.app j.unop).op ≫ c.ι.app j) ≫ eqToHom hp =
    L.map ((d.inv.app j.unop ≫ e.inv.app j.unop).op) ≫ (a z).ι.app j
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun f => L.map (e.inv.app j.unop).op ≫ f) (hleg j)).trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (fun f => f ≫ (a z).ι.app j)
          (L.map_comp (e.inv.app j.unop).op (d.inv.app j.unop).op).symm)))

private def comparisonCocone {I C : Type*} [Category I] [Category C]
    {F G : I ⥤ C} (v : F ⟶ G) (c : Cocone G) : Cocone F :=
  Cocone.mk c.pt (v ≫ c.ι)

private def descendComparison {I C : Type*} [Category I] [Category C]
    {F G : I ⥤ C} (v : F ⟶ G) (cN : Cocone G) (cF : Cocone F)
    (hcF : IsColimit cF) : cF.pt ⟶ cN.pt :=
  hcF.desc (comparisonCocone v cN)

private theorem descendComparison_leg {I C : Type*} [Category I] [Category C]
    {F G : I ⥤ C} (v : F ⟶ G) (cN : Cocone G) (cF : Cocone F)
    (hcF : IsColimit cF) (q : cF.pt ⟶ cN.pt)
    (hq : q = descendComparison v cN cF hcF) (i : I) :
    v.app i ≫ cN.ι.app i = cF.ι.app i ≫ q := by
  subst q
  exact (hcF.fac (comparisonCocone v cN) i).symm

private theorem descendComparison_unique {I C : Type*} [Category I] [Category C]
    {F G : I ⥤ C} (v : F ⟶ G) (cN : Cocone G) (cF : Cocone F)
    (hcF : IsColimit cF) (q : cF.pt ⟶ cN.pt)
    (hq : q = descendComparison v cN cF hcF) (g : cF.pt ⟶ cN.pt)
    (hg : ∀ i, v.app i ≫ cN.ι.app i = cF.ι.app i ≫ g) : q = g := by
  apply hcF.hom_ext
  intro i
  exact (descendComparison_leg v cN cF hcF q hq i).symm.trans (hg i)

private def specScalarTransformation {I : Type v} [Category.{w} I]
    (N F : I ⥤ CommRingCat.{u}) (v : N ⟶ F) :
    F.op ⋙ Scheme.Spec ⟶ N.op ⋙ Scheme.Spec where
  app s := Spec.map (v.app s.unop)
  naturality {s t} f := by
    change Spec.map (F.map f.unop) ≫ Spec.map (v.app t.unop) =
      Spec.map (v.app s.unop) ≫ Spec.map (N.map f.unop)
    simpa only [Spec.map_comp] using (congrArg Spec.map (v.naturality f.unop)).symm

variable {R K : Type u} [CommRing R] [CommRing K]
    {I : Type v} [Category.{w} I]
    (N : I ⥤ CommAlgCat.{u} R) (F : I ⥤ CommAlgCat.{u} K)
    (v : N ⋙ forget₂ (CommAlgCat R) CommRingCat ⟶
      F ⋙ forget₂ (CommAlgCat K) CommRingCat)
    (cN : Cocone (N.op ⋙ algSpec (.of R)))
    (cF : Cocone (F.op ⋙ algSpec (.of K))) (hcF : IsColimit cF)

private def scalarSchemesMap :
    F.op ⋙ algSpec (.of K) ⋙ Over.forget (Spec (.of K)) ⟶
      N.op ⋙ algSpec (.of R) ⋙ Over.forget (Spec (.of R)) :=
  specScalarTransformation (N ⋙ forget₂ (CommAlgCat R) CommRingCat)
    (F ⋙ forget₂ (CommAlgCat K) CommRingCat) v

/-- The prescribed natural coefficient comparison determines a map of the
colimit schemes, without choosing a second coefficient comparison. -/
def scalarModelProjection : cF.pt.left ⟶ cN.pt.left :=
  descendComparison (scalarSchemesMap N F v)
    ((Over.forget (Spec (.of R))).mapCocone cN)
    ((Over.forget (Spec (.of K))).mapCocone cF)
    (isColimitOfPreserves (Over.forget (Spec (.of K))) hcF)

/-- Every affine node square for the scalar model projection uses the
prescribed component of the retained natural coefficient comparison. -/
theorem scalarModelProjection_node (s : I) :
    Spec.map (v.app s) ≫ (cN.ι.app (op s)).left =
      (cF.ι.app (op s)).left ≫ scalarModelProjection N F v cN cF hcF :=
  descendComparison_leg (scalarSchemesMap N F v)
    ((Over.forget (Spec (.of R))).mapCocone cN)
    ((Over.forget (Spec (.of K))).mapCocone cF)
    (isColimitOfPreserves (Over.forget (Spec (.of K))) hcF)
    (scalarModelProjection N F v cN cF hcF) rfl (op s)

/-- A geometric scalar projection is the retained projection when its affine
node squares use the same prescribed coefficient comparison. -/
theorem scalarModelProjection_unique (q : cF.pt.left ⟶ cN.pt.left)
    (hq : ∀ s : I, Spec.map (v.app s) ≫ (cN.ι.app (op s)).left =
      (cF.ι.app (op s)).left ≫ q) : scalarModelProjection N F v cN cF hcF = q :=
  descendComparison_unique (scalarSchemesMap N F v)
    ((Over.forget (Spec (.of R))).mapCocone cN)
    ((Over.forget (Spec (.of K))).mapCocone cF)
    (isColimitOfPreserves (Over.forget (Spec (.of K))) hcF)
    (scalarModelProjection N F v cN cF hcF) rfl q (fun s => hq s.unop)

end FrobeniusSplitting
