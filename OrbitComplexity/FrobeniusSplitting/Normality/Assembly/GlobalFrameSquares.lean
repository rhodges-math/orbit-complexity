import OrbitComplexity.FrobeniusSplitting.Normality.Assembly.FrameScalarTransport
import Batteries.Tactic.Lint

/-!
# Squares of global coframes

Pulling a global coframe along a commutative square agrees with pulling it
along the other two sides, through the pullback comparison isomorphisms.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.Modules

namespace FrobeniusSplitting.CharacterLine

private abbrev unitModule (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

private def squareModuleComparison {A B S T : Scheme.{u}}
    (q : T ⟶ S) (a : A ⟶ T) (b : B ⟶ S) (k : A ⟶ B)
    (h : k ≫ b = a ≫ q) :
    Scheme.Modules.pullback q ⋙ Scheme.Modules.pullback a ≅
      Scheme.Modules.pullback b ⋙ Scheme.Modules.pullback k :=
  pullbackComp a q ≪≫ pullbackCongr h.symm ≪≫ (pullbackComp k b).symm

private theorem iso_hom_compare {C : Type*} [Category C] {A B D : C}
    (e : A ≅ B) (c : B ⟶ D) (d : A ⟶ D) (h : e.inv ≫ d = c) :
    e.hom ≫ c = d := by
  rw [← h, Iso.hom_inv_id_assoc]

set_option backward.isDefEq.respectTransparency.types false in
private theorem square_unit {A B S T : Scheme.{u}}
    (q : T ⟶ S) (a : A ⟶ T) (b : B ⟶ S) (k : A ⟶ B)
    (h : k ≫ b = a ≫ q) :
    (squareModuleComparison q a b k h).hom.app (unitModule S) ≫
        (Scheme.Modules.pullback k).map (pullbackObjUnitIso b).hom ≫
          (pullbackObjUnitIso k).hom =
      (Scheme.Modules.pullback a).map (pullbackObjUnitIso q).hom ≫
        (pullbackObjUnitIso a).hom := by
  have hb : (pullbackComp k b).inv.app (unitModule S) ≫
      (Scheme.Modules.pullback k).map (pullbackObjUnitIso b).hom ≫
        (pullbackObjUnitIso k).hom = (pullbackObjUnitIso (k ≫ b)).hom :=
    pullbackObjUnitIso_comp k b
  have hc : (pullbackCongr h.symm).hom.app (unitModule S) ≫
      (pullbackObjUnitIso (k ≫ b)).hom = (pullbackObjUnitIso (a ≫ q)).hom :=
    pullbackObjUnitIso_congr h.symm
  have ha : (pullbackComp a q).hom.app (unitModule S) ≫
      (pullbackObjUnitIso (a ≫ q)).hom =
      (Scheme.Modules.pullback a).map (pullbackObjUnitIso q).hom ≫
        (pullbackObjUnitIso a).hom :=
    iso_hom_compare ((pullbackComp a q).app (unitModule S)) _ _
      (pullbackObjUnitIso_comp a q)
  have hh : (pullbackComp a q).hom.app (unitModule S) ≫
      (pullbackCongr h.symm).hom.app (unitModule S) ≫
      (pullbackComp k b).inv.app (unitModule S) ≫
      (Scheme.Modules.pullback k).map (pullbackObjUnitIso b).hom ≫
        (pullbackObjUnitIso k).hom =
      (Scheme.Modules.pullback a).map (pullbackObjUnitIso q).hom ≫
        (pullbackObjUnitIso a).hom := by
    rw [hb, hc, ha]
  simpa only [squareModuleComparison, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Category.assoc] using hh

private theorem frame_on_square {C D : Type*} [Category C] [Category D]
    (F G : C ⥤ D) (a : F ≅ G) {M O : C} {T : D}
    (u : F.obj O ≅ T) (v : G.obj O ≅ T) (e : M ≅ O)
    (hu : a.app O ≪≫ v = u) :
    a.app M ≪≫ G.mapIso e ≪≫ v = F.mapIso e ≪≫ u := by
  apply Iso.ext
  have hunit := congrArg Iso.hom hu
  simp only [Iso.trans_hom, Iso.app_hom] at hunit
  simp only [Iso.trans_hom, Iso.app_hom, CategoryTheory.Functor.mapIso_hom]
  rw [← a.hom.naturality_assoc e.hom, hunit]

set_option backward.isDefEq.respectTransparency.types false in
/-- The coframe square of a global coframe agrees with its pullback along
the other side of the square. -/
theorem squareFrameIso_global {A B S T : Scheme.{u}}
    (q : T ⟶ S) (a : A ⟶ T) (b : B ⟶ S) (k : A ⟶ B)
    (h : k ≫ b = a ≫ q) (L : S.Modules) (E : L ≅ unitModule S) :
    squareFrameIso q a b k h L
        ((Scheme.Modules.pullback b).mapIso E ≪≫ pullbackObjUnitIso b) =
      (Scheme.Modules.pullback a).mapIso
          ((Scheme.Modules.pullback q).mapIso E ≪≫ pullbackObjUnitIso q) ≪≫
        pullbackObjUnitIso a := by
  let F := Scheme.Modules.pullback q ⋙ Scheme.Modules.pullback a
  let G := Scheme.Modules.pullback b ⋙ Scheme.Modules.pullback k
  let α : F ≅ G := squareModuleComparison q a b k h
  let u : F.obj (unitModule S) ≅ unitModule A :=
    (Scheme.Modules.pullback a).mapIso (pullbackObjUnitIso q) ≪≫ pullbackObjUnitIso a
  let v : G.obj (unitModule S) ≅ unitModule A :=
    (Scheme.Modules.pullback k).mapIso (pullbackObjUnitIso b) ≪≫ pullbackObjUnitIso k
  have hu : α.app (unitModule S) ≪≫ v = u := by
    apply Iso.ext
    exact square_unit q a b k h
  have hh := congrArg Iso.hom (frame_on_square F G α u v E hu)
  have happ : (squareModuleComparison q a b k h).hom.app L =
      (pullbackComp a q).hom.app L ≫ (pullbackCongr h.symm).hom.app L ≫
        (pullbackComp k b).inv.app L := rfl
  apply Iso.ext
  simpa only [squareFrameIso, F, G, α, u, v, Iso.trans_hom, Iso.symm_hom,
    Iso.app_hom, Iso.app_inv, CategoryTheory.Functor.mapIso_hom,
    CategoryTheory.Functor.comp_map, CategoryTheory.Functor.map_comp,
    happ, Category.assoc] using hh

end FrobeniusSplitting.CharacterLine
