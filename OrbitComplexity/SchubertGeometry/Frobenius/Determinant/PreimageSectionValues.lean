import OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.PullbackFrames
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.CommonPolynomialCoframes
import OrbitComplexity.SchubertGeometry.Frobenius.Determinant.FlatSectionReflection
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Values of pulled sections in commuting squares -/

set_option autoImplicit false

noncomputable section
universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry.Scheme.Modules

namespace SchubertGeometry.RetainedCharacter

open private wholeComparison from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.CommonPolynomialCoframes
open private SchubertGeometry.CharacterLine.pullSection
  SchubertGeometry.CharacterLine.pullSection_comp
  SchubertGeometry.CharacterLine.pullSection_congr from
  OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.PullbackFrames

private theorem section_frame_comp {C : Type*} [Category C] {A B D E : C}
    (s : A ⟶ B) (e : B ≅ D) (f : D ≅ E) :
    s ≫ (e ≪≫ f).hom = (s ≫ e.hom) ≫ f.hom :=
  (Category.assoc _ _ _).symm

private theorem section_comp_hom {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : Z.Modules) (s : (𝟙_ Z.Modules) ⟶ M) :
    SchubertGeometry.CharacterLine.pullSection f ((Scheme.Modules.pullback g).obj M)
        (SchubertGeometry.CharacterLine.pullSection g M s) ≫
          (pullbackComp f g).hom.app M =
      SchubertGeometry.CharacterLine.pullSection (f ≫ g) M s := by
  calc
    _ = (SchubertGeometry.CharacterLine.pullSection (f ≫ g) M s ≫
        (pullbackComp f g).inv.app M) ≫ (pullbackComp f g).hom.app M :=
      congrArg (fun t => t ≫ (pullbackComp f g).hom.app M)
        (SchubertGeometry.CharacterLine.pullSection_comp f g M s).symm
    _ = _ := by simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]

private theorem section_base {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (q : X ⟶ Z) (h : f ≫ g = q) (M : Z.Modules) (s : (𝟙_ Z.Modules) ⟶ M) :
    SchubertGeometry.CharacterLine.pullSection f ((Scheme.Modules.pullback g).obj M)
        (SchubertGeometry.CharacterLine.pullSection g M s) ≫
          ((pullbackComp f g).app M ≪≫ (pullbackCongr h).app M).hom =
      SchubertGeometry.CharacterLine.pullSection q M s := by
  calc
    _ = (SchubertGeometry.CharacterLine.pullSection f ((Scheme.Modules.pullback g).obj M)
        (SchubertGeometry.CharacterLine.pullSection g M s) ≫
          (pullbackComp f g).hom.app M) ≫ (pullbackCongr h).hom.app M := by
      simp only [Iso.trans_hom, Iso.app_hom, Category.assoc]
    _ = SchubertGeometry.CharacterLine.pullSection (f ≫ g) M s ≫
        (pullbackCongr h).hom.app M :=
      congrArg (fun t => t ≫ (pullbackCongr h).hom.app M) (section_comp_hom f g M s)
    _ = _ := SchubertGeometry.CharacterLine.pullSection_congr h M s

private theorem section_square {X Y Z C : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ C) (a : X ⟶ Z) (b : Z ⟶ C)
    (h : f ≫ g = a ≫ b) (M : C.Modules) (s : (𝟙_ C.Modules) ⟶ M) :
    SchubertGeometry.CharacterLine.pullSection f ((Scheme.Modules.pullback g).obj M)
        (SchubertGeometry.CharacterLine.pullSection g M s) ≫
          (wholeComparison b g a f h M).hom =
      SchubertGeometry.CharacterLine.pullSection a ((Scheme.Modules.pullback b).obj M)
        (SchubertGeometry.CharacterLine.pullSection b M s) := by
  calc
    _ = (SchubertGeometry.CharacterLine.pullSection f ((Scheme.Modules.pullback g).obj M)
        (SchubertGeometry.CharacterLine.pullSection g M s) ≫
          ((pullbackComp f g).app M ≪≫ (pullbackCongr h).app M).hom) ≫
            (pullbackComp a b).inv.app M := by
      simp only [wholeComparison, Iso.trans_hom, Iso.app_hom, Iso.app_inv, Iso.symm_hom,
        Category.assoc]
    _ = SchubertGeometry.CharacterLine.pullSection (a ≫ b) M s ≫
        (pullbackComp a b).inv.app M :=
      congrArg (fun t => t ≫ (pullbackComp a b).inv.app M)
        (section_base f g (a ≫ b) h M s)
    _ = _ := SchubertGeometry.CharacterLine.pullSection_comp a b M s

private theorem function_square {X Y A B : Scheme.{u}}
    (q : X ⟶ Y) (c : Y ⟶ A) (p : X ⟶ B) (f : B ⟶ A)
    (h : q ≫ c = p ≫ f) (v : Γ(A, ⊤)) (w : Γ(B, ⊤))
    (hw : f.appTop.hom v = w) : q.appTop.hom (c.appTop.hom v) = p.appTop.hom w := by
  change (q ≫ c).appTop.hom v = _
  rw [h]
  change p.appTop.hom (f.appTop.hom v) = _
  exact congrArg p.appTop.hom hw

private theorem function_base {X Y Z A : Scheme.{u}}
    {z : X ⟶ Z} {b : Z ⟶ A} {v : Γ(A, ⊤)} {r : Γ(X, ⊤)}
    (hr : z.appTop.hom (b.appTop.hom v) = r)
    (n : X ⟶ Y) (q : Y ⟶ Z) (h : n ≫ q = z) :
    n.appTop.hom ((q ≫ b).appTop.hom v) = r := by
  change ((n ≫ q) ≫ b).appTop.hom v = r
  rw [h]
  exact hr

private theorem preimage_section_value {T Y X C CK : Scheme.{u}}
    {g : X ⟶ CK} {qN : CK ⟶ C} {M : C.Modules} {s : (𝟙_ C.Modules) ⟶ M}
    {FK : (Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback qN).obj M) ≅
      SheafOfModules.unit X.ringCatSheaf} {r : Γ(X, ⊤)}
    (hvalue : SchubertGeometry.CharacterLine.pullSection g
        ((Scheme.Modules.pullback qN).obj M)
        (SchubertGeometry.CharacterLine.pullSection qN M s) ≫ FK.hom =
      globalSectionsSmul (SheafOfModules.unit X.ringCatSheaf) r)
    (n : X ⟶ T) (q : T ⟶ Y) (z : X ⟶ Y) (hbase : n ≫ q = z)
    (j : Y ⟶ C) (hwhole : z ≫ j = g ≫ qN) :
    SchubertGeometry.CharacterLine.pullSection n
        ((Scheme.Modules.pullback q).obj ((Scheme.Modules.pullback j).obj M))
        (SchubertGeometry.CharacterLine.pullSection q ((Scheme.Modules.pullback j).obj M)
          (SchubertGeometry.CharacterLine.pullSection j M s)) ≫
      (((pullbackComp n q).app ((Scheme.Modules.pullback j).obj M) ≪≫
        (pullbackCongr hbase).app ((Scheme.Modules.pullback j).obj M)) ≪≫
          wholeComparison qN j g z hwhole M ≪≫ FK).hom =
        globalSectionsSmul (SheafOfModules.unit X.ringCatSheaf) r := by
  calc
    _ = (SchubertGeometry.CharacterLine.pullSection n
        ((Scheme.Modules.pullback q).obj ((Scheme.Modules.pullback j).obj M))
        (SchubertGeometry.CharacterLine.pullSection q ((Scheme.Modules.pullback j).obj M)
          (SchubertGeometry.CharacterLine.pullSection j M s)) ≫
        ((pullbackComp n q).app ((Scheme.Modules.pullback j).obj M) ≪≫
          (pullbackCongr hbase).app ((Scheme.Modules.pullback j).obj M)).hom) ≫
            (wholeComparison qN j g z hwhole M ≪≫ FK).hom := by
      exact section_frame_comp _ _ _
    _ = SchubertGeometry.CharacterLine.pullSection z ((Scheme.Modules.pullback j).obj M)
          (SchubertGeometry.CharacterLine.pullSection j M s) ≫
            (wholeComparison qN j g z hwhole M ≪≫ FK).hom :=
      congrArg (fun t => t ≫ (wholeComparison qN j g z hwhole M ≪≫ FK).hom)
        (section_base n q z hbase ((Scheme.Modules.pullback j).obj M)
          (SchubertGeometry.CharacterLine.pullSection j M s))
    _ = (SchubertGeometry.CharacterLine.pullSection z ((Scheme.Modules.pullback j).obj M)
          (SchubertGeometry.CharacterLine.pullSection j M s) ≫
            (wholeComparison qN j g z hwhole M).hom) ≫ FK.hom := by
      exact section_frame_comp _ _ _
    _ = SchubertGeometry.CharacterLine.pullSection g ((Scheme.Modules.pullback qN).obj M)
          (SchubertGeometry.CharacterLine.pullSection qN M s) ≫ FK.hom :=
      congrArg (fun t => t ≫ FK.hom) (section_square z j g qN hwhole M s)
    _ = _ := hvalue

/-- A commuting coefficient square and a scalar coframe comparison reflect
an entire pulled section through a flat coefficient extension. -/
theorem preimageSection_reflect
    {R K : Type u} [rComm : CommRing R] [kComm : CommRing K]
    [rKAlg : Algebra R K] (hi : Function.Injective (algebraMap R K))
    {T Y X C CK : Scheme.{u}} (base : T ⟶ Spec (.of R)) [hFlat : Flat base]
    (baseK : X ⟶ Spec (.of K)) (n : X ⟶ T)
    (hn : IsPullback n baseK base (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (q : T ⟶ Y) (z : X ⟶ Y) (hbase : n ≫ q = z)
    (j : Y ⟶ C) (g : X ⟶ CK) (b : CK ⟶ C) (hwhole : z ≫ j = g ≫ b)
    (M : C.Modules) (s : SheafOfModules.unit C.ringCatSheaf ⟶ M)
    (E : (Scheme.Modules.pullback q).obj ((Scheme.Modules.pullback j).obj M) ≅
      SheafOfModules.unit T.ringCatSheaf)
    (FK : (Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback b).obj M) ≅
      SheafOfModules.unit X.ringCatSheaf)
    (hE : (Scheme.Modules.pullback n).mapIso E ≪≫ pullbackObjUnitIso n =
      ((pullbackComp n q).app ((Scheme.Modules.pullback j).obj M) ≪≫
        (pullbackCongr hbase).app ((Scheme.Modules.pullback j).obj M)) ≪≫
          wholeComparison b j g z hwhole M ≪≫ FK)
    (A B : CommRingCat.{u}) (f : A ⟶ B) (c : Y ⟶ Spec A) (p : X ⟶ Spec B)
    (hmap : z ≫ c = p ≫ Spec.map f)
    (v : Γ(Spec A, ⊤)) (w : Γ(Spec B, ⊤))
    (hw : (Spec.map f).appTop.hom v = w) (r : Γ(X, ⊤))
    (hr : p.appTop.hom w = r)
    (hvalue : SchubertGeometry.CharacterLine.pullSection g
      ((Scheme.Modules.pullback b).obj M)
      (SchubertGeometry.CharacterLine.pullSection b M s) ≫ FK.hom =
        globalSectionsSmul (SheafOfModules.unit X.ringCatSheaf) r) :
    SchubertGeometry.CharacterLine.pullSection q ((Scheme.Modules.pullback j).obj M)
      (SchubertGeometry.CharacterLine.pullSection j M s) ≫ E.hom =
        globalSectionsSmul (SheafOfModules.unit T.ringCatSheaf)
          ((q ≫ c).appTop.hom v) := by
  have hfunction := @function_square.{u} X Y (Spec A) (Spec B)
    z c p (Spec.map f) hmap v w hw
  have hscalar := (@function_base.{u} X T Y (Spec A) z c v
    (p.appTop.hom w) hfunction n q hbase).trans hr
  have hsection := @preimage_section_value.{u} T Y X C CK g b M s FK r
    hvalue n q z hbase j hwhole
  exact @flatSection_reflect.{u} R K rComm kComm rKAlg hi T X base hFlat
    baseK n hn ((Scheme.Modules.pullback q).obj ((Scheme.Modules.pullback j).obj M))
    (SchubertGeometry.CharacterLine.pullSection q ((Scheme.Modules.pullback j).obj M)
      (SchubertGeometry.CharacterLine.pullSection j M s)) E
    (((pullbackComp n q).app ((Scheme.Modules.pullback j).obj M) ≪≫
      (pullbackCongr hbase).app ((Scheme.Modules.pullback j).obj M)) ≪≫
        wholeComparison b j g z hwhole M ≪≫ FK) hE
    ((q ≫ c).appTop.hom v) r hscalar hsection

end SchubertGeometry.RetainedCharacter
