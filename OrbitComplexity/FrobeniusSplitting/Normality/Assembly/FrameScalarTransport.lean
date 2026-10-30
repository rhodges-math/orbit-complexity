import OrbitComplexity.FrobeniusSplitting.Normality.Assembly.FunctionsScalarMap
import TauCeti.AlgebraicGeometry.Modules.Pullback
import Batteries.Tactic.Lint

/-!
# Transport of a frame in a commuting square

The transpose of a scalar morphism on relative functions is the pullback of the
original frame. Composition and equality comparisons are made over arbitrary
schemes before applying the result to any affine presentation.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.Modules

noncomputable section

universe u

namespace FrobeniusSplitting.CharacterLine

private theorem pushforwardCongr_refl {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : X.Modules) :
    (pushforwardCongr (rfl : f = f)).hom.app M = 𝟙 _ := by
  apply Scheme.Modules.hom_ext
  intro V
  change M.presheaf.map (eqToHom (rfl : f ⁻¹ᵁ V = f ⁻¹ᵁ V)).op = 𝟙 _
  exact CategoryTheory.Functor.map_id M.presheaf _

/-- Transposition along a composite agrees with iterated transposition and the
canonical composition map for pushforward. -/
theorem pullbackHomEquiv_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : Z.Modules) (N : X.Modules)
    (t : (pullback f).obj ((pullback g).obj M) ⟶ N) :
    (pullbackPushforwardAdjunction (f ≫ g)).homEquiv M N
        ((pullbackComp f g).inv.app M ≫ t) =
      ((pullbackPushforwardAdjunction g).comp
        (pullbackPushforwardAdjunction f)).homEquiv M N t ≫
          (pushforwardComp f g).hom.app N := by
  simpa only [conjugateEquiv_pullbackComp_inv] using
    (Adjunction.homEquiv_conjugateEquiv
      ((pullbackPushforwardAdjunction g).comp (pullbackPushforwardAdjunction f))
      (pullbackPushforwardAdjunction (f ≫ g)) (pullbackComp f g).inv t).symm

/-- Transposition along equal scheme morphisms respects their specified
pullback and pushforward comparisons. -/
theorem pullbackHomEquiv_congr {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g)
    (M : Y.Modules) (N : X.Modules) (t : (pullback f).obj M ⟶ N) :
    (pullbackPushforwardAdjunction g).homEquiv M N
        ((pullbackCongr h.symm).hom.app M ≫ t) =
      (pullbackPushforwardAdjunction f).homEquiv M N t ≫
        (pushforwardCongr h).hom.app N := by
  subst g
  simp only [pullbackCongr, eqToIso_refl, Iso.refl_hom, NatTrans.id_app,
    Category.id_comp, pushforwardCongr_refl, Category.comp_id]

private theorem transpose_composite {C D E : Type*} [Category C] [Category D]
    [Category E] {L : C ⥤ D} {R : D ⥤ C} {F : D ⥤ E} {P : E ⥤ D}
    (a : L ⊣ R) (b : F ⊣ P) {M : C} {N : D} {O : E}
    (e : L.obj M ⟶ N) (q : F.obj N ⟶ O) :
    (a.comp b).homEquiv M O (F.map e ≫ q) =
      a.homEquiv M N e ≫ R.map (b.homEquiv N O q) := by
  rw [Adjunction.comp_homEquiv, Equiv.trans_apply,
    b.homEquiv_naturality_left, a.homEquiv_naturality_right]

/-- Iterated transposition cancels a transpose followed by the second counit. -/
theorem pullbackHomEquiv_double {P S T : Scheme.{u}} (q : T ⟶ S) (a : P ⟶ T)
    (M : S.Modules) (N : P.Modules)
    (ψ : M ⟶ (pushforward q).obj ((pushforward a).obj N)) :
    ((pullbackPushforwardAdjunction q).comp
      (pullbackPushforwardAdjunction a)).homEquiv M N
        ((pullback a).map
            (((pullbackPushforwardAdjunction q).homEquiv M
              ((pushforward a).obj N)).symm ψ) ≫
          (pullbackPushforwardAdjunction a).counit.app N) = ψ := by
  rw [Adjunction.comp_homEquiv, Equiv.trans_apply,
    ← Adjunction.homEquiv_counit, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- The pullback of a frame has the transpose given by the scalar unit and the
composition map for pushforward. -/
theorem frameHomEquiv_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : Z.Modules)
    (e : (pullback g).obj M ⟶ SheafOfModules.unit Y.ringCatSheaf) :
    (pullbackPushforwardAdjunction (f ≫ g)).homEquiv M
        (SheafOfModules.unit X.ringCatSheaf)
        ((pullbackComp f g).inv.app M ≫ (pullback f).map e ≫
          (pullbackObjUnitIso f).hom) =
      (pullbackPushforwardAdjunction g).homEquiv M
          (SheafOfModules.unit Y.ringCatSheaf) e ≫
        (pushforward g).map
          (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) ≫
        (pushforwardComp f g).hom.app (SheafOfModules.unit X.ringCatSheaf) := by
  erw [pullbackHomEquiv_comp, transpose_composite,
    pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitIso_hom]
  exact Category.assoc _ _ _

/-- A frame pulls back through a commuting square by composition, equality and
pullback of the unit object. -/
def squareFrameIso {P X S T : Scheme.{u}} (q : T ⟶ S) (a : P ⟶ T)
    (b : X ⟶ S) (k : P ⟶ X) (h : k ≫ b = a ≫ q)
    (M : S.Modules)
    (e : (pullback b).obj M ≅ SheafOfModules.unit X.ringCatSheaf) :
    (pullback a).obj ((pullback q).obj M) ≅ SheafOfModules.unit P.ringCatSheaf :=
  (pullbackComp a q).app M ≪≫ (pullbackCongr h.symm).app M ≪≫
    ((pullbackComp k b).app M).symm ≪≫ (pullback k).mapIso e ≪≫
      pullbackObjUnitIso k

private theorem scalar_composition {C : Type*} [Category C]
    {A B D E F G : C} (c : A ⟶ B) (u : B ⟶ D) (v : D ⟶ E)
    (w : E ⟶ F) (i : G ≅ F) (z : B ⟶ G)
    (hz : z = u ≫ v ≫ w ≫ i.inv) :
    (c ≫ z) ≫ i.hom = (c ≫ u ≫ v) ≫ w := by
  subst z
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

private theorem iso_transpose_cancel {C : Type*} [Category C]
    {A B D : C} (i : A ≅ B) (j : B ≅ D) (d : A ≅ D)
    (hd : d = i ≪≫ j) (t : A ⟶ D) (ht : i.inv ≫ t = j.hom) :
    t = d.hom := by
  have h : t = i.hom ≫ j.hom := by
    calc
      t = (𝟙 A) ≫ t := (Category.id_comp t).symm
      _ = (i.hom ≫ i.inv) ≫ t :=
        congrArg (fun f : A ⟶ A => f ≫ t) i.hom_inv_id.symm
      _ = i.hom ≫ (i.inv ≫ t) := Category.assoc _ _ _
      _ = i.hom ≫ j.hom := congrArg (fun f : B ⟶ D => i.hom ≫ f) ht
  exact h.trans (congrArg (fun e : A ≅ D => e.hom) hd).symm

/-- The local transpose of the scalar image of a frame is exactly its
pullback frame, including the specified commuting-square comparison. -/
theorem squareFrameIso_transpose {P X S T : Scheme.{u}} (q : T ⟶ S)
    (a : P ⟶ T) (b : X ⟶ S) (k : P ⟶ X) (h : k ≫ b = a ≫ q)
    (M : S.Modules)
    (e : (pullback b).obj M ≅ SheafOfModules.unit X.ringCatSheaf) :
    (pullback a).map
        (((pullbackPushforwardAdjunction q).homEquiv M
          (relativeFunctionsObj T (Over.mk a))).symm
            ((pullbackPushforwardAdjunction b).homEquiv M
                (SheafOfModules.unit X.ringCatSheaf) e.hom ≫
              functionsScalarMap q (Over.mk a) (Over.mk b) k h)) ≫
        (pullbackPushforwardAdjunction a).counit.app
          (SheafOfModules.unit P.ringCatSheaf) =
      (squareFrameIso q a b k h M e).hom := by
  let U : P.Modules := SheafOfModules.unit P.ringCatSheaf
  let W : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let c : M ⟶ (pushforward b).obj W :=
    (pullbackPushforwardAdjunction b).homEquiv M W e.hom
  let z : (pushforward b).obj W ⟶
      (pushforward q).obj ((pushforward a).obj U) :=
    functionsScalarMap q (Over.mk a) (Over.mk b) k h
  let ψ : M ⟶ (pushforward q).obj ((pushforward a).obj U) := c ≫ z
  let t₁ : (pullback a).obj ((pullback q).obj M) ⟶ U :=
    (pullback a).map
        (((pullbackPushforwardAdjunction q).homEquiv M
          ((pushforward a).obj U)).symm ψ) ≫
      (pullbackPushforwardAdjunction a).counit.app U
  let t₂ : (pullback (k ≫ b)).obj M ⟶ U :=
    (pullbackComp k b).inv.app M ≫ (pullback k).map e.hom ≫
      (pullbackObjUnitIso k).hom
  let i : (pullback a).obj ((pullback q).obj M) ≅
      (pullback (a ≫ q)).obj M := (pullbackComp a q).app M
  let j : (pushforward q).obj ((pushforward a).obj U) ≅
      (pushforward (a ≫ q)).obj U := (pushforwardComp a q).app U
  let E : (pullback (a ≫ q)).obj M ≅ U :=
    (pullbackCongr h.symm).app M ≪≫ ((pullbackComp k b).app M).symm ≪≫
      (pullback k).mapIso e ≪≫ pullbackObjUnitIso k
  let u : (pushforward b).obj W ⟶
      (pushforward b).obj ((pushforward k).obj U) :=
    (pushforward b).map
      (SheafOfModules.unitToPushforwardObjUnit k.toRingCatSheafHom)
  let v : (pushforward b).obj ((pushforward k).obj U) ⟶
      (pushforward (k ≫ b)).obj U := (pushforwardComp k b).hom.app U
  let w : (pushforward (k ≫ b)).obj U ⟶
      (pushforward (a ≫ q)).obj U := (pushforwardCongr h).hom.app U
  let Φ := (pullbackPushforwardAdjunction (a ≫ q)).homEquiv M U
  have hleft₁ : Φ (i.inv ≫ t₁) =
      ((pullbackPushforwardAdjunction q).comp
        (pullbackPushforwardAdjunction a)).homEquiv M U t₁ ≫ j.hom :=
    pullbackHomEquiv_comp a q M U t₁
  have hleft₂ : ((pullbackPushforwardAdjunction q).comp
      (pullbackPushforwardAdjunction a)).homEquiv M U t₁ = ψ :=
    pullbackHomEquiv_double q a M U ψ
  have hleft : Φ (i.inv ≫ t₁) = ψ ≫ j.hom :=
    hleft₁.trans (congrArg
      (fun f : M ⟶ (pushforward q).obj ((pushforward a).obj U) => f ≫ j.hom)
      hleft₂)
  have hright₁ : Φ ((pullbackCongr h.symm).hom.app M ≫ t₂) =
      (pullbackPushforwardAdjunction (k ≫ b)).homEquiv M U t₂ ≫ w :=
    pullbackHomEquiv_congr h M U t₂
  have hright₂ : (pullbackPushforwardAdjunction (k ≫ b)).homEquiv M U t₂ =
      c ≫ u ≫ v :=
    frameHomEquiv_comp k b M e.hom
  have hright : Φ E.hom = (c ≫ u ≫ v) ≫ w :=
    hright₁.trans (congrArg
      (fun f : M ⟶ (pushforward (k ≫ b)).obj U => f ≫ w) hright₂)
  have hz : z = u ≫ v ≫ w ≫ j.inv :=
    functionsScalarMap_expansion q a b k h
  have hmiddle : ψ ≫ j.hom = (c ≫ u ≫ v) ≫ w :=
    scalar_composition c u v w j z hz
  have hbase : i.inv ≫ t₁ = E.hom :=
    Φ.injective (hleft.trans (hmiddle.trans hright.symm))
  exact iso_transpose_cancel i E (squareFrameIso q a b k h M e) rfl t₁ hbase

private theorem transpose_isIso {C D : Type*} [Category C] [Category D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) [R.Full] [R.Faithful]
    {M : C} {N : D} (c : M ⟶ R.obj N) (hc : IsIso (L.map c)) :
    IsIso ((adj.homEquiv M N).symm c) := by
  let : IsIso (L.map c) := hc
  rw [Adjunction.homEquiv_counit]
  infer_instance

private theorem module_transpose_isIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] (M : Y.Modules)
    (c : M ⟶ (pushforward f).obj (SheafOfModules.unit X.ringCatSheaf))
    (hc : IsIso ((pullback f).map c)) :
    IsIso (((pullbackPushforwardAdjunction f).homEquiv M
      (SheafOfModules.unit X.ringCatSheaf)).symm c) :=
  transpose_isIso (C := Y.Modules) (D := X.Modules)
    (L := pullback f) (R := pushforward f) (M := M)
    (N := SheafOfModules.unit X.ringCatSheaf) (pullbackPushforwardAdjunction f) c hc

private theorem module_counit_isIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] (M : X.Modules) :
    IsIso ((pullbackPushforwardAdjunction f).counit.app M) := by
  let : (pushforward f).Full := inferInstance
  let : (pushforward f).Faithful := inferInstance
  let : IsIso (pullbackPushforwardAdjunction f).counit :=
    (pullbackPushforwardAdjunction f).counit_isIso_of_R_fully_faithful
  infer_instance

private theorem isIso_composition {C : Type*} [Category C] {A B D : C}
    (f : A ⟶ B) (g : B ⟶ D) (hf : IsIso f) (hg : IsIso g) : IsIso (f ≫ g) := by
  let : IsIso f := hf
  let : IsIso g := hg
  infer_instance

private theorem isIso_from_frame {C : Type*} [Category C] {A B D : C}
    (f : A ⟶ B) (g : B ⟶ D) (e : A ≅ D) (h : f ≫ g = e.hom)
    (hg : IsIso g) : IsIso f := by
  let : IsIso g := hg
  let : IsIso (f ≫ g) := h.symm ▸ inferInstance
  exact IsIso.of_isIso_comp_right f g

/-- A scalar comparison is an isomorphism on a chart when both selected
coordinates are frames and its coordinate is the specified scalar transpose. -/
theorem frameScalar_isIso {P X S T : Scheme.{u}} (q : T ⟶ S)
    (a : P ⟶ T) (b : X ⟶ S) [IsOpenImmersion a] [IsOpenImmersion b]
    (k : P ⟶ X) (h : k ≫ b = a ≫ q) (M : S.Modules) (N : T.Modules)
    (c : M ⟶ relativeFunctionsObj S (Over.mk b))
    (d : N ⟶ relativeFunctionsObj T (Over.mk a))
    (f : (pullback q).obj M ⟶ N)
    (hc : IsIso ((pullback b).map c)) (hd : IsIso ((pullback a).map d))
    (hf : f ≫ d = ((pullbackPushforwardAdjunction q).homEquiv M
      (relativeFunctionsObj T (Over.mk a))).symm
        (c ≫ functionsScalarMap q (Over.mk a) (Over.mk b) k h)) :
    IsIso ((pullback a).map f) := by
  let : IsIso ((pullback b).map c) := hc
  let : IsIso ((pullback a).map d) := hd
  let : IsIso (((pullbackPushforwardAdjunction b).homEquiv M
      (SheafOfModules.unit X.ringCatSheaf)).symm c) :=
    module_transpose_isIso b M c hc
  let : IsIso ((pullbackPushforwardAdjunction a).counit.app
      (SheafOfModules.unit P.ringCatSheaf)) :=
    module_counit_isIso a (SheafOfModules.unit P.ringCatSheaf)
  let e : (pullback b).obj M ≅ SheafOfModules.unit X.ringCatSheaf :=
    asIso (((pullbackPushforwardAdjunction b).homEquiv M
      (SheafOfModules.unit X.ringCatSheaf)).symm c)
  have hc' : (pullbackPushforwardAdjunction b).homEquiv M
      (SheafOfModules.unit X.ringCatSheaf) e.hom = c :=
    Equiv.apply_symm_apply _ c
  have he := squareFrameIso_transpose q a b k h M e
  rw [hc'] at he
  have hframe : (pullback a).map f ≫ (pullback a).map d ≫
      (pullbackPushforwardAdjunction a).counit.app
        (SheafOfModules.unit P.ringCatSheaf) = (squareFrameIso q a b k h M e).hom := by
    erw [← Category.assoc, ← CategoryTheory.Functor.map_comp, hf]
    exact he
  have hdε := isIso_composition (C := P.Modules)
    (A := (pullback a).obj N)
    (B := (pullback a).obj ((pushforward a).obj (SheafOfModules.unit P.ringCatSheaf)))
    (D := SheafOfModules.unit P.ringCatSheaf)
    ((pullback a).map d)
    ((pullbackPushforwardAdjunction a).counit.app (SheafOfModules.unit P.ringCatSheaf))
    hd (module_counit_isIso a (SheafOfModules.unit P.ringCatSheaf))
  exact isIso_from_frame (C := P.Modules)
    (A := (pullback a).obj ((pullback q).obj M)) (B := (pullback a).obj N)
    (D := SheafOfModules.unit P.ringCatSheaf) ((pullback a).map f)
    ((pullback a).map d ≫ (pullbackPushforwardAdjunction a).counit.app
      (SheafOfModules.unit P.ringCatSheaf))
    (squareFrameIso q a b k h M e) hframe hdε

end FrobeniusSplitting.CharacterLine
