import OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.FrameComposition
import TauCeti.AlgebraicGeometry.Modules.Pullback
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Adjunction transport of character coframes -/

open AlgebraicGeometry CategoryTheory ReductiveGroups GroupActions
open AlgebraicGeometry.Scheme.Modules
open scoped CategoryTheory.MonObj
set_option autoImplicit false
noncomputable section
universe u v w
namespace SchubertGeometry.CharacterLine.CoframeTransport
open private restrict_adjunct
  from OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.NativeFrame
open private adjunct_composite pushforwardCongr_refl
  from OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.FrameComposition

private def frameIso {X Y Z U : Scheme.{u}} (r : X ⟶ Z) (c : Y ⟶ X)
    [IsOpenImmersion c] (a : Y ⟶ U) (q : U ⟶ Z) (M : Z.Modules)
    (h : a ≫ q = c ≫ r)
    (e : (pullback (a ≫ q)).obj M ≅ SheafOfModules.unit Y.ringCatSheaf) :
    (restrictFunctor c).obj ((pullback r).obj M) ≅
      SheafOfModules.unit Y.ringCatSheaf :=
  (restrictFunctorIsoPullback c).app ((pullback r).obj M) ≪≫
    (pullbackComp c r).app M ≪≫ (pullbackCongr h.symm).app M ≪≫ e

private def pullCoframe {X Y Z : Scheme.{u}} (f : X ⟶ Y) (c : Y ⟶ Z)
    (M : Z.Modules) (e : (pullback c).obj M ⟶ SheafOfModules.unit Y.ringCatSheaf) :
    (pullback (f ≫ c)).obj M ⟶ SheafOfModules.unit X.ringCatSheaf :=
  (pullbackComp f c).inv.app M ≫ (pullback f).map e ≫ (pullbackObjUnitIso f).hom

private theorem iso_app_eqToHom {C D : Type*} [Category C] [Category D]
    {F G : C ⥤ D} (h : F = G) (M : C) :
    (eqToIso h).hom.app M = eqToHom (congrArg (fun T => T.obj M) h) := by
  cases h
  rfl

private theorem mapped_composition {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {A E : D} {B T U : C} (a : A ⟶ F.obj B)
    (b : B ⟶ T) (e : T ⟶ U) (v : F.obj U ⟶ E) :
    a ≫ F.map (b ≫ e) ≫ v = (a ≫ F.map b) ≫ F.map e ≫ v := by
  have h₀ := congrArg (fun t => a ≫ t ≫ v) (F.map_comp b e)
  have h₁ := congrArg (fun t => a ≫ t) (Category.assoc (F.map b) (F.map e) v)
  exact h₀.trans (h₁.trans (Category.assoc a (F.map b) (F.map e ≫ v)).symm)

private theorem base_change_at {X Y Z W : Scheme.{u}} (f : X ⟶ Y) (c : Y ⟶ Z)
    (r : Z ⟶ W) (k : X ⟶ Z) (h : f ≫ c = k) (M : W.Modules)
    (e : (pullback (c ≫ r)).obj M ⟶ SheafOfModules.unit Y.ringCatSheaf) :
    (pullbackCongr h.symm).hom.app ((pullback r).obj M) ≫
        pullCoframe f c ((pullback r).obj M) ((pullbackComp c r).hom.app M ≫ e) =
      (pullbackComp k r).hom.app M ≫
        (pullbackCongr ((Category.assoc f c r).symm.trans
          (congrArg (fun a => a ≫ r) h)).symm).hom.app M ≫ pullCoframe f (c ≫ r) M e := by
  subst k
  let a := (pullbackComp f c).inv.app ((pullback r).obj M)
  let b := (pullbackComp c r).hom.app M
  let v := (pullbackObjUnitIso f).hom
  let q := (pullbackComp (f ≫ c) r).hom.app M
  let t := (pullbackComp f (c ≫ r)).inv.app M
  have hi : (pullbackCongr (rfl : f ≫ c = f ≫ c)).hom.app ((pullback r).obj M) =
      𝟙 ((pullback (f ≫ c)).obj ((pullback r).obj M)) := rfl
  have hl := (congrArg (fun z => z ≫ pullCoframe f c ((pullback r).obj M) (b ≫ e)) hi).trans
    (Category.id_comp _)
  have hm := mapped_composition (pullback f) a b e v
  have ht := pullbackComp_inv_app_comp_pullback_map_pullbackComp_hom_app f c r M
  have hp := congrArg (fun z => z ≫ (pullback f).map e ≫ v) ht
  have hc : (pullbackCongr (Category.assoc f c r)).hom.app M =
      eqToHom (congrArg (fun z : X ⟶ W => (pullback z).obj M) (Category.assoc f c r)) :=
    iso_app_eqToHom _ M
  have hr := congrArg (fun z => (q ≫ z ≫ t) ≫ (pullback f).map e ≫ v) hc.symm
  have ha := (Category.assoc q
    ((pullbackCongr (Category.assoc f c r)).hom.app M ≫ t) ((pullback f).map e ≫ v)).trans
      (congrArg (fun z => q ≫ z)
        (Category.assoc ((pullbackCongr (Category.assoc f c r)).hom.app M) t
          ((pullback f).map e ≫ v)))
  exact hl.trans (hm.trans (hp.trans (hr.trans ha)))

private theorem adjunct_congr {X Y : Scheme.{u}} {a b : X ⟶ Y} (h : a = b)
    (M : Y.Modules) (N : X.Modules) (e : (pullback a).obj M ⟶ N) :
    (pullbackPushforwardAdjunction a).homEquiv M N e ≫
        (pushforwardCongr h).hom.app N =
      (pullbackPushforwardAdjunction b).homEquiv M N
        ((pullbackCongr h.symm).hom.app M ≫ e) := by
  subst b
  have hi := pushforwardCongr_refl a N
  have he : (pullbackCongr (rfl : a = a)).hom.app M ≫ e = e := by
    simp only [pullbackCongr, eqToIso_refl, Iso.refl_hom, NatTrans.id_app, Category.id_comp]
  exact ((congrArg (fun t => (pullbackPushforwardAdjunction a).homEquiv M N e ≫ t) hi).trans
    (Category.comp_id _)).trans
      (congrArg ((pullbackPushforwardAdjunction a).homEquiv M N) he).symm

private theorem coordinate_match {P Q X : Scheme.{u}} (c₀ c₁ : P ⟶ X)
    [IsOpenImmersion c₀] [IsOpenImmersion c₁] (f₀ f₁ : Q ⟶ P)
    (h : f₁ ≫ c₁ = f₀ ≫ c₀) (M : X.Modules)
    (e₀ : (restrictFunctor c₀).obj M ⟶ SheafOfModules.unit P.ringCatSheaf)
    (e₁ : (restrictFunctor c₁).obj M ⟶ SheafOfModules.unit P.ringCatSheaf)
    (s : SheafOfModules.unit Q.ringCatSheaf ⟶ SheafOfModules.unit Q.ringCatSheaf)
    (hm : pullCoframe f₀ c₀ M ((restrictFunctorIsoPullback c₀).inv.app M ≫ e₀) =
      (pullbackCongr h.symm).hom.app M ≫
        pullCoframe f₁ c₁ M ((restrictFunctorIsoPullback c₁).inv.app M ≫ e₁) ≫ s) :
    (restrictAdjunction c₀).homEquiv M _ e₀ ≫
        (pushforward c₀).map (SheafOfModules.unitToPushforwardObjUnit f₀.toRingCatSheafHom) ≫
        (pushforwardComp f₀ c₀).hom.app _ =
      (restrictAdjunction c₁).homEquiv M _ e₁ ≫
        (pushforward c₁).map (SheafOfModules.unitToPushforwardObjUnit f₁.toRingCatSheafHom) ≫
        (pushforwardComp f₁ c₁).hom.app _ ≫ (pushforwardCongr h).hom.app _ ≫
        (pushforward (f₀ ≫ c₀)).map s := by
  let O : Q.Modules := SheafOfModules.unit Q.ringCatSheaf
  let a₀ := (restrictFunctorIsoPullback c₀).inv.app M ≫ e₀
  let a₁ := (restrictFunctorIsoPullback c₁).inv.app M ≫ e₁
  have h₀ := adjunct_composite f₀ c₀ M a₀
  have h₁ := adjunct_composite f₁ c₁ M a₁
  have u₀ : (pullbackPushforwardAdjunction c₀).homEquiv M
      (SheafOfModules.unit P.ringCatSheaf) a₀ = (restrictAdjunction c₀).homEquiv M _ e₀ :=
    restrict_adjunct c₀ M (SheafOfModules.unit P.ringCatSheaf) e₀
  have u₁ : (pullbackPushforwardAdjunction c₁).homEquiv M
      (SheafOfModules.unit P.ringCatSheaf) a₁ = (restrictAdjunction c₁).homEquiv M _ e₁ :=
    restrict_adjunct c₁ M (SheafOfModules.unit P.ringCatSheaf) e₁
  have ht := adjunct_congr h M O (pullCoframe f₁ c₁ M a₁)
  have hn := (pullbackPushforwardAdjunction (f₀ ≫ c₀)).homEquiv_naturality_right
    ((pullbackCongr h.symm).hom.app M ≫ pullCoframe f₁ c₁ M a₁) s
  calc
    _ = (pullbackPushforwardAdjunction (f₀ ≫ c₀)).homEquiv M O
        (pullCoframe f₀ c₀ M a₀) :=
      (congrArg (fun a => a ≫ (pushforward c₀).map
        (SheafOfModules.unitToPushforwardObjUnit f₀.toRingCatSheafHom) ≫
          (pushforwardComp f₀ c₀).hom.app O) u₀.symm).trans h₀.symm
    _ = (pullbackPushforwardAdjunction (f₀ ≫ c₀)).homEquiv M O
        ((pullbackCongr h.symm).hom.app M ≫ pullCoframe f₁ c₁ M a₁ ≫ s) :=
      congrArg ((pullbackPushforwardAdjunction (f₀ ≫ c₀)).homEquiv M O) hm
    _ = ((pullbackPushforwardAdjunction (f₁ ≫ c₁)).homEquiv M O
        (pullCoframe f₁ c₁ M a₁) ≫ (pushforwardCongr h).hom.app O) ≫
        (pushforward (f₀ ≫ c₀)).map s :=
      hn.trans (congrArg (fun a => a ≫ (pushforward (f₀ ≫ c₀)).map s) ht.symm)
    _ = _ := by
      have hu := congrArg (fun a => a ≫ (pushforward c₁).map
        (SheafOfModules.unitToPushforwardObjUnit f₁.toRingCatSheafHom) ≫
          (pushforwardComp f₁ c₁).hom.app O) u₁
      have hv := congrArg (fun a => a ≫ (pushforwardCongr h).hom.app O ≫
        (pushforward (f₀ ≫ c₀)).map s) (h₁.trans hu)
      have ha := congrArg (fun t => (restrictAdjunction c₁).homEquiv M
        (SheafOfModules.unit P.ringCatSheaf) e₁ ≫ t)
        (Category.assoc
          ((pushforward c₁).map (SheafOfModules.unitToPushforwardObjUnit f₁.toRingCatSheafHom))
          ((pushforwardComp f₁ c₁).hom.app O)
          ((pushforwardCongr h).hom.app O ≫ (pushforward (f₀ ≫ c₀)).map s))
      exact hv.trans ha

private def algebraMapOver {K A B : Type u} [CommRing K] [CommRing A] [CommRing B]
    [Algebra K A] [Algebra K B] (f : A →ₐ[K] B) :
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K B))) ⟶
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K A))) :=
  Over.homMk (Spec.map (CommRingCat.ofHom f.toRingHom)) (by
    change Spec.map (CommRingCat.ofHom f.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap K A)) =
        Spec.map (CommRingCat.ofHom (algebraMap K B))
    rw [← Spec.map_comp]
    congr 1
    ext a
    exact f.commutes a)

private theorem algebraMapOver_comp {K A B C : Type u} [CommRing K]
    [CommRing A] [CommRing B] [CommRing C] [Algebra K A] [Algebra K B] [Algebra K C]
    (f : A →ₐ[K] B) (g : B →ₐ[K] C) :
    algebraMapOver g ≫ algebraMapOver f = algebraMapOver (g.comp f) := by
  apply CostructuredArrow.hom_ext
  exact (Spec.map_comp _ _).symm

private theorem iso_chain_cancel {D : Type*} [Category D] {A B C E F : D}
    (a : A ≅ B) (b : B ≅ C) (c : C ≅ E) (d : E ≅ F) :
    a.inv ≫ (a ≪≫ b ≪≫ c ≪≫ d).hom = b.hom ≫ c.hom ≫ d.hom := by
  change a.inv ≫ a.hom ≫ b.hom ≫ c.hom ≫ d.hom = _
  exact a.inv_hom_id_assoc _

private theorem frameIso_hom {X Y Z U : Scheme.{u}} (r : X ⟶ Z) (c : Y ⟶ X)
    [IsOpenImmersion c] (a : Y ⟶ U) (q : U ⟶ Z) (M : Z.Modules)
    (h : a ≫ q = c ≫ r)
    (e : (pullback (a ≫ q)).obj M ≅ SheafOfModules.unit Y.ringCatSheaf) :
    (restrictFunctorIsoPullback c).inv.app ((pullback r).obj M) ≫
        (frameIso r c a q M h e).hom =
      (pullbackComp c r).hom.app M ≫ (pullbackCongr h.symm).hom.app M ≫ e.hom := by
  exact iso_chain_cancel ((restrictFunctorIsoPullback c).app ((pullback r).obj M))
    ((pullbackComp c r).app M) ((pullbackCongr h.symm).app M) e

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

private theorem frameIso_evaluation {L : Scheme.{u}} (chi : G.characters)
    (P : Over (Spec (.of K))) (c : P.left ⟶ L) [IsOpenImmersion c]
    (r : L ⟶ (flagVariety G).scheme) (g : G.points)
    (a : P ⟶ (oppositeUnipotentVariety G).toOver)
    (h : a.left ≫ (flagChartMorphism G g).left = c ≫ r) :
    (restrictFunctorIsoPullback c).inv.app ((pullback r).obj (flagCharacterModule G chi)) ≫
        (frameIso r c a.left (flagChartMorphism G g).left (flagCharacterModule G chi) h
          (flagCharacterPullbackIso G g chi a.left)).hom =
      (pullbackComp c r).hom.app (flagCharacterModule G chi) ≫
        characterFrameEvaluation G chi P (c ≫ r) (a ≫ flagChartMap G g)
          (((Category.assoc a.left (flagChartMap G g).left (flagQuotient G)).trans
            (congrArg (fun t => a.left ≫ t)
              (congrArg (fun f : (oppositeUnipotentVariety G).toOver ⟶
                (flagVariety G).toOver => f.left) (flagChartMap_quotient G g)))).trans h) := by
  have hq : (a ≫ flagChartMap G g).left ≫ flagQuotient G = c ≫ r :=
    ((Category.assoc a.left (flagChartMap G g).left (flagQuotient G)).trans
      (congrArg (fun t => a.left ≫ t)
        (congrArg (fun f : (oppositeUnipotentVariety G).toOver ⟶
          (flagVariety G).toOver => f.left) (flagChartMap_quotient G g)))).trans h
  let v := (pullbackCongr h.symm).hom.app (flagCharacterModule G chi)
  have he := flagCharacterPullbackIso_eval G chi g P a
  have hc := characterFrameEvaluation_congr G chi P h.symm (a ≫ flagChartMap G g) hq
  have hv := (congrArg (fun e => v ≫ e) he).trans hc
  have hf := frameIso_hom r c a.left (flagChartMorphism G g).left
    (flagCharacterModule G chi) h (flagCharacterPullbackIso G g chi a.left)
  exact hf.trans (congrArg (fun e => (pullbackComp c r).hom.app (flagCharacterModule G chi) ≫ e) hv)

private theorem evaluation_base_change {L : Scheme.{u}} (chi : G.characters)
    (P Q : Over (Spec (.of K))) (f : Q ⟶ P) (c : P.left ⟶ L)
    (r : L ⟶ (flagVariety G).scheme) (k : Q.left ⟶ L) (h : f.left ≫ c = k)
    (a : P ⟶ (reductiveVariety G).toOver)
    (ha : a.left ≫ flagQuotient G = c ≫ r) :
    (pullbackCongr h.symm).hom.app ((pullback r).obj (flagCharacterModule G chi)) ≫
        pullCoframe f.left c ((pullback r).obj (flagCharacterModule G chi))
          ((pullbackComp c r).hom.app (flagCharacterModule G chi) ≫
            characterFrameEvaluation G chi P (c ≫ r) a ha) =
      (pullbackComp k r).hom.app (flagCharacterModule G chi) ≫
        characterFrameEvaluation G chi Q (k ≫ r) (f ≫ a)
          (((Category.assoc f.left a.left (flagQuotient G)).trans
            (congrArg (fun t => f.left ≫ t) ha)).trans
              ((Category.assoc f.left c r).symm.trans (congrArg (fun t => t ≫ r) h))) := by
  let he := (Category.assoc f.left c r).symm.trans (congrArg (fun t => t ≫ r) h)
  let hq := ((Category.assoc f.left a.left (flagQuotient G)).trans
    (congrArg (fun t => f.left ≫ t) ha)).trans he
  have hb := base_change_at f.left c r k h (flagCharacterModule G chi)
    (characterFrameEvaluation G chi P (c ≫ r) a ha)
  have hp := characterFrameEvaluation_pullback G chi Q P f (c ≫ r) a ha
  have hc := characterFrameEvaluation_congr G chi Q he.symm (f ≫ a) hq
  have ht := (congrArg (fun t => (pullbackCongr he.symm).hom.app
    (flagCharacterModule G chi) ≫ t) hp).trans hc
  exact hb.trans (congrArg (fun t =>
    (pullbackComp k r).hom.app (flagCharacterModule G chi) ≫ t) ht)

private theorem evaluation_match {L : Scheme.{u}} (chi : G.characters)
    (P Q : Over (Spec (.of K))) (f₀ f₁ : Q ⟶ P) (c₀ c₁ : P.left ⟶ L)
    (r : L ⟶ (flagVariety G).scheme) (h : f₁.left ≫ c₁ = f₀.left ≫ c₀)
    (a₀ a₁ : P ⟶ (reductiveVariety G).toOver)
    (ha₀ : a₀.left ≫ flagQuotient G = c₀ ≫ r)
    (ha₁ : a₁.left ≫ flagQuotient G = c₁ ≫ r)
    (b : Q ⟶ (borelVariety G).toOver)
    (hab : f₀ ≫ a₀ = (f₁ ≫ a₁) * (b ≫ borelInclusion G)) :
    pullCoframe f₀.left c₀ ((pullback r).obj (flagCharacterModule G chi))
        ((pullbackComp c₀ r).hom.app (flagCharacterModule G chi) ≫
          characterFrameEvaluation G chi P (c₀ ≫ r) a₀ ha₀) =
      (pullbackCongr h.symm).hom.app ((pullback r).obj (flagCharacterModule G chi)) ≫
        pullCoframe f₁.left c₁ ((pullback r).obj (flagCharacterModule G chi))
          ((pullbackComp c₁ r).hom.app (flagCharacterModule G chi) ≫
            characterFrameEvaluation G chi P (c₁ ≫ r) a₁ ha₁) ≫
        globalSectionsSmul (SheafOfModules.unit Q.left.ringCatSheaf)
          (b.left.appTop (borelCharacterSection G chi)) := by
  let k := f₀.left ≫ c₀
  let M := flagCharacterModule G chi
  let s := globalSectionsSmul (SheafOfModules.unit Q.left.ringCatSheaf)
    (b.left.appTop (borelCharacterSection G chi))
  let q₀ := ((Category.assoc f₀.left a₀.left (flagQuotient G)).trans
    (congrArg (fun t => f₀.left ≫ t) ha₀)).trans (Category.assoc f₀.left c₀ r).symm
  let q₁ := ((Category.assoc f₁.left a₁.left (flagQuotient G)).trans
    (congrArg (fun t => f₁.left ≫ t) ha₁)).trans
      ((Category.assoc f₁.left c₁ r).symm.trans (congrArg (fun t => t ≫ r) h))
  have h₀ := evaluation_base_change G chi P Q f₀ c₀ r k rfl a₀ ha₀
  have h₁ := evaluation_base_change G chi P Q f₁ c₁ r k h a₁ ha₁
  have hl : pullCoframe f₀.left c₀ ((pullback r).obj M)
      ((pullbackComp c₀ r).hom.app M ≫ characterFrameEvaluation G chi P (c₀ ≫ r) a₀ ha₀) =
      (pullbackComp k r).hom.app M ≫ characterFrameEvaluation G chi Q (k ≫ r)
        (f₀ ≫ a₀) q₀ := by
    let z := pullCoframe f₀.left c₀ ((pullback r).obj M)
      ((pullbackComp c₀ r).hom.app M ≫ characterFrameEvaluation G chi P (c₀ ≫ r) a₀ ha₀)
    exact (Category.id_comp z).symm.trans h₀
  have hs := characterFrameEvaluation_rule G chi Q (k ≫ r)
    (f₀ ≫ a₀) (f₁ ≫ a₁) b q₀ q₁ hab
  have hp := congrArg (fun t => (pullbackComp k r).hom.app M ≫ t) hs
  have hr := congrArg (fun t => t ≫ s) h₁.symm
  exact hl.trans (hp.trans ((Category.assoc _ _ s).symm.trans
    (hr.trans (Category.assoc _ _ s))))

private theorem cancel_middle_iso {C : Type v} [Category.{w} C]
    {P A B D Q T : C} (a : P ⟶ A) (b : A ⟶ B) (e : B ≅ D)
    (c : P ⟶ Q) (q : Q ⟶ D) (t : D ⟶ T)
    (h : a ≫ b = c ≫ q ≫ e.inv) : a ≫ b ≫ e.hom ≫ t = c ≫ q ≫ t := by
  simpa only [Category.assoc, Iso.inv_hom_id_assoc] using
    congrArg (fun x => x ≫ e.hom ≫ t) h

private theorem three_pullback_coframe {X Y Z W : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W) (M : W.Modules)
    {T : X.Modules} (e : (Scheme.Modules.pullback (f ≫ g ≫ h)).obj M ⟶ T) :
    (Scheme.Modules.pullbackComp f g).inv.app ((Scheme.Modules.pullback h).obj M) ≫
        (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackComp g h).hom.app M) ≫
        (Scheme.Modules.pullbackComp f (g ≫ h)).hom.app M ≫ e =
      (Scheme.Modules.pullbackComp (f ≫ g) h).hom.app M ≫
        (Scheme.Modules.pullbackCongr (Category.assoc f g h)).hom.app M ≫ e := by
  have hc : (Scheme.Modules.pullbackCongr (Category.assoc f g h)).hom.app M =
      eqToHom (congrArg (fun t : X ⟶ W => (Scheme.Modules.pullback t).obj M)
        (Category.assoc f g h)) := iso_app_eqToHom _ M
  have ht := Scheme.Modules.pullbackComp_inv_app_comp_pullback_map_pullbackComp_hom_app f g h M
  have hv := congrArg (fun t =>
    (Scheme.Modules.pullbackComp (f ≫ g) h).hom.app M ≫ t ≫
      (Scheme.Modules.pullbackComp f (g ≫ h)).inv.app M) hc.symm
  exact cancel_middle_iso
    ((Scheme.Modules.pullbackComp f g).inv.app ((Scheme.Modules.pullback h).obj M))
    ((Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackComp g h).hom.app M))
    ((Scheme.Modules.pullbackComp f (g ≫ h)).app M)
    ((Scheme.Modules.pullbackComp (f ≫ g) h).hom.app M)
    ((Scheme.Modules.pullbackCongr (Category.assoc f g h)).hom.app M) e (ht.trans hv)


/-- Reindex a coframe identity along an equality of module objects. -/
theorem component_reindex {C D : Type*} [Category C] [Category D]
    {F H : C ⥤ D} (E : F ≅ H) {N N₀ : C} (hN : N = N₀) {T : D}
    (frame : H.obj N ⟶ T) (tail : F.obj N ⟶ T)
    (hf : frame = E.inv.app N ≫ tail) :
    eqToHom (congrArg H.obj hN.symm) ≫ frame =
      E.inv.app N₀ ≫ eqToHom (congrArg F.obj hN.symm) ≫ tail := by
  subst N₀
  simpa only [eqToHom_refl, Category.id_comp] using hf


/-- Identity casts can be removed from a coframe comparison. -/
theorem strip_component_casts {C : Type*} [Category C] {P A T : C}
    {rho : P ⟶ P} {sigma : A ⟶ A} {frame : P ⟶ T}
    {alpha : P ⟶ A} {tail : A ⟶ T}
    (hrho : rho = 𝟙 P) (hsigma : sigma = 𝟙 A)
    (hc : rho ≫ frame = alpha ≫ sigma ≫ tail) : frame = alpha ≫ tail := by
  rw [hrho, hsigma] at hc
  simpa only [Category.id_comp] using hc

/-- Transport an isomorphism component through equal functors. -/
theorem iso_app_reindex {C D : Type*} [Category C] [Category D]
    {F H F₀ H₀ : C ⥤ D} (hF : F = F₀) (hH : H = H₀)
    (E : F ≅ H) (E₀ : F₀ ≅ H₀) (hE : HEq E E₀) (M : C) {T : D}
    (raw : F.obj M ⟶ T) (ev : H.obj M ⟶ T)
    (hr : raw = E.hom.app M ≫ ev) :
    eqToHom (congrArg (fun L : C ⥤ D => L.obj M) hF.symm) ≫ raw =
      E₀.hom.app M ≫ eqToHom (congrArg (fun L : C ⥤ D => L.obj M) hH.symm) ≫ ev := by
  subst F₀
  subst H₀
  cases hE
  simpa only [eqToHom_refl, Category.id_comp] using hr

/-- Combine successive pullback comparisons with associativity. -/
theorem coframe_to_assoc {X Y Z W : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W) (M : W.Modules) {T : X.Modules}
    (frame : (Scheme.Modules.pullback (f ≫ g)).obj
      ((Scheme.Modules.pullback h).obj M) ⟶ T)
    (raw : (Scheme.Modules.pullback f).obj
      ((Scheme.Modules.pullback (g ≫ h)).obj M) ⟶ T)
    (ev : (Scheme.Modules.pullback (f ≫ g ≫ h)).obj M ⟶ T)
    (hframe : frame =
      (Scheme.Modules.pullbackComp f g).inv.app ((Scheme.Modules.pullback h).obj M) ≫
      (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackComp g h).hom.app M) ≫ raw)
    (hraw : raw = (Scheme.Modules.pullbackComp f (g ≫ h)).hom.app M ≫ ev) :
    frame = (Scheme.Modules.pullbackComp (f ≫ g) h).hom.app M ≫
      (Scheme.Modules.pullbackCongr (Category.assoc f g h)).hom.app M ≫ ev := by
  rw [hframe, hraw, three_pullback_coframe f g h M ev]



end SchubertGeometry.CharacterLine.CoframeTransport
