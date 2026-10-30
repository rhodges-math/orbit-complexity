import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.MatchingFrameOverlaps
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.MatchingFrameSections
import OrbitComplexity.FrobeniusSplitting.Normality.Assembly.FrameScalarTransport
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Matching coframes under affine refinement

The same global matching coordinate determines the coframe on an original
affine member and on every refined intersection. Adjunction carries that
coordinate through the whole chart triangle. Retained units then give the
refinement equation for all adjusted character powers and their inverse frames.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open FrobeniusSplitting FrobeniusSplitting.CharacterLine
open FrobeniusSplitting.RetainedCharacter

noncomputable section
universe u v w

namespace SchubertGeometry.RetainedCharacter

open private matching_frame_adjunct scalar_power_hom
  from OrbitComplexity.SchubertGeometry.Frobenius.Assembly.MatchingFrameOverlaps
open private mapped_frame_scalar coefficient_power_scalar
  from OrbitComplexity.SchubertGeometry.Frobenius.Assembly.RetainedLocalFrames
open private relativeFunctionsMap_comp
  from OrbitComplexity.FrobeniusSplitting.Modules.RelativeFunctions
open private singletonIndex singletonArrow
  from OrbitComplexity.FrobeniusSplitting.Modules.MatchingModule
open private rangeSection
  from OrbitComplexity.SchubertGeometry.Frobenius.Assembly.MatchingFrameSections
open private originalLeg originalLegOpen
  from OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.UnitFrames

private def framePullbackHom {S : Scheme.{u}} {X Y : Over S}
    (k : X ⟶ Y) (M : S.Modules)
    (e : (Scheme.Modules.pullback Y.hom).obj M ⟶ SheafOfModules.unit Y.left.ringCatSheaf) :
    (Scheme.Modules.pullback X.hom).obj M ⟶ SheafOfModules.unit X.left.ringCatSheaf :=
  (Scheme.Modules.pullbackCongr k.w.symm).hom.app M ≫
    (Scheme.Modules.pullbackComp k.left Y.hom).inv.app M ≫
    (Scheme.Modules.pullback k.left).map e ≫ (Scheme.Modules.pullbackObjUnitIso k.left).hom

private def framePullbackIso {S : Scheme.{u}} {X Y : Over S}
    (k : X ⟶ Y) (M : S.Modules)
    (e : (Scheme.Modules.pullback Y.hom).obj M ≅ SheafOfModules.unit Y.left.ringCatSheaf) :
    (Scheme.Modules.pullback X.hom).obj M ≅ SheafOfModules.unit X.left.ringCatSheaf :=
  (Scheme.Modules.pullbackCongr k.w.symm).app M ≪≫
    ((Scheme.Modules.pullbackComp k.left Y.hom).app M).symm ≪≫
      (Scheme.Modules.pullback k.left).mapIso e ≪≫ Scheme.Modules.pullbackObjUnitIso k.left

private theorem comp_four {C : Type v} [Category.{w} C]
    {A B D E F : C} (a : A ⟶ B) (b : B ⟶ D) (c : D ⟶ E) (d : E ⟶ F) :
    (a ≫ (b ≫ c)) ≫ d = a ≫ b ≫ c ≫ d := by
  simp only [Category.assoc]

private theorem framePullback_adjunct {S : Scheme.{u}} {X Y : Over S}
    (k : X ⟶ Y) (M : S.Modules)
    (e : (Scheme.Modules.pullback Y.hom).obj M ⟶ SheafOfModules.unit Y.left.ringCatSheaf) :
    (Scheme.Modules.pullbackPushforwardAdjunction X.hom).homEquiv M
        (SheafOfModules.unit X.left.ringCatSheaf) (framePullbackHom k M e) =
      (Scheme.Modules.pullbackPushforwardAdjunction Y.hom).homEquiv M
          (SheafOfModules.unit Y.left.ringCatSheaf) e ≫ relativeFunctionsMap S k := by
  let U := SheafOfModules.unit X.left.ringCatSheaf
  let t := (Scheme.Modules.pullbackComp k.left Y.hom).inv.app M ≫
    (Scheme.Modules.pullback k.left).map e ≫ (Scheme.Modules.pullbackObjUnitIso k.left).hom
  have hc := pullbackHomEquiv_congr k.w M U t
  have hf := frameHomEquiv_comp k.left Y.hom M e
  exact hc.trans ((congrArg (fun f => f ≫
    (Scheme.Modules.pushforwardCongr k.w).hom.app U) hf).trans (by
      dsimp only [relativeFunctionsMap]
      exact comp_four _ _ _ _))

private theorem framePullback_smul {S : Scheme.{u}} {X Y : Over S}
    (k : X ⟶ Y) (M : S.Modules)
    (e : (Scheme.Modules.pullback Y.hom).obj M ⟶ SheafOfModules.unit Y.left.ringCatSheaf)
    (r : Γ(Y.left, ⊤)) (s : Γ(X.left, ⊤)) (h : k.left.appTop r = s) :
    framePullbackHom k M
        (e ≫ Scheme.Modules.globalSectionsSmul (SheafOfModules.unit Y.left.ringCatSheaf) r) =
      framePullbackHom k M e ≫
        Scheme.Modules.globalSectionsSmul (SheafOfModules.unit X.left.ringCatSheaf) s := by
  let v := (Scheme.Modules.pullbackCongr k.w.symm).hom.app M ≫
    (Scheme.Modules.pullbackComp k.left Y.hom).inv.app M
  let unit := (Scheme.Modules.pullbackObjUnitIso k.left).hom
  have hm := (congrArg (fun f => f ≫ unit)
    (Scheme.Modules.pullback_map_globalSectionsSmul k.left
      (SheafOfModules.unit Y.left.ringCatSheaf) r)).trans
      (Scheme.Modules.globalSectionsSmul_naturality unit (k.left.appTop r))
  have hs := hm.trans (congrArg
    (fun a => unit ≫ Scheme.Modules.globalSectionsSmul (SheafOfModules.unit X.left.ringCatSheaf) a)
        h)
  exact mapped_frame_scalar (Scheme.Modules.pullback k.left) v e
    (Scheme.Modules.globalSectionsSmul (SheafOfModules.unit Y.left.ringCatSheaf) r) unit
    (Scheme.Modules.globalSectionsSmul (SheafOfModules.unit X.left.ringCatSheaf) s) hs

private theorem rangeFrame_hom_eq {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j] (M : Y.Modules)
    (e f : SheafOfModules.unit X.ringCatSheaf ⟶ (Scheme.Modules.pullback j).obj M)
    (h : e = f) :
    rangeSection j M ((e.val.app (op ⊤)).hom (1 : Γ(X, ⊤))) =
      rangeSection j M ((f.val.app (op ⊤)).hom (1 : Γ(X, ⊤))) :=
  congrArg (fun q : SheafOfModules.unit X.ringCatSheaf ⟶
    (Scheme.Modules.pullback j).obj M =>
      rangeSection j M ((q.val.app (op ⊤)).hom (1 : Γ(X, ⊤)))) h

private theorem cocone_map_comp {I : Type*} {C : Type*} [Category I] [Category C]
    (F : I ⥤ C) (c : Cocone F) {i j k : I} (f : i ⟶ j) (g : j ⟶ k)
    (a : Over.mk (c.ι.app i) ⟶ Over.mk (c.ι.app j))
    (b : Over.mk (c.ι.app j) ⟶ Over.mk (c.ι.app k))
    (d : Over.mk (c.ι.app i) ⟶ Over.mk (c.ι.app k))
    (ha : a.left = F.map f) (hb : b.left = F.map g) (hd : d.left = F.map (f ≫ g)) :
    a ≫ b = d := by
  apply Over.OverMorphism.ext
  exact (congrArg₂ (fun a b => a ≫ b) ha hb).trans ((F.map_comp f g).symm.trans hd.symm)

private theorem coordinate_refinement {C : Type v} [Category.{w} C]
    {M A B D : C} (a : M ⟶ A) (b : A ⟶ B) (c : B ⟶ D) (d : A ⟶ D)
    (x : M ⟶ B) (y : M ⟶ D) (hx : x = a ≫ b) (hy : y = a ≫ d)
    (hd : b ≫ c = d) : x ≫ c = y := by
  rw [hx, Category.assoc, hd, ← hy]

private theorem adjustment_transport {C D : Type v} [Category.{w} C] [Category.{w} D]
    {M N : C} {P Q : D} (T : (M ⟶ N) → (P ⟶ Q)) (e e' : M ⟶ N) (r : N ⟶ N)
    (f f' : P ⟶ Q) (s : Q ⟶ Q)
    (he : e' = e ≫ r) (hf : f' = f ≫ s)
    (ht : T (e ≫ r) = T e ≫ s) (h : T e = f) : T e' = f' := by
  exact (congrArg T he).trans (ht.trans ((congrArg (fun a => a ≫ s) h).trans hf.symm))

variable {R J : Type u} [CommRing R]
    (N : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} R)
    [hopen : ∀ {s t} (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (N.map f).hom.toRingHom))]
    [hdir : ((N.op ⋙ algSpec (.of R) ⋙ Over.forget (Spec (.of R))) ⋙
      Scheme.forget).IsLocallyDirected]
    (cN : Cocone (N.op ⋙ algSpec (.of R))) (hcN : IsColimit cN)

omit hopen hdir in
private theorem nodeMap_singleton {s t : {s : Finset J // s.Nonempty}}
    (f : s ⟶ t) (j : J) (hj : j ∈ s.val) :
    nodeMap N cN f ≫ nodeMap N cN (singletonArrow s j hj) =
      nodeMap N cN (singletonArrow t j ((leOfHom f) hj)) := by
  let D := N.op ⋙ algSpec (.of R) ⋙ Over.forget (Spec (.of R))
  let C : Cocone D := (Over.forget (Spec (.of R))).mapCocone cN
  have hc := cocone_map_comp D C f.op (singletonArrow s j hj).op
    (nodeMap N cN f) (nodeMap N cN (singletonArrow s j hj))
    (nodeMap N cN (singletonArrow s j hj ≫ f)) rfl rfl rfl
  have h : singletonArrow s j hj ≫ f = singletonArrow t j ((leOfHom f) hj) :=
    Subsingleton.elim _ _
  exact hc.trans (congrArg (fun a => nodeMap N cN a) h)

variable (delta : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val)
      (k : J) (_ : k ∈ s.val), (N.obj s)ˣ) (n : ℕ)
    (hco : ∀ s j hj k hk l hl,
      delta s j hj l hl = delta s k hk l hl * delta s j hj k hk)
    (hn : ∀ s t (f : s ⟶ t) j hj k hk,
      Units.map (N.map f).hom.toMonoidHom (delta s j hj k hk) =
        delta t j ((leOfHom f) hj) k ((leOfHom f) hk))

/-- Refining an affine member pulls its matching coframe to the coframe with
the same selected index on the unchanged refined member. -/
theorem matchingFrame_refinement {s t : {s : Finset J // s.Nonempty}}
    (f : s ⟶ t) (j : J) (hj : j ∈ s.val) :
    framePullbackHom (nodeMap N cN f) (matchingModule N cN delta n)
        (localCharacterTrivialization N cN hcN delta n hco hn s j hj).hom =
      (localCharacterTrivialization N cN hcN delta n hco hn t j ((leOfHom f) hj)).hom := by
  let M := matchingModule N cN delta n
  let es := localCharacterTrivialization N cN hcN delta n hco hn s j hj
  let et := localCharacterTrivialization N cN hcN delta n hco hn t j ((leOfHom f) hj)
  have hs := matching_frame_adjunct N cN hcN delta n hco hn s j hj
  have ht := matching_frame_adjunct N cN hcN delta n hco hn t j ((leOfHom f) hj)
  have hnode := nodeMap_singleton N cN f j hj
  have hmap := relativeFunctionsMap_comp cN.pt.left
    (nodeMap N cN f) (nodeMap N cN (singletonArrow s j hj))
  have hr := hmap.symm.trans (congrArg
    (fun a : node N cN t ⟶ node N cN (singletonIndex j) =>
      relativeFunctionsMap cN.pt.left a) hnode)
  have hcoords := coordinate_refinement (coordinate N cN delta n j)
    (relativeFunctionsMap cN.pt.left (nodeMap N cN (singletonArrow s j hj)))
    (relativeFunctionsMap cN.pt.left (nodeMap N cN f))
    (relativeFunctionsMap cN.pt.left (nodeMap N cN (singletonArrow t j ((leOfHom f) hj))))
    ((Scheme.Modules.pullbackPushforwardAdjunction (originalLeg N cN s)).homEquiv M
      (SheafOfModules.unit (Spec (.of (N.obj s))).ringCatSheaf) es.hom)
    ((Scheme.Modules.pullbackPushforwardAdjunction (originalLeg N cN t)).homEquiv M
      (SheafOfModules.unit (Spec (.of (N.obj t))).ringCatSheaf) et.hom) hs ht hr
  apply ((Scheme.Modules.pullbackPushforwardAdjunction (originalLeg N cN t)).homEquiv M
    (SheafOfModules.unit (Spec (.of (N.obj t))).ringCatSheaf)).injective
  exact (framePullback_adjunct (nodeMap N cN f) M es.hom).trans hcoords

/-- The adjusted matching coframe is natural under refinement once the
specified retained unit is carried by the original coefficient map. -/
theorem adjustedMatchingFrame_refinement {s t : {s : Finset J // s.Nonempty}}
    (f : s ⟶ t) (j : J) (hj : j ∈ s.val) (d : (N.obj s)ˣ) (e : (N.obj t)ˣ)
    (hd : Units.map (N.map f).hom.toMonoidHom d = e) :
    framePullbackHom (nodeMap N cN f) (matchingModule N cN delta n)
        (adjustedMatchingFrame N cN hcN delta n hco hn s j hj d).hom =
      (adjustedMatchingFrame N cN hcN delta n hco hn t j ((leOfHom f) hj) e).hom := by
  let M := matchingModule N cN delta n
  let Us := SheafOfModules.unit (Spec (.of (N.obj s))).ringCatSheaf
  let Ut := SheafOfModules.unit (Spec (.of (N.obj t))).ringCatSheaf
  let r := (Scheme.ΓSpecIso (.of (N.obj s))).inv ((d : N.obj s) ^ n)
  let q := (Scheme.ΓSpecIso (.of (N.obj t))).inv ((e : N.obj t) ^ n)
  let es := localCharacterTrivialization N cN hcN delta n hco hn s j hj
  let et := localCharacterTrivialization N cN hcN delta n hco hn t j ((leOfHom f) hj)
  have hv : (N.map f).hom.toRingHom (d : N.obj s) = (e : N.obj t) :=
    congrArg (fun a : (N.obj t)ˣ => (a : N.obj t)) hd
  have hc := coefficient_power_scalar (CommRingCat.ofHom (N.map f).hom.toRingHom)
    (d : N.obj s) (e : N.obj t) hv n
  have hs : (adjustedMatchingFrame N cN hcN delta n hco hn s j hj d).hom =
      es.hom ≫ Scheme.Modules.globalSectionsSmul Us r :=
    congrArg (fun a => es.hom ≫ a) (scalar_power_hom (N.obj s) Us d n)
  have ht : (adjustedMatchingFrame N cN hcN delta n hco hn t j ((leOfHom f) hj) e).hom =
      et.hom ≫ Scheme.Modules.globalSectionsSmul Ut q :=
    congrArg (fun a => et.hom ≫ a) (scalar_power_hom (N.obj t) Ut e n)
  exact adjustment_transport (framePullbackHom (nodeMap N cN f) M) es.hom
    (adjustedMatchingFrame N cN hcN delta n hco hn s j hj d).hom
    (Scheme.Modules.globalSectionsSmul Us r) et.hom
    (adjustedMatchingFrame N cN hcN delta n hco hn t j ((leOfHom f) hj) e).hom
    (Scheme.Modules.globalSectionsSmul Ut q) hs ht
    (framePullback_smul (nodeMap N cN f) M es.hom r q hc)
    (matchingFrame_refinement N cN hcN delta n hco hn f j hj)

/-- The inverse adjusted coframes have the same refinement equation, so their
line frames agree before any open-range section transport is applied. -/
theorem adjustedMatchingFrameInv_refine {s t : {s : Finset J // s.Nonempty}}
    (f : s ⟶ t) (j : J) (hj : j ∈ s.val) (d : (N.obj s)ˣ) (e : (N.obj t)ˣ)
    (hd : Units.map (N.map f).hom.toMonoidHom d = e) :
    (framePullbackIso (nodeMap N cN f) (matchingModule N cN delta n)
      (adjustedMatchingFrame N cN hcN delta n hco hn s j hj d)).inv =
        (adjustedMatchingFrame N cN hcN delta n hco hn t j ((leOfHom f) hj) e).inv := by
  have h : framePullbackIso (nodeMap N cN f) (matchingModule N cN delta n)
      (adjustedMatchingFrame N cN hcN delta n hco hn s j hj d) =
        adjustedMatchingFrame N cN hcN delta n hco hn t j ((leOfHom f) hj) e :=
    Iso.ext (adjustedMatchingFrame_refinement N cN hcN delta n hco hn f j hj d e hd)
  exact congrArg (fun E : (Scheme.Modules.pullback (originalLeg N cN t)).obj
      (matchingModule N cN delta n) ≅ SheafOfModules.unit (Spec (.of (N.obj t))).ringCatSheaf =>
    E.inv) h

/-- The incoming adjusted inverse coframe gives the matching line section
on the refined open range after the whole coframe equality is transported. -/
theorem adjustedMatchingFrame_range_refine {s t : {s : Finset J // s.Nonempty}}
    (f : s ⟶ t) (j : J) (hj : j ∈ s.val) (d : (N.obj s)ˣ) (e : (N.obj t)ˣ)
    (hd : Units.map (N.map f).hom.toMonoidHom d = e) :
    @rangeSection _ _ (originalLeg N cN t) (originalLegOpen N cN hcN t)
        (matchingModule N cN delta n)
        (((framePullbackIso (nodeMap N cN f) (matchingModule N cN delta n)
          (adjustedMatchingFrame N cN hcN delta n hco hn s j hj d)).inv.val.app
            (op ⊤)).hom (1 : Γ(Spec (.of (N.obj t)), ⊤))) =
      retainedMatchingFrameSection N cN hcN delta n hco hn t j ((leOfHom f) hj) e := by
  exact @rangeFrame_hom_eq _ _ (originalLeg N cN t) (originalLegOpen N cN hcN t)
    (matchingModule N cN delta n)
    (framePullbackIso (nodeMap N cN f) (matchingModule N cN delta n)
      (adjustedMatchingFrame N cN hcN delta n hco hn s j hj d)).inv
    (adjustedMatchingFrame N cN hcN delta n hco hn t j ((leOfHom f) hj) e).inv
    (adjustedMatchingFrameInv_refine N cN hcN delta n hco hn f j hj d e hd)

end SchubertGeometry.RetainedCharacter
