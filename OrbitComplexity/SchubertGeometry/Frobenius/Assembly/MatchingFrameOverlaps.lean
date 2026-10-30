import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.MatchingCoframeEvaluation
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.RetainedLocalFrames
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Matching coframes on intersections

The matching projection equation determines the orientation of the local
coframe transition. Multiplying those coframes by the retained units then
constructs the transition at every character power. Inverting the coframes
gives the inverse transition for the line frames.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open FrobeniusSplitting.CharacterLine FrobeniusSplitting.RetainedCharacter

noncomputable section
universe u v w

namespace SchubertGeometry.RetainedCharacter

open private local_character_hom selected_pullback_adjunct
  from OrbitComplexity.SchubertGeometry.Frobenius.Assembly.MatchingCoframeEvaluation
open private unitFunctions selectedFunctionsIso
  from OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.UnitTrivialization
open private originalLeg originalLegOpen frameInto
  from OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.UnitFrames
open private coefficientSection singletonArrow
  from OrbitComplexity.FrobeniusSplitting.Modules.MatchingModule
open private scalarIso
  from OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.LiftEvaluation
open private affine_smul_power
  from OrbitComplexity.SchubertGeometry.Frobenius.Assembly.RetainedLocalFrames

private theorem adjunct_composite {C D : Type v} [Category.{w} C] [Category.{w} D]
    (F : C ⥤ D) (R : D ⥤ C) (adj : F ⊣ R) {M N : C} {U : D}
    (d : M ⟶ N) (e : F.obj N ⟶ U)
    (t : F.obj M ⟶ U) (ht : t = F.map d ≫ e) :
    adj.homEquiv M U t = d ≫ adj.homEquiv N U e :=
  (congrArg (adj.homEquiv M U) ht).trans
    (adj.homEquiv_naturality_left d e)

private def coframeChange {X : Scheme.{u}} {M U : X.Modules}
    (e f : M ≅ U) (a : Γ(X, ⊤)) : Prop :=
  e.hom = f.hom ≫ Scheme.Modules.globalSectionsSmul U a

private def frameValueRatio {X : Scheme.{u}} {M U : X.Modules}
    (e f : U ⟶ M) (a : Γ(X, ⊤)) (one : Γ(U, ⊤)) : Prop :=
  (Scheme.Modules.Hom.app e ⊤).hom one =
    a • (Scheme.Modules.Hom.app f ⊤).hom one

private theorem coframe_from_adjunct {C D : Type v} [Category.{w} C] [Category.{w} D]
    (F : C ⥤ D) (R : D ⥤ C) (adj : F ⊣ R) {M : C} {U : D}
    (e f : F.obj M ⟶ U) (a b : M ⟶ R.obj U) (g : U ⟶ U)
    (he : adj.homEquiv M U e = a) (hf : adj.homEquiv M U f = b)
    (hab : a = b ≫ R.map g) : e = f ≫ g := by
  apply (adj.homEquiv M U).injective
  have hfg : adj.homEquiv M U (f ≫ g) = b ≫ R.map g :=
    (adj.homEquiv_naturality_right f g).trans (congrArg (fun k => k ≫ R.map g) hf)
  exact he.trans (hab.trans hfg.symm)

private theorem matching_adjunct_rule {C : Type v} [Category.{w} C]
    {M A U : C} (a : M ⟶ U) (c : M ⟶ A) (d : A ⟶ U)
    (r q : U ⟶ U) (b : M ⟶ U)
    (h : a = c ≫ d ≫ r) (hb : b = c ≫ d) (hr : r = q) : a = b ≫ q := by
  exact h.trans ((Category.assoc c d r).symm.trans
    (congrArg₂ (fun k l => k ≫ l) hb.symm hr))

private theorem adjusted_coframe {C : Type v} [Category.{w} C]
    {M U : C} (e f : M ⟶ U) (a b c d z : U ⟶ U)
    (he : e = f ≫ a) (ha : a ≫ b = z) (hc : c ≫ d = z) :
    e ≫ b = (f ≫ c) ≫ d := by
  calc
    _ = f ≫ z := by rw [he, Category.assoc, ha]
    _ = _ := by rw [Category.assoc, hc]

private theorem coframe_inverse {C : Type v} [Category.{w} C]
    {M U : C} (e f : M ≅ U) (a : U ≅ U)
    (h : e.hom = f.hom ≫ a.hom) : e.inv = a.inv ≫ f.inv := by
  have hi : e = f ≪≫ a := Iso.ext h
  exact congrArg (fun k : M ≅ U => k.inv) hi

private theorem unit_adjustment {A : Type u} [CommRing A] (a b c : Aˣ) :
    b * (c * a * b⁻¹) = c * a := by
  calc
    _ = (c * a) * (b * b⁻¹) := by ac_rfl
    _ = _ := by rw [mul_inv_cancel, mul_one]

private theorem scalar_power_hom (A : Type u) [CommRing A]
    (M : (Spec (.of A)).Modules) (d : Aˣ) (n : ℕ) :
    (scalarIso M (Units.map (Scheme.ΓSpecIso (.of A)).inv.hom.toMonoidHom (d ^ n))).hom =
      Scheme.Modules.globalSectionsSmul M ((Scheme.ΓSpecIso (.of A)).inv.hom ((d : A) ^ n)) := by
  apply congrArg (Scheme.Modules.globalSectionsSmul M)
  change (Scheme.ΓSpecIso (.of A)).inv.hom ((d ^ n : Aˣ) : A) = _
  exact congrArg (fun a : A => (Scheme.ΓSpecIso (.of A)).inv.hom a)
    (Units.val_pow_eq_pow_val d n)

private theorem scalar_top {X : Scheme.{u}} (L : X.Modules)
    (a : Γ(X, ⊤)) (x : Γ(L, ⊤)) :
    ((Scheme.Modules.globalSectionsSmul L a).app ⊤).hom x = a • x := by
  rw [Scheme.Modules.globalSectionsSmul_app]
  change (L.smul (X.presheaf.map (𝟙 (op (⊤ : X.Opens))) a)).hom x = a • x
  rw [CategoryTheory.Functor.map_id]
  exact L.smul_apply a x

private theorem value_ratio_of_eq {X : Scheme.{u}} {M U : X.Modules}
    (e f : U ⟶ M) (a : Γ(X, ⊤)) (one : Γ(U, ⊤))
    (he : e = Scheme.Modules.globalSectionsSmul U a ≫ f) :
    frameValueRatio e f a one := by
  have h := he.trans (Scheme.Modules.globalSectionsSmul_naturality f a)
  exact (congrArg (fun g : U ⟶ M => (Scheme.Modules.Hom.app g ⊤).hom one) h).trans
    (scalar_top M a ((Scheme.Modules.Hom.app f ⊤).hom one))

variable {R J : Type u} [CommRing R]
    (N : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} R)
    [hopen : ∀ {s t} (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (N.map f).hom.toRingHom))]
    [hdir : ((N.op ⋙ algSpec (.of R) ⋙ Over.forget (Spec (.of R))) ⋙
      Scheme.forget).IsLocallyDirected]
    (cN : Cocone (N.op ⋙ algSpec (.of R))) (hcN : IsColimit cN)
    (delta : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val)
      (k : J) (_ : k ∈ s.val), (N.obj s)ˣ) (n : ℕ)
    (hco : ∀ s j hj k hk l hl,
      delta s j hj l hl = delta s k hk l hl * delta s j hj k hk)
    (hn : ∀ s t (f : s ⟶ t) j hj k hk,
      Units.map (N.map f).hom.toMonoidHom (delta s j hj k hk) =
        delta t j ((leOfHom f) hj) k ((leOfHom f) hk))

private theorem matching_frame_adjunct (s : {s : Finset J // s.Nonempty})
    (j : J) (hj : j ∈ s.val) :
    (Scheme.Modules.pullbackPushforwardAdjunction (originalLeg N cN s)).homEquiv
        (matchingModule N cN delta n)
        (SheafOfModules.unit (Spec (.of (N.obj s))).ringCatSheaf)
        (localCharacterTrivialization N cN hcN delta n hco hn s j hj).hom =
      coordinate N cN delta n j ≫
        relativeFunctionsMap cN.pt.left (nodeMap N cN (singletonArrow s j hj)) := by
  have ht := local_character_hom N cN hcN delta n hco hn s j hj
  have he := selected_pullback_adjunct N cN hcN s j hj
  exact (adjunct_composite (Scheme.Modules.pullback (originalLeg N cN s))
    (Scheme.Modules.pushforward (originalLeg N cN s))
    (Scheme.Modules.pullbackPushforwardAdjunction (originalLeg N cN s))
    (M := matchingModule N cN delta n) (N := unitFunctions N cN j)
    (U := SheafOfModules.unit (Spec (.of (N.obj s))).ringCatSheaf)
    (coordinate N cN delta n j)
    ((@Scheme.Modules.restrictFunctorIsoPullback _ _ (originalLeg N cN s)
      (originalLegOpen N cN hcN s)).inv.app (unitFunctions N cN j) ≫
        (selectedFunctionsIso N cN hcN s j hj).hom)
    (localCharacterTrivialization N cN hcN delta n hco hn s j hj).hom ht).trans
      (congrArg (fun k => coordinate N cN delta n j ≫ k) he)

/-- The coframe with index j equals the coframe with index k followed by
multiplication by the matching unit from j to k at the full character power. -/
theorem matchingFrame_change (s : {s : Finset J // s.Nonempty})
    (j : J) (hj : j ∈ s.val) (k : J) (hk : k ∈ s.val) :
    coframeChange (X := (node N cN s).left)
      (localCharacterTrivialization N cN hcN delta n hco hn s j hj)
      (localCharacterTrivialization N cN hcN delta n hco hn s k hk)
      (coefficientSection N cN s ((delta s j hj k hk : N.obj s) ^ n)) := by
  let U : (node N cN s).left.Modules :=
    SheafOfModules.unit (Spec (.of (N.obj s))).ringCatSheaf
  let g := Scheme.Modules.globalSectionsSmul U
    (coefficientSection N cN s ((delta s j hj k hk : N.obj s) ^ n))
  have hj' := matching_frame_adjunct N cN hcN delta n hco hn s j hj
  have hk' := matching_frame_adjunct N cN hcN delta n hco hn s k hk
  have hr : relativeFunctionsSmul cN.pt.left (node N cN s)
      (coefficientSection N cN s ((delta s j hj k hk : N.obj s) ^ n)) =
      (Scheme.Modules.pushforward (originalLeg N cN s)).map g := rfl
  have hm := coordinate_matching N cN delta n s j hj k hk
  have hab := matching_adjunct_rule
    (coordinate N cN delta n j ≫
      relativeFunctionsMap cN.pt.left (nodeMap N cN (singletonArrow s j hj)))
    (coordinate N cN delta n k)
    (relativeFunctionsMap cN.pt.left (nodeMap N cN (singletonArrow s k hk)))
    (relativeFunctionsSmul cN.pt.left (node N cN s)
      (coefficientSection N cN s ((delta s j hj k hk : N.obj s) ^ n)))
    ((Scheme.Modules.pushforward (originalLeg N cN s)).map g)
    (coordinate N cN delta n k ≫
      relativeFunctionsMap cN.pt.left (nodeMap N cN (singletonArrow s k hk))) hm rfl hr
  let ej := (localCharacterTrivialization N cN hcN delta n hco hn s j hj).hom
  let ek := (localCharacterTrivialization N cN hcN delta n hco hn s k hk).hom
  let aj := coordinate N cN delta n j ≫
    relativeFunctionsMap cN.pt.left (nodeMap N cN (singletonArrow s j hj))
  let ak := coordinate N cN delta n k ≫
    relativeFunctionsMap cN.pt.left (nodeMap N cN (singletonArrow s k hk))
  have leaf := coframe_from_adjunct
    (Scheme.Modules.pullback (originalLeg N cN s))
    (Scheme.Modules.pushforward (originalLeg N cN s))
    (Scheme.Modules.pullbackPushforwardAdjunction (originalLeg N cN s))
    (M := matchingModule N cN delta n) (U := U)
  exact leaf ej ek aj ak g hj' hk' hab

/-- The matching coframe on an intersection is adjusted by its retained unit
to the same character power. -/
def adjustedMatchingFrame (s : {s : Finset J // s.Nonempty})
    (j : J) (hj : j ∈ s.val) (d : (N.obj s)ˣ) :
    (Scheme.Modules.pullback (originalLeg N cN s)).obj (matchingModule N cN delta n) ≅
      SheafOfModules.unit (Spec (.of (N.obj s))).ringCatSheaf :=
  localCharacterTrivialization N cN hcN delta n hco hn s j hj ≪≫
    scalarIso (SheafOfModules.unit (Spec (.of (N.obj s))).ringCatSheaf)
      (Units.map (Scheme.ΓSpecIso (.of (N.obj s))).inv.hom.toMonoidHom (d ^ n))

/-- The adjusted coframe ratio is delta times the first retained unit divided
by the second retained unit, raised to the full character power. -/
theorem adjustedMatchingFrame_change (s : {s : Finset J // s.Nonempty})
    (j : J) (hj : j ∈ s.val) (k : J) (hk : k ∈ s.val) (d e : (N.obj s)ˣ) :
    (adjustedMatchingFrame N cN hcN delta n hco hn s j hj d).hom =
      (adjustedMatchingFrame N cN hcN delta n hco hn s k hk e).hom ≫
        Scheme.Modules.globalSectionsSmul
          (SheafOfModules.unit (Spec (.of (N.obj s))).ringCatSheaf)
          ((Scheme.ΓSpecIso (.of (N.obj s))).inv.hom
            (((delta s j hj k hk * d * e⁻¹ : (N.obj s)ˣ) : N.obj s) ^ n)) := by
  let U := SheafOfModules.unit (Spec (.of (N.obj s))).ringCatSheaf
  let r := delta s j hj k hk
  let c := r * d * e⁻¹
  have hleft := scalar_power_hom (N.obj s) U d n
  have hright := scalar_power_hom (N.obj s) U e n
  have hc := congrArg (fun a : (N.obj s)ˣ => (a : N.obj s)) (unit_adjustment d e r)
  have hp := congrArg (fun a : N.obj s => Scheme.Modules.globalSectionsSmul U
    ((Scheme.ΓSpecIso (.of (N.obj s))).inv.hom (a ^ n))) hc
  have hs := adjusted_coframe
    (localCharacterTrivialization N cN hcN delta n hco hn s j hj).hom
    (localCharacterTrivialization N cN hcN delta n hco hn s k hk).hom
    (Scheme.Modules.globalSectionsSmul U ((Scheme.ΓSpecIso (.of (N.obj s))).inv.hom ((r : N.obj s) ^
        n)))
    (Scheme.Modules.globalSectionsSmul U ((Scheme.ΓSpecIso (.of (N.obj s))).inv.hom ((d : N.obj s) ^
        n)))
    (Scheme.Modules.globalSectionsSmul U ((Scheme.ΓSpecIso (.of (N.obj s))).inv.hom ((e : N.obj s) ^
        n)))
    (Scheme.Modules.globalSectionsSmul U ((Scheme.ΓSpecIso (.of (N.obj s))).inv.hom ((c : N.obj s) ^
        n)))
    (Scheme.Modules.globalSectionsSmul U
      ((Scheme.ΓSpecIso (.of (N.obj s))).inv.hom (((r : N.obj s) * (d : N.obj s)) ^ n)))
    (matchingFrame_change N cN hcN delta n hco hn s j hj k hk)
    (affine_smul_power (N.obj s) U (r : N.obj s) (d : N.obj s) n)
    ((affine_smul_power (N.obj s) U (e : N.obj s) (c : N.obj s) n).trans hp)
  change ((localCharacterTrivialization N cN hcN delta n hco hn s j hj).hom ≫
    (scalarIso U (Units.map (Scheme.ΓSpecIso (.of (N.obj s))).inv.hom.toMonoidHom (d ^ n))).hom) =
      ((localCharacterTrivialization N cN hcN delta n hco hn s k hk).hom ≫
        (scalarIso U (Units.map (Scheme.ΓSpecIso (.of (N.obj s))).inv.hom.toMonoidHom (e ^ n))).hom)
            ≫ _
  rw [hleft, hright]
  exact hs

/-- The line frames have the inverse adjusted transition; this is the full
prior-frame factor corresponding to the coframe transition. -/
theorem adjustedMatchingFrame_inverse (s : {s : Finset J // s.Nonempty})
    (j : J) (hj : j ∈ s.val) (k : J) (hk : k ∈ s.val) (d e : (N.obj s)ˣ) :
    (adjustedMatchingFrame N cN hcN delta n hco hn s j hj d).inv =
      Scheme.Modules.globalSectionsSmul
          (SheafOfModules.unit (Spec (.of (N.obj s))).ringCatSheaf)
          ((Scheme.ΓSpecIso (.of (N.obj s))).inv.hom
            ((((delta s j hj k hk * d * e⁻¹) ^ n)⁻¹ : (N.obj s)ˣ) : N.obj s)) ≫
        (adjustedMatchingFrame N cN hcN delta n hco hn s k hk e).inv := by
  let U := SheafOfModules.unit (Spec (.of (N.obj s))).ringCatSheaf
  let r := delta s j hj k hk * d * e⁻¹
  let a := scalarIso U (Units.map (Scheme.ΓSpecIso (.of (N.obj s))).inv.hom.toMonoidHom (r ^ n))
  have ha := scalar_power_hom (N.obj s) U r n
  have h := (adjustedMatchingFrame_change N cN hcN delta n hco hn s j hj k hk d e).trans
    (congrArg (fun b => (adjustedMatchingFrame N cN hcN delta n hco hn s k hk e).hom ≫ b)
      ha.symm)
  exact coframe_inverse
    (adjustedMatchingFrame N cN hcN delta n hco hn s j hj d)
    (adjustedMatchingFrame N cN hcN delta n hco hn s k hk e) a h

/-- Evaluating the inverse coframes at one constructs the prior line-frame
factor as the inverse of the full adjusted matching unit power. -/
theorem adjustedMatchingFrame_section (s : {s : Finset J // s.Nonempty})
    (j : J) (hj : j ∈ s.val) (k : J) (hk : k ∈ s.val) (d e : (N.obj s)ˣ) :
    frameValueRatio (X := (node N cN s).left)
      (adjustedMatchingFrame N cN hcN delta n hco hn s j hj d).inv
      (adjustedMatchingFrame N cN hcN delta n hco hn s k hk e).inv
      (coefficientSection N cN s
        ((((delta s j hj k hk * d * e⁻¹) ^ n)⁻¹ : (N.obj s)ˣ) : N.obj s))
      (1 : Γ(Spec (.of (N.obj s)), ⊤)) := by
  have hi := adjustedMatchingFrame_inverse N cN hcN delta n hco hn s j hj k hk d e
  exact value_ratio_of_eq _ _ _ _ hi

end SchubertGeometry.RetainedCharacter
