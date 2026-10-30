import OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.WordMatching
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Matching coframes and character evaluation

The selected matching coordinate is the coframe obtained by evaluating the
character on the chosen flag lift. Open base change is first identified with
the adjunct of relative functions over arbitrary open-immersion triangles.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open ReductiveGroups GroupActions
open FrobeniusSplitting.CharacterLine FrobeniusSplitting.RetainedCharacter
open scoped CategoryTheory.MonObj

noncomputable section
universe u v w

namespace SchubertGeometry.RetainedCharacter

open private frameIndex frameInto specArrow originalLeg originalLegOpen chartRestriction
  from OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.UnitFrames
open private unitFunctions selectedFunctionsIso identity_pullback
  from OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.UnitTrivialization
open private singletonIndex singletonArrow localFunctions
  from OrbitComplexity.FrobeniusSplitting.Modules.MatchingModule
open private leg legOpen flagPullback chartCoordinate chartLift lift_quotient coordinate_at
  from OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.WordMatchingBase
open private flagMatchingHom flagMatching_coordinate
  from OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.WordMatching
open private restrict_adjunct
  from OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.NativeFrame

private theorem section_image_preimage {X P Y : Scheme.{u}}
    (j : X ⟶ Y) [IsOpenImmersion j] (q : P ⟶ Y) (s : X ⟶ P)
    (h : s ≫ q = j) (W : X.Opens) : W ≤ s ⁻¹ᵁ (q ⁻¹ᵁ (j ''ᵁ W)) := by
  change W ≤ (s ≫ q) ⁻¹ᵁ (j ''ᵁ W)
  rw [h, j.preimage_image_eq]

private theorem open_triangle_adjunct {X P Y : Scheme.{u}}
    (j : X ⟶ Y) [IsOpenImmersion j] (q : P ⟶ Y)
    (s : X ⟶ P) [IsOpenImmersion s] (H : IsPullback (𝟙 X) s j q) :
    (Scheme.Modules.restrictAdjunction j).homEquiv
        (relativeFunctionsObj Y (Over.mk q)) (SheafOfModules.unit X.ringCatSheaf)
        ((openFunctionsBaseChange (𝟙 X) s j q H).hom ≫
          ((Scheme.Modules.pushforwardId X).app
            (SheafOfModules.unit X.ringCatSheaf)).hom) =
      relativeFunctionsMap Y (X := Over.mk j) (Y := Over.mk q)
        (Over.homMk s (H.w.symm.trans (Category.id_comp j))) := by
  have he := openFunctionsBaseChange_hom (𝟙 X) s j q H
  refine (congrArg
    ((Scheme.Modules.restrictAdjunction j).homEquiv
      (relativeFunctionsObj Y (Over.mk q)) (SheafOfModules.unit X.ringCatSheaf))
    (congrArg (fun t => t ≫ ((Scheme.Modules.pushforwardId X).app
      (SheafOfModules.unit X.ringCatSheaf)).hom) he)).trans ?_
  ext V t
  change Γ(P, q ⁻¹ᵁ V) at t
  let W := j ⁻¹ᵁ V
  have hV : q ⁻¹ᵁ (j ''ᵁ W) ≤ q ⁻¹ᵁ V :=
    q.preimage_mono (j.image_preimage_le V)
  have e : W ≤ s ⁻¹ᵁ (q ⁻¹ᵁ (j ''ᵁ W)) :=
    section_image_preimage j q s (H.w.symm.trans (Category.id_comp j)) W
  change s.appLE (q ⁻¹ᵁ (j ''ᵁ W)) W e
      ((P.presheaf.map (homOfLE hV).op) t) =
    ((relativeFunctionsMap Y (X := Over.mk j) (Y := Over.mk q)
      (Over.homMk s (H.w.symm.trans (Category.id_comp j)))).val.app (op V)).hom t
  let Xo : Over Y := Over.mk j
  let Po : Over Y := Over.mk q
  let f : Xo ⟶ Po := Over.homMk s (H.w.symm.trans (Category.id_comp j))
  have hf := @relativeFunctionsMap_app Y Xo Po f V t
  exact (ConcreteCategory.congr_hom (s.map_appLE e (homOfLE hV).op) t).trans hf.symm

private theorem functor_coframe {C D : Type v} [Category.{w} C] [Category.{w} D]
    (F P : C ⥤ D) (eta : F ≅ P) {M N : C} {T : D}
    (d : M ⟶ N) (e : F.obj N ⟶ T) :
    eta.inv.app M ≫ F.map d ≫ e = P.map d ≫ eta.inv.app N ≫ e := by
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun t => t ≫ e) (eta.inv.naturality d).symm).trans
      (Category.assoc _ _ _))

private theorem adjunct_coordinate {C D : Type v} [Category.{w} C] [Category.{w} D]
    (F : C ⥤ D) (R : D ⥤ C) (adj : F ⊣ R) {M L N : C} {T : D}
    (f : M ⟶ L) (d : L ⟶ N) (c : M ⟶ N)
    (t : F.obj L ⟶ T) (e : F.obj N ⟶ T) (k : N ⟶ R.obj T)
    (r : F.obj M ⟶ T) (ht : t = F.map d ≫ e)
    (he : adj.homEquiv N T e = k) (hd : f ≫ d = c)
    (hc : c ≫ k = adj.homEquiv M T r) : F.map f ≫ t = r := by
  apply (adj.homEquiv M T).injective
  calc
    _ = adj.homEquiv M T (F.map (f ≫ d) ≫ e) := by
      rw [ht, CategoryTheory.Functor.map_comp, Category.assoc]
    _ = (f ≫ d) ≫ adj.homEquiv N T e := adj.homEquiv_naturality_left (f ≫ d) e
    _ = c ≫ k := congrArg₂ (fun a b => a ≫ b) hd he
    _ = _ := hc

private theorem map_coframe_composite {C D : Type v} [Category.{w} C] [Category.{w} D]
    (F : C ⥤ D) {M N P : C} {T : D} (a : M ⟶ N) (b : N ⟶ P)
    (d : M ⟶ P) (hd : d = a ≫ b) (e : F.obj P ⟶ T)
    (r : F.obj N ⟶ T) (h : F.map b ≫ e = r) :
    F.map d ≫ e = F.map a ≫ r := by
  rw [hd, CategoryTheory.Functor.map_comp, Category.assoc, h]

section Relative
variable {R J : Type u} [CommRing R]
    (N : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} R)
    [hopen : ∀ {s t} (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (N.map f).hom.toRingHom))]
    [hdir : ((N.op ⋙ algSpec (.of R) ⋙ Over.forget (Spec (.of R))) ⋙
      Scheme.forget).IsLocallyDirected]
    (cN : Cocone (N.op ⋙ algSpec (.of R))) (hcN : IsColimit cN)

private theorem selected_functions_adjunct (s : {s : Finset J // s.Nonempty})
    (j : J) (hj : j ∈ s.val) :
    (@Scheme.Modules.restrictAdjunction _ _ (originalLeg N cN s)
      (originalLegOpen N cN hcN s)).homEquiv
        (unitFunctions N cN j) (SheafOfModules.unit (Spec (.of (N.obj s))).ringCatSheaf)
        (selectedFunctionsIso N cN hcN s j hj).hom =
      relativeFunctionsMap cN.pt.left (nodeMap N cN (frameInto s j hj)) := by
  let U := Spec (.of (N.obj s))
  let a := specArrow N (frameInto s j hj)
  let ja := originalLeg N cN s
  let jb := originalLeg N cN (frameIndex j)
  let hja : IsOpenImmersion ja := originalLegOpen N cN hcN s
  let hjb : IsOpenImmersion jb := originalLegOpen N cN hcN (frameIndex j)
  let ha : IsOpenImmersion a := hopen (frameInto s j hj)
  have h : (𝟙 U) ≫ ja = a ≫ jb :=
    (Category.id_comp ja).trans (nodeMap N cN (frameInto s j hj)).w.symm
  have H : IsPullback (𝟙 U) a ja jb :=
    identity_pullback a ja jb (@IsOpenImmersion.mono _ _ jb hjb) h
  have he : (selectedFunctionsIso N cN hcN s j hj).hom =
      (@openFunctionsBaseChange _ _ _ _ (𝟙 U) a ja jb hja ha H).hom ≫
        ((Scheme.Modules.pushforwardId U).app (SheafOfModules.unit U.ringCatSheaf)).hom := rfl
  exact (congrArg
    ((@Scheme.Modules.restrictAdjunction _ _ ja hja).homEquiv
      (unitFunctions N cN j) (SheafOfModules.unit U.ringCatSheaf)) he).trans
        (@open_triangle_adjunct _ _ _ ja hja jb a ha H)

variable (delta : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val)
      (k : J) (_ : k ∈ s.val), (N.obj s)ˣ) (n : ℕ)
    (hco : ∀ s j hj k hk l hl,
      delta s j hj l hl = delta s k hk l hl * delta s j hj k hk)
    (hn : ∀ s t (f : s ⟶ t) j hj k hk,
      Units.map (N.map f).hom.toMonoidHom (delta s j hj k hk) =
        delta t j ((leOfHom f) hj) k ((leOfHom f) hk))

private theorem local_character_hom (s : {s : Finset J // s.Nonempty})
    (j : J) (hj : j ∈ s.val) :
    (localCharacterTrivialization N cN hcN delta n hco hn s j hj).hom =
      (Scheme.Modules.pullback (originalLeg N cN s)).map (coordinate N cN delta n j) ≫
        (@Scheme.Modules.restrictFunctorIsoPullback _ _ (originalLeg N cN s)
          (originalLegOpen N cN hcN s)).inv.app (unitFunctions N cN j) ≫
        (selectedFunctionsIso N cN hcN s j hj).hom := by
  exact functor_coframe (chartRestriction N cN hcN s)
    (Scheme.Modules.pullback (originalLeg N cN s))
    (@Scheme.Modules.restrictFunctorIsoPullback _ _ (originalLeg N cN s)
      (originalLegOpen N cN hcN s)) (coordinate N cN delta n j)
      (selectedFunctionsIso N cN hcN s j hj).hom

private theorem selected_pullback_adjunct (s : {s : Finset J // s.Nonempty})
    (j : J) (hj : j ∈ s.val) :
    (Scheme.Modules.pullbackPushforwardAdjunction (originalLeg N cN s)).homEquiv
        (unitFunctions N cN j) (SheafOfModules.unit (Spec (.of (N.obj s))).ringCatSheaf)
        ((@Scheme.Modules.restrictFunctorIsoPullback _ _ (originalLeg N cN s)
          (originalLegOpen N cN hcN s)).inv.app (unitFunctions N cN j) ≫
            (selectedFunctionsIso N cN hcN s j hj).hom) =
      relativeFunctionsMap cN.pt.left (nodeMap N cN (frameInto s j hj)) :=
  (@restrict_adjunct _ _ (originalLeg N cN s) (originalLegOpen N cN hcN s)
    (unitFunctions N cN j) (SheafOfModules.unit (Spec (.of (N.obj s))).ringCatSheaf)
    (selectedFunctionsIso N cN hcN s j hj).hom).trans
      (selected_functions_adjunct N cN hcN s j hj)

end Relative

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K) {J : Type u}
    (F : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} K)
    [hopen : ∀ {s t} (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (F.map f).hom.toRingHom))]
    [hdir : ((F.op ⋙ algSpec (.of K) ⋙ Over.forget (Spec (.of K))) ⋙
      Scheme.forget).IsLocallyDirected]
    (cF : Cocone (F.op ⋙ algSpec (.of K))) (hcF : IsColimit cF)
    (word : List G.rootBase.support) (q : cF.pt.left ⟶ bsdhScheme G word) (n : ℕ)
    (point : J → G.points)
    (a : ∀ j, (algSpec (.of K)).obj (.op (F.obj (singletonIndex j))) ⟶
      (oppositeUnipotentVariety G).toOver)
    (ha : ∀ j, (a j).left ≫ (flagChartMorphism G (point j)).left =
      (cF.ι.app (.op (singletonIndex j))).left ≫ (q ≫ bsdhMap G word))
    (beta : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val)
      (k : J) (_ : k ∈ s.val),
      (algSpec (.of K)).obj (.op (F.obj s)) ⟶ (borelVariety G).toOver)
    (hgroup : ∀ s j hj k hk, chartLift G F point a s j hj =
      chartLift G F point a s k hk * (beta s j hj k hk ≫ borelInclusion G))
    (hco : ∀ s j hj k hk l hl, wordTransitionUnit G F beta s j hj l hl =
      wordTransitionUnit G F beta s k hk l hl * wordTransitionUnit G F beta s j hj k hk)
    (hn : ∀ s t (f : s ⟶ t) j hj k hk,
      Units.map (F.map f).hom.toMonoidHom (wordTransitionUnit G F beta s j hj k hk) =
        wordTransitionUnit G F beta t j ((leOfHom f) hj) k ((leOfHom f) hk))

private def node_map_piece (s : {s : Finset J // s.Nonempty}) (j : J) (hj : j ∈ s.val) :
    unitFunctions F cF j ⟶
      (Scheme.Modules.pushforward (leg F cF s)).obj
        (SheafOfModules.unit (Spec (.of (F.obj s))).ringCatSheaf) :=
  @relativeFunctionsMap cF.pt.left (node F cF s) (node F cF (singletonIndex j))
    (nodeMap F cF (singletonArrow s j hj))

omit [IsAlgClosed K] [CharZero K] in
private theorem selected_adjunct_piece (s : {s : Finset J // s.Nonempty})
    (j : J) (hj : j ∈ s.val) :
    (Scheme.Modules.pullbackPushforwardAdjunction (leg F cF s)).homEquiv
        (unitFunctions F cF j) (SheafOfModules.unit (Spec (.of (F.obj s))).ringCatSheaf)
        ((@Scheme.Modules.restrictFunctorIsoPullback _ _ (leg F cF s)
          (legOpen F cF hcF s)).inv.app (unitFunctions F cF j) ≫
            (selectedFunctionsIso F cF hcF s j hj).hom) =
      node_map_piece F cF s j hj :=
  selected_pullback_adjunct F cF hcF s j hj

private theorem coordinate_at_piece (s : {s : Finset J // s.Nonempty})
    (j : J) (hj : j ∈ s.val) :
    chartCoordinate G F cF hcF word q n point a ha j ≫ node_map_piece F cF s j hj =
      (Scheme.Modules.pullbackPushforwardAdjunction (leg F cF s)).homEquiv
        (flagPullback G F cF word q n)
        (SheafOfModules.unit (Spec (.of (F.obj s))).ringCatSheaf)
        ((Scheme.Modules.pullbackComp (leg F cF s) (q ≫ bsdhMap G word)).hom.app
          (CharacterLine.flagCharacterModule G (G.positiveRootCharacter ^ n)) ≫
          CharacterLine.characterFrameEvaluation G (G.positiveRootCharacter ^ n)
            ((algSpec (.of K)).obj (.op (F.obj s)))
            (leg F cF s ≫ (q ≫ bsdhMap G word)) (chartLift G F point a s j hj)
            (lift_quotient G F cF word q point a ha s j hj)) :=
  coordinate_at G F cF hcF word q n point a ha s j hj

private theorem flag_matching_evaluation (s : {s : Finset J // s.Nonempty})
    (j : J) (hj : j ∈ s.val) :
    (Scheme.Modules.pullback (leg F cF s)).map
        (flagMatchingHom G F cF hcF word q n point a ha beta hgroup) ≫
      (localCharacterTrivialization F cF hcF (wordTransitionUnit G F beta) n hco hn s j hj).hom =
      (Scheme.Modules.pullbackComp (leg F cF s) (q ≫ bsdhMap G word)).hom.app
        (CharacterLine.flagCharacterModule G (G.positiveRootCharacter ^ n)) ≫
      CharacterLine.characterFrameEvaluation G (G.positiveRootCharacter ^ n)
        ((algSpec (.of K)).obj (.op (F.obj s)))
        (leg F cF s ≫ (q ≫ bsdhMap G word)) (chartLift G F point a s j hj)
        (lift_quotient G F cF word q point a ha s j hj) := by
  have ht := local_character_hom F cF hcF (wordTransitionUnit G F beta) n hco hn s j hj
  have he := selected_adjunct_piece F cF hcF s j hj
  have hd := flagMatching_coordinate G F cF hcF word q n point a ha beta hgroup j
  have hc := coordinate_at_piece G F cF hcF word q n point a ha s j hj
  exact adjunct_coordinate
    (Scheme.Modules.pullback (leg F cF s)) (Scheme.Modules.pushforward (leg F cF s))
    (Scheme.Modules.pullbackPushforwardAdjunction (leg F cF s))
    (M := flagPullback G F cF word q n)
    (L := matchingModule F cF (wordTransitionUnit G F beta) n)
    (N := unitFunctions F cF j)
    (T := SheafOfModules.unit (Spec (.of (F.obj s))).ringCatSheaf)
    (flagMatchingHom G F cF hcF word q n point a ha beta hgroup)
    (coordinate F cF (wordTransitionUnit G F beta) n j)
    (chartCoordinate G F cF hcF word q n point a ha j)
    (localCharacterTrivialization F cF hcF (wordTransitionUnit G F beta) n hco hn s j hj).hom
    ((@Scheme.Modules.restrictFunctorIsoPullback _ _ (leg F cF s)
      (legOpen F cF hcF s)).inv.app (unitFunctions F cF j) ≫
        (selectedFunctionsIso F cF hcF s j hj).hom)
    (node_map_piece F cF s j hj)
    ((Scheme.Modules.pullbackComp (leg F cF s) (q ≫ bsdhMap G word)).hom.app
      (CharacterLine.flagCharacterModule G (G.positiveRootCharacter ^ n)) ≫
      CharacterLine.characterFrameEvaluation G (G.positiveRootCharacter ^ n)
        ((algSpec (.of K)).obj (.op (F.obj s)))
        (leg F cF s ≫ (q ≫ bsdhMap G word)) (chartLift G F point a s j hj)
        (lift_quotient G F cF word q point a ha s j hj))
    ht he hd hc

/-- The matching coframe on each intersection chart evaluates the full
character power on its specified flag lift. -/
theorem wordMatchingFrame_evaluation (s : {s : Finset J // s.Nonempty})
    (j : J) (hj : j ∈ s.val) :
    (Scheme.Modules.pullback (leg F cF s)).map
        (wordCharacterMatchingIso G F cF hcF word q n point a ha beta hgroup hco hn).hom ≫
      (localCharacterTrivialization F cF hcF (wordTransitionUnit G F beta) n hco hn s j hj).hom =
      (Scheme.Modules.pullback (leg F cF s)).map
        ((Scheme.Modules.pullbackComp q (bsdhMap G word)).hom.app
          (CharacterLine.flagCharacterModule G (G.positiveRootCharacter ^ n))) ≫
      (Scheme.Modules.pullbackComp (leg F cF s) (q ≫ bsdhMap G word)).hom.app
        (CharacterLine.flagCharacterModule G (G.positiveRootCharacter ^ n)) ≫
      CharacterLine.characterFrameEvaluation G (G.positiveRootCharacter ^ n)
        ((algSpec (.of K)).obj (.op (F.obj s)))
        (leg F cF s ≫ (q ≫ bsdhMap G word)) (chartLift G F point a s j hj)
        (lift_quotient G F cF word q point a ha s j hj) := by
  exact map_coframe_composite (Scheme.Modules.pullback (leg F cF s))
    ((Scheme.Modules.pullbackComp q (bsdhMap G word)).hom.app
      (CharacterLine.flagCharacterModule G (G.positiveRootCharacter ^ n)))
    (flagMatchingHom G F cF hcF word q n point a ha beta hgroup)
    (wordCharacterMatchingIso G F cF hcF word q n point a ha beta hgroup hco hn).hom rfl
    (localCharacterTrivialization F cF hcF (wordTransitionUnit G F beta) n hco hn s j hj).hom
    ((Scheme.Modules.pullbackComp (leg F cF s) (q ≫ bsdhMap G word)).hom.app
      (CharacterLine.flagCharacterModule G (G.positiveRootCharacter ^ n)) ≫
      CharacterLine.characterFrameEvaluation G (G.positiveRootCharacter ^ n)
        ((algSpec (.of K)).obj (.op (F.obj s)))
        (leg F cF s ≫ (q ≫ bsdhMap G word)) (chartLift G F point a s j hj)
        (lift_quotient G F cF word q point a ha s j hj))
    (flag_matching_evaluation G F cF hcF word q n point a ha beta hgroup hco hn s j hj)

end SchubertGeometry.RetainedCharacter
