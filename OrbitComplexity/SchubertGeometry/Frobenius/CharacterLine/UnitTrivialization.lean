import OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.UnitFrames
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Trivializations of matching character modules -/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open FrobeniusSplitting.CharacterLine FrobeniusSplitting.RetainedCharacter

noncomputable section
universe u

namespace SchubertGeometry.RetainedCharacter

open private functionsUnit coefficientCoordinate_map frameIndex frameInto
  combinedArrow specArrow specArrow_triangle originalLeg
  originalLegOpen chartRestriction localIntersectionMap localBC
  frameCoefficient candidateCoordinate weightedBaseCoordinate
  from OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.UnitFrames
private theorem map_matching {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {A B E T : C} (f : A ⟶ B) (g : B ⟶ T)
    (h : A ⟶ E) (k : E ⟶ T) (m : T ⟶ T) (heq : f ≫ g = h ≫ k ≫ m) :
    F.map f ≫ F.map g = F.map h ≫ F.map k ≫ F.map m :=
  (F.map_comp f g).symm.trans ((congrArg F.map heq).trans
    ((F.map_comp h (k ≫ m)).trans
      (congrArg (fun z => F.map h ≫ z) (F.map_comp k m))))
private def isoOfFrame {C : Type*} [Category C] {A B P : C}
    (f : A ⟶ B) [Mono f] (e : B ≅ P) (g : P ⟶ A)
    (h : g ≫ (f ≫ e.hom) = 𝟙 P) : A ≅ P where
  hom := f ≫ e.hom
  inv := g
  hom_inv_id := by
    apply (cancel_mono (f ≫ e.hom)).mp
    simp only [Category.assoc, h, Category.comp_id, Category.id_comp]
  inv_hom_id := h
private theorem iso_right {C : Type*} [Category C] {A B P : C}
    (f : A ⟶ B) (e : B ≅ P) (h : IsIso (f ≫ e.hom)) : IsIso f := by
  have : IsIso (f ≫ e.hom) := h
  exact IsIso.of_isIso_comp_right f e.hom
private theorem identity_comparison {C : Type*} [Category C] {A B T : C}
    (x : A ⟶ B) (f : B ⟶ B) (e : B ⟶ T) (a : A ⟶ T) (g : T ⟶ T)
    (hf : f = 𝟙 B) (hg : g = 𝟙 T) (he : x ≫ f ≫ e = a ≫ g) : x ≫ e = a := by
  simpa only [hf, hg, Category.id_comp, Category.comp_id] using he
private theorem coordinate_transport {C D : Type*} [Category C] [Category D]
    (F P : C ⥤ D) (eta : F ≅ P) {M N : C} {U : D}
    (b : U ⟶ F.obj M) (m : M ⟶ N) (d : U ⟶ F.obj N) (h : b ≫ F.map m = d) :
    (b ≫ eta.hom.app M) ≫ P.map m = d ≫ eta.hom.app N := by
  rw [Category.assoc, ← eta.hom.naturality, ← Category.assoc, h]
private theorem iso_comp_cancel {C : Type*} [Category C] {A B D E : C}
    (f : A ⟶ B) (e : B ≅ D) (a : A ≅ E) (r : E ⟶ D) (hr : IsIso r)
    (h : f ≫ e.hom = a.hom ≫ r) : IsIso f := by
  have : IsIso r := hr
  have : IsIso (a.hom ≫ r) := inferInstance
  exact IsIso.of_isIso_fac_right h
private theorem identity_pullback {C : Type*} [Category C] {U V S : C}
    (a : U ⟶ V) (j : U ⟶ S) (k : V ⟶ S) (hm : Mono k)
    (h : (𝟙 U) ≫ j = a ≫ k) : IsPullback (𝟙 U) a j k :=
  @IsPullback.of_horiz_isIso_mono C _ U U V S (𝟙 U) a j k inferInstance hm ⟨h⟩
private theorem pi_transport {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {I : Type*} (A : I → C) [HasProduct A]
    [HasProduct (fun j => F.obj (A j))] {M : C} {T : D}
    (a b : T ⟶ F.obj M) (i : M ⟶ ∏ᶜ A) (k : I)
    (h : a ≫ F.map (i ≫ Pi.π A k) = b ≫ F.map (i ≫ Pi.π A k)) :
    ((a ≫ F.map i) ≫ piComparison F A) ≫ Pi.π _ k =
      ((b ≫ F.map i) ≫ piComparison F A) ≫ Pi.π _ k := by
  simpa only [Category.assoc, piComparison_comp_π, ← Functor.map_comp] using h
variable {R J : Type u} [CommRing R]
    (N : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} R)
    [hmapOpen : ∀ {s t} (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (N.map f).hom.toRingHom))]
    [hdirected : ((N.op ⋙ algSpec (.of R) ⋙ Over.forget (Spec (.of R))) ⋙
      Scheme.forget).IsLocallyDirected]
    (cG : Cocone (N.op ⋙ algSpec (.of R))) (hcG : IsColimit cG)
    (delta₀ : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val)
      (k : J) (_ : k ∈ s.val), (N.obj s)ˣ) (n : ℕ)
private theorem localBC_natural (u : {s : Finset J // s.Nonempty})
    {s t : {s : Finset J // s.Nonempty}} (f : s ⟶ t) :
    (chartRestriction N cG hcG u).map (relativeFunctionsMap cG.pt.left
        (nodeMap N cG f)) ≫ (localBC N cG hcG u t).hom =
      (localBC N cG hcG u s).hom ≫
        relativeFunctionsMap (Spec (.of (N.obj u))) (localIntersectionMap N u f) := by
  have hk : (localIntersectionMap N u f).left ≫ specArrow N (unionRight u s) =
      specArrow N (unionRight u t) ≫ (nodeMap N cG f).left :=
    (specArrow_triangle N (unionRight u s) (combinedArrow u f) (f ≫ unionRight u t)).trans
      (specArrow_triangle N f (unionRight u t) (f ≫ unionRight u t)).symm
  let j := originalLeg N cG u
  let hj := originalLegOpen N cG hcG u
  let p₁ := specArrow N (unionLeft u t)
  let p₂ := specArrow N (unionLeft u s)
  let q₁ := originalLeg N cG t
  let q₂ := originalLeg N cG s
  let k₁ := specArrow N (unionRight u t)
  let k₂ := specArrow N (unionRight u s)
  let hk₁ := hmapOpen (unionRight u t)
  let hk₂ := hmapOpen (unionRight u s)
  let H₁ := retained_overlap_square N cG hcG u t
  let H₂ := retained_overlap_square N cG hcG u s
  let m := (chartRestriction N cG hcG u).map
    (relativeFunctionsMap cG.pt.left (nodeMap N cG f))
  let r := relativeFunctionsMap (Spec (.of (N.obj u))) (localIntersectionMap N u f)
  have h₁ : (localBC N cG hcG u t).hom =
      @openFunctionsPullback _ _ _ _ p₁ k₁ j q₁ hj H₁.w :=
    @openFunctionsBaseChange_hom _ _ _ _ p₁ k₁ j q₁ hj hk₁ H₁
  have h₂ : (localBC N cG hcG u s).hom =
      @openFunctionsPullback _ _ _ _ p₂ k₂ j q₂ hj H₂.w :=
    @openFunctionsBaseChange_hom _ _ _ _ p₂ k₂ j q₂ hj hk₂ H₂
  have hn := @openFunctionsPullback_natural _ _ _ _ _ _ j hj
    p₁ p₂ q₁ q₂ k₁ k₂ H₁.w H₂.w (nodeMap N cG f) (localIntersectionMap N u f) hk
  exact (congrArg (fun z ↦ m ≫ z) h₁).trans
    (hn.trans (congrArg (fun z ↦ z ≫ r) h₂.symm))
private theorem restrictedNodeMapIso (u : {s : Finset J // s.Nonempty})
    {s t : {s : Finset J // s.Nonempty}} (f : s ⟶ t)
    (heq : unionIndex u s = unionIndex u t) :
    IsIso ((chartRestriction N cG hcG u).map
      (relativeFunctionsMap cG.pt.left (nodeMap N cG f))) := by
  let hidx : IsIso (combinedArrow u f) :=
    (isIso_iff_of_thin _).mpr ⟨eqToHom heq.symm⟩
  let E := N.op ⋙ algSpec (.of R) ⋙ Over.forget (Spec (.of R))
  let hspec : IsIso (specArrow N (combinedArrow u f)) := by
    change IsIso (E.map (combinedArrow u f).op)
    infer_instance
  let T := localIntersectionMap N u f
  have : IsIso ((Over.forget (Spec (.of (N.obj u)))).map T) := hspec
  have hT : IsIso T := isIso_of_reflects_iso T (Over.forget (Spec (.of (N.obj u))))
  have hm : IsIso (relativeFunctionsMap (Spec (.of (N.obj u))) T) := by
    change IsIso ((relativeFunctions (Spec (.of (N.obj u)))).map T.op)
    infer_instance
  let m := (chartRestriction N cG hcG u).map
    (relativeFunctionsMap cG.pt.left (nodeMap N cG f))
  exact iso_comp_cancel m (localBC N cG hcG u t) (localBC N cG hcG u s)
    (relativeFunctionsMap (Spec (.of (N.obj u))) T) hm (localBC_natural N cG hcG u f)
private def unitFunctions (k : J) : cG.pt.left.Modules :=
  relativeFunctionsObj cG.pt.left (node N cG (frameIndex k))
private def unitOverlap :=
  Σ s : {s : Finset J // s.Nonempty}, {j : J // j ∈ s.val} × {k : J // k ∈ s.val}
private def unitOverlapFunctions (b : unitOverlap (J := J)) : cG.pt.left.Modules :=
  relativeFunctionsObj cG.pt.left (node N cG b.1)
private def unitFirst : (∏ᶜ unitFunctions N cG) ⟶ ∏ᶜ unitOverlapFunctions N cG :=
  Pi.lift (fun b ↦ Pi.π (unitFunctions N cG) b.2.1.val ≫
    relativeFunctionsMap cG.pt.left
      (nodeMap N cG (frameInto b.1 b.2.1.val b.2.1.property)))
private def unitSecond : (∏ᶜ unitFunctions N cG) ⟶ ∏ᶜ unitOverlapFunctions N cG :=
  Pi.lift (fun b ↦ Pi.π (unitFunctions N cG) b.2.2.val ≫
    relativeFunctionsMap cG.pt.left
      (nodeMap N cG (frameInto b.1 b.2.2.val b.2.2.property)) ≫
    relativeFunctionsSmul cG.pt.left (node N cG b.1)
      ((Scheme.ΓSpecIso (.of (N.obj b.1))).inv
        ((delta₀ b.1 b.2.1.val b.2.1.property b.2.2.val b.2.2.property : N.obj b.1) ^ n)))
private theorem restricted_coordinate_ext (u : {s : Finset J // s.Nonempty})
    {P : (Spec (.of (N.obj u))).Modules}
    (a b : P ⟶ (chartRestriction N cG hcG u).obj (matchingModule N cG delta₀ n))
    (h : ∀ k, a ≫ (chartRestriction N cG hcG u).map (coordinate N cG delta₀ n k) =
      b ≫ (chartRestriction N cG hcG u).map (coordinate N cG delta₀ n k)) : a = b := by
  let F := chartRestriction N cG hcG u
  let hSize : PreservesLimitsOfSize.{u, u} F := @restrictPreservesLimits _ _
    (originalLeg N cG u) (originalLegOpen N cG hcG u)
  let hSmall : PreservesLimitsOfSize.{0, 0} F := preservesLimitsOfSize_shrink F
  let hShape : PreservesLimitsOfShape WalkingParallelPair F :=
    hSmall.preservesLimitsOfShape (J := WalkingParallelPair)
  let : PreservesLimit (parallelPair (unitFirst N cG) (unitSecond N cG delta₀ n)) F :=
    hShape.preservesLimit
  let hp : PreservesLimitsOfShape (Discrete J) F := hSize.preservesLimitsOfShape
  let hProduct : PreservesLimit (Discrete.functor (unitFunctions N cG)) F := hp.preservesLimit
  let eProduct := @PreservesProduct.iso _ _ _ _ F J (unitFunctions N cG)
    inferInstance inferInstance hProduct
  let i := equalizer.ι (unitFirst N cG) (unitSecond N cG delta₀ n)
  apply Fork.IsLimit.hom_ext
    (isLimitOfHasEqualizerOfPreservesLimit F (unitFirst N cG) (unitSecond N cG delta₀ n))
  change a ≫ F.map i = b ≫ F.map i
  apply (cancel_mono eProduct.hom).mp
  change (a ≫ F.map i) ≫ piComparison F (unitFunctions N cG) =
    (b ≫ F.map i) ≫ piComparison F (unitFunctions N cG)
  have : HasProduct (fun j : J => F.obj (unitFunctions N cG j)) := inferInstance
  apply Pi.hom_ext (f := fun j : J => F.obj (unitFunctions N cG j))
  intro k
  have hk : a ≫ F.map (i ≫ Pi.π (unitFunctions N cG) k) =
      b ≫ F.map (i ≫ Pi.π (unitFunctions N cG) k) := h k
  exact pi_transport F (unitFunctions N cG) a b i k hk
private theorem selectedCoordinateMono (u : {s : Finset J // s.Nonempty})
    (j : J) (hj : j ∈ u.val) :
    Mono ((chartRestriction N cG hcG u).map (coordinate N cG delta₀ n j)) := by
  classical
  let F := chartRestriction N cG hcG u
  constructor
  intro P a b hab
  apply restricted_coordinate_ext N cG hcG delta₀ n u a b
  intro k
  let w := unionIndex u (frameIndex k)
  let hjw : j ∈ w.val := (leOfHom (unionLeft u (frameIndex k))) hj
  let hkw : k ∈ w.val := (leOfHom (unionRight u (frameIndex k))) (Finset.mem_singleton_self k)
  let fk := frameInto w k hkw
  let fj := frameInto w j hjw
  have heq : unionIndex u (frameIndex k) = unionIndex u w := by
    apply Subtype.ext
    change u.val ∪ {k} = u.val ∪ (u.val ∪ {k})
    rw [← Finset.union_assoc, Finset.union_self]
  let hm : IsIso (F.map (relativeFunctionsMap cG.pt.left (nodeMap N cG fk))) :=
    restrictedNodeMapIso N cG hcG u fk heq
  let rk := F.map (relativeFunctionsMap cG.pt.left (nodeMap N cG fk))
  let rj := F.map (relativeFunctionsMap cG.pt.left (nodeMap N cG fj))
  let d := F.map (relativeFunctionsSmul cG.pt.left (node N cG w)
    ((Scheme.ΓSpecIso (.of (N.obj w))).inv ((delta₀ w k hkw j hjw : N.obj w) ^ n)))
  have hmatch : F.map (coordinate N cG delta₀ n k) ≫ rk =
      F.map (coordinate N cG delta₀ n j) ≫ rj ≫ d := by
    exact map_matching F _ _ _ _ _ (coordinate_matching N cG delta₀ n w k hkw j hjw)
  apply (cancel_mono rk).mp
  calc
    (a ≫ F.map (coordinate N cG delta₀ n k)) ≫ rk =
        a ≫ (F.map (coordinate N cG delta₀ n j) ≫ rj ≫ d) :=
      (Category.assoc _ _ _).trans (congrArg (fun z ↦ a ≫ z) hmatch)
    _ = (a ≫ F.map (coordinate N cG delta₀ n j)) ≫ rj ≫ d :=
      (Category.assoc _ _ _).symm
    _ = (b ≫ F.map (coordinate N cG delta₀ n j)) ≫ rj ≫ d :=
      congrArg (fun z ↦ z ≫ rj ≫ d) hab
    _ = b ≫ (F.map (coordinate N cG delta₀ n k) ≫ rk) :=
      (Category.assoc _ _ _).trans (congrArg (fun z ↦ b ≫ z) hmatch.symm)
    _ = (b ≫ F.map (coordinate N cG delta₀ n k)) ≫ rk := (Category.assoc _ _ _).symm
private def selectedFunctionsIso (u : {s : Finset J // s.Nonempty})
    (j : J) (hj : j ∈ u.val) :
    (chartRestriction N cG hcG u).obj (unitFunctions N cG j) ≅
      SheafOfModules.unit (Spec (.of (N.obj u))).ringCatSheaf := by
  let U := Spec (.of (N.obj u))
  let a := specArrow N (frameInto u j hj)
  let ja := originalLeg N cG u
  let jb := originalLeg N cG (frameIndex j)
  let hja : IsOpenImmersion ja := originalLegOpen N cG hcG u
  let hjb : IsOpenImmersion jb := originalLegOpen N cG hcG (frameIndex j)
  let ha : IsOpenImmersion a := hmapOpen (frameInto u j hj)
  have h : (𝟙 U) ≫ ja = a ≫ jb := by
    exact (Category.id_comp ja).trans (nodeMap N cG (frameInto u j hj)).w.symm
  have H : IsPullback (𝟙 U) a ja jb :=
    identity_pullback a ja jb (@IsOpenImmersion.mono _ _ jb hjb) h
  exact @openFunctionsBaseChange _ _ _ _ (𝟙 U) a ja jb hja ha H ≪≫
    (Scheme.Modules.pushforwardId U).app (SheafOfModules.unit U.ringCatSheaf)
private theorem functionsIdentityUnit (U : Scheme.{u}) :
    functionsUnit U (Over.mk (𝟙 U)) ≫
      ((Scheme.Modules.pushforwardId U).app (SheafOfModules.unit U.ringCatSheaf)).hom = 𝟙 _ := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  rfl
private theorem selectedCoordinate_unit
    (hco : ∀ s j hj k hk l hl,
      delta₀ s j hj l hl = delta₀ s k hk l hl * delta₀ s j hj k hk)
    (u : {s : Finset J // s.Nonempty}) (j : J) (hj : j ∈ u.val) :
    candidateCoordinate N cG hcG delta₀ n u j hj j ≫
      (selectedFunctionsIso N cG hcG u j hj).hom = 𝟙 _ := by
  classical
  let U := Spec (.of (N.obj u))
  let w := unionIndex u (frameIndex j)
  let back : w ⟶ u := homOfLE (Finset.union_subset (fun _ hx ↦ hx)
    (Finset.singleton_subset_iff.mpr hj))
  let a := specArrow N (frameInto u j hj)
  let ja := originalLeg N cG u
  let jb := originalLeg N cG (frameIndex j)
  let hja : IsOpenImmersion ja := originalLegOpen N cG hcG u
  let hjb : IsOpenImmersion jb := originalLegOpen N cG hcG (frameIndex j)
  let ha : IsOpenImmersion a := hmapOpen (frameInto u j hj)
  have h : (𝟙 U) ≫ ja = a ≫ jb :=
    (Category.id_comp ja).trans (nodeMap N cG (frameInto u j hj)).w.symm
  let H : IsPullback (𝟙 U) a ja jb := identity_pullback a ja jb (@IsOpenImmersion.mono _ _ jb hjb) h
  let p := specArrow N (unionLeft u (frameIndex j))
  let r := specArrow N (unionRight u (frameIndex j))
  have hp : specArrow N back ≫ p = 𝟙 U := by
    have hi : specArrow N (𝟙 u) = 𝟙 U := by
      let E := N.op ⋙ algSpec (.of R) ⋙ Over.forget (Spec (.of R))
      exact E.map_id (.op u)
    exact (specArrow_triangle N (unionLeft u (frameIndex j)) back (𝟙 u)).trans hi
  let T : Over.mk (𝟙 U) ⟶ Over.mk p := Over.homMk (specArrow N back) hp
  have hk : T.left ≫ r = a ≫ 𝟙 (Spec (.of (N.obj (frameIndex j)))) := by
    change specArrow N back ≫ r = a ≫ 𝟙 _
    exact (specArrow_triangle N (unionRight u (frameIndex j)) back
      (frameInto u j hj)).trans (Category.comp_id a).symm
  have hunit : (frameCoefficient N delta₀ n u j hj j : Γ(Spec (.of (N.obj w)), ⊤)) = 1 := by
    let hjw : j ∈ w.val := (leOfHom (unionLeft u (frameIndex j))) hj
    have hd : delta₀ w j hjw j hjw = 1 := by
      have hh := hco w j hjw j hjw j hjw
      exact mul_left_cancel (hh.symm.trans (mul_one _).symm)
    change (Scheme.ΓSpecIso (.of (N.obj w))).inv (↑((delta₀ w j hjw j hjw)⁻¹ ^ n)) = 1
    rw [hd, inv_one, one_pow, Units.val_one, map_one]
  have hid : relativeFunctionsMap cG.pt.left
      (𝟙 (node N cG (frameIndex j))) = 𝟙 _ :=
    (relativeFunctions cG.pt.left).map_id (.op (node N cG (frameIndex j)))
  have he := @coefficientCoordinate_map _ _ _ _ _ _ ja hja
    (𝟙 U) p jb jb a r ha (hmapOpen (unionRight u (frameIndex j)))
    H (retained_overlap_square N cG hcG u (frameIndex j))
    (𝟙 (node N cG (frameIndex j))) T hk (1 : Γ(Spec (.of (N.obj w)), ⊤))
  have he' : candidateCoordinate N cG hcG delta₀ n u j hj j ≫
      (@openFunctionsBaseChange _ _ _ _ (𝟙 U) a ja jb hja ha H).hom =
      functionsUnit U (Over.mk (𝟙 U)) := by
    let F := chartRestriction N cG hcG u
    let rho := relativeFunctionsMap cG.pt.left (𝟙 (node N cG (frameIndex j)))
    let B := @weightedBaseCoordinate _ _ _ _ ja hja p jb r
      (hmapOpen (unionRight u (frameIndex j)))
      (retained_overlap_square N cG hcG u (frameIndex j))
    have hx : candidateCoordinate N cG hcG delta₀ n u j hj j = B 1 := congrArg B hunit
    have hf : F.map rho = 𝟙 _ := (congrArg F.map hid).trans (F.map_id _)
    let z := Over.mk (𝟙 U)
    let gamma := relativeFunctionsSmul U z (T.left.appTop (1 : Γ(Spec (.of (N.obj w)), ⊤)))
    have hg : gamma = 𝟙 _ :=
      (congrArg (relativeFunctionsSmul U z) (map_one T.left.appTop.hom)).trans
        (relativeFunctionsSmul_one U z)
    have hh := identity_comparison (B 1) (F.map rho)
      (@openFunctionsBaseChange _ _ _ _ (𝟙 U) a ja jb hja ha H).hom
      (functionsUnit U z) gamma hf hg he
    exact (congrArg (fun t => t ≫
      (@openFunctionsBaseChange _ _ _ _ (𝟙 U) a ja jb hja ha H).hom) hx).trans hh
  change candidateCoordinate N cG hcG delta₀ n u j hj j ≫
    ((@openFunctionsBaseChange _ _ _ _ (𝟙 U) a ja jb hja ha H).hom ≫
      ((Scheme.Modules.pushforwardId U).app (SheafOfModules.unit U.ringCatSheaf)).hom) = 𝟙 _
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun z ↦ z ≫
      ((Scheme.Modules.pushforwardId U).app (SheafOfModules.unit U.ringCatSheaf)).hom) he').trans
        (functionsIdentityUnit U))

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "UnitTrivialization: localCharacterTrivialization"
    (← IO.getStderr).flush
private def restrictionCharacterIso
    (hco : ∀ s j hj k hk l hl,
      delta₀ s j hj l hl = delta₀ s k hk l hl * delta₀ s j hj k hk)
    (hn : ∀ s t (f : s ⟶ t) j hj k hk,
      Units.map (N.map f).hom.toMonoidHom (delta₀ s j hj k hk) =
        delta₀ t j ((leOfHom f) hj) k ((leOfHom f) hk))
    (u : {s : Finset J // s.Nonempty}) (j : J) (hj : j ∈ u.val) :
    (chartRestriction N cG hcG u).obj (matchingModule N cG delta₀ n) ≅
      SheafOfModules.unit (Spec (.of (N.obj u))).ringCatSheaf := by
  let F := chartRestriction N cG hcG u
  let b := localUnitFrame N cG hcG delta₀ n hco hn u j hj
  let r := F.map (coordinate N cG delta₀ n j) ≫ (selectedFunctionsIso N cG hcG u j hj).hom
  have hbr : b ≫ r = 𝟙 _ :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun z ↦ z ≫ (selectedFunctionsIso N cG hcG u j hj).hom)
        (localUnitFrame_coordinate N cG hcG delta₀ n hco hn u j hj j)).trans
          (selectedCoordinate_unit N cG hcG delta₀ n hco u j hj))
  letI : Mono (F.map (coordinate N cG delta₀ n j)) :=
    selectedCoordinateMono N cG hcG delta₀ n u j hj
  exact isoOfFrame (F.map (coordinate N cG delta₀ n j))
    (selectedFunctionsIso N cG hcG u j hj) b hbr
/-- The matching character module is trivial on each intersection chart. -/
def localCharacterTrivialization
    (hco : ∀ s j hj k hk l hl,
      delta₀ s j hj l hl = delta₀ s k hk l hl * delta₀ s j hj k hk)
    (hn : ∀ s t (f : s ⟶ t) j hj k hk,
      Units.map (N.map f).hom.toMonoidHom (delta₀ s j hj k hk) =
        delta₀ t j ((leOfHom f) hj) k ((leOfHom f) hk))
    (u : {s : Finset J // s.Nonempty}) (j : J) (hj : j ∈ u.val) :
    (Scheme.Modules.pullback (cG.ι.app (.op u)).left).obj (matchingModule N cG delta₀ n) ≅
      SheafOfModules.unit (Spec (.of (N.obj u))).ringCatSheaf :=
  ((@Scheme.Modules.restrictFunctorIsoPullback _ _ (originalLeg N cG u)
    (originalLegOpen N cG hcG u)).symm.app (matchingModule N cG delta₀ n)) ≪≫
      restrictionCharacterIso N cG hcG delta₀ n hco hn u j hj
/-- A selected coordinate is an isomorphism after restriction to its chart. -/
theorem selectedCoordinate_isIso
    (hco : ∀ s j hj k hk l hl,
      delta₀ s j hj l hl = delta₀ s k hk l hl * delta₀ s j hj k hk)
    (hn : ∀ s t (f : s ⟶ t) j hj k hk,
      Units.map (N.map f).hom.toMonoidHom (delta₀ s j hj k hk) =
        delta₀ t j ((leOfHom f) hj) k ((leOfHom f) hk))
    (u : {s : Finset J // s.Nonempty}) (j : J) (hj : j ∈ u.val) :
    IsIso ((chartRestriction N cG hcG u).map (coordinate N cG delta₀ n j)) := by
  exact iso_right _ (selectedFunctionsIso N cG hcG u j hj)
    (restrictionCharacterIso N cG hcG delta₀ n hco hn u j hj).isIso_hom
/-- The inverse trivialization has the inverse transition coefficients. -/
theorem localCharacterTriv_inv_coord
    (hco : ∀ s j hj k hk l hl,
      delta₀ s j hj l hl = delta₀ s k hk l hl * delta₀ s j hj k hk)
    (hn : ∀ s t (f : s ⟶ t) j hj k hk,
      Units.map (N.map f).hom.toMonoidHom (delta₀ s j hj k hk) =
        delta₀ t j ((leOfHom f) hj) k ((leOfHom f) hk))
    (u : {s : Finset J // s.Nonempty}) (j : J) (hj : j ∈ u.val) (k : J) :
    (localCharacterTrivialization N cG hcG delta₀ n hco hn u j hj).inv ≫
        (Scheme.Modules.pullback (cG.ι.app (.op u)).left).map (coordinate N cG delta₀ n k) =
      inverseFrameCoordinate N cG hcG delta₀ n u j hj k := by
  let a := originalLeg N cG u
  let ha := originalLegOpen N cG hcG u
  let eta := @Scheme.Modules.restrictFunctorIsoPullback _ _ a ha
  let b := localUnitFrame N cG hcG delta₀ n hco hn u j hj
  let m := coordinate N cG delta₀ n k
  change (b ≫ eta.hom.app _) ≫ (Scheme.Modules.pullback a).map m = _
  exact coordinate_transport (chartRestriction N cG hcG u) (Scheme.Modules.pullback a)
    eta b m (candidateCoordinate N cG hcG delta₀ n u j hj k)
    (localUnitFrame_coordinate N cG hcG delta₀ n hco hn u j hj k)

end SchubertGeometry.RetainedCharacter
