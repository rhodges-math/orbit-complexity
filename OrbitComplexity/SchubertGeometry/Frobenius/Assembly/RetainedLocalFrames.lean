import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendPowerFrames
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.MatchingPullback
import OrbitComplexity.FrobeniusSplitting.Normality.Assembly.MatchingSections
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Adjusted arithmetic coframes on the fixed affine cover

The retained degree-one units modify the canonical matching coframes. Their
scalar-square equations and section coordinates hold for every character
power on the same chosen coefficient diagram.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open FrobeniusSplitting.CharacterLine FrobeniusSplitting.RetainedCharacter
open ReductiveGroups GroupActions CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj

noncomputable section
universe u v w

namespace SchubertGeometry.RetainedCharacter

open private singletonIndex singletonArrow localFunctions
  from OrbitComplexity.FrobeniusSplitting.Modules.MatchingModule
open private relativeFunctionsMap_id
  from OrbitComplexity.FrobeniusSplitting.Modules.RelativeFunctions
open private local_character_hom selected_pullback_adjunct
  from OrbitComplexity.SchubertGeometry.Frobenius.Assembly.MatchingCoframeEvaluation
open private originalLeg originalLegOpen
  from OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.UnitFrames
open private selectedFunctionsIso
  from OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.UnitTrivialization
open private scalarIso
  from OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.LiftEvaluation
open private chartLift
  from OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.WordMatchingBase
open private pullSection
  from OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.PullbackFrames

private theorem coordinate_adjunct {C D : Type v} [Category.{w} C] [Category.{w} D]
    (L : C ⥤ D) (R : D ⥤ C) (adj : L ⊣ R) {M : C} {U : D}
    (d : M ⟶ R.obj U) (e : L.obj (R.obj U) ⟶ U) (t : L.obj M ⟶ U)
    (ht : t = L.map d ≫ e) (he : adj.homEquiv (R.obj U) U e = 𝟙 _) :
    adj.homEquiv M U t = d :=
  (congrArg (adj.homEquiv M U) ht).trans
    ((adj.homEquiv_naturality_left d e).trans
      ((congrArg (fun x => d ≫ x) he).trans (Category.comp_id d)))

private theorem frame_counit {C D : Type v} [Category.{w} C] [Category.{w} D]
    (L : C ⥤ D) (R : D ⥤ C) (adj : L ⊣ R) {M : C} {U : D}
    (c : M ⟶ R.obj U) (e : L.obj M ⟶ U) (he : adj.homEquiv M U e = c) :
    e = L.map c ≫ adj.counit.app U := by
  calc
    e = (adj.homEquiv M U).symm c :=
      ((adj.homEquiv M U).symm_apply_apply e).symm.trans
        (congrArg (adj.homEquiv M U).symm he)
    _ = L.map c ≫ adj.counit.app U := adj.homEquiv_counit M U c

private theorem coordinate_square {C D : Type v} [Category.{w} C] [Category.{w} D]
    (L : C ⥤ D) {M N P : C} {U : D}
    (f : M ⟶ N) (d : N ⟶ P) (t : M ⟶ P)
    (e : L.obj N ⟶ U) (eps : L.obj P ⟶ U) (r : L.obj M ⟶ U)
    (he : e = L.map d ≫ eps) (hf : f ≫ d = t) (hr : L.map t ≫ eps = r) :
    L.map f ≫ e = r := by
  calc
    _ = L.map f ≫ L.map d ≫ eps := congrArg (fun x => L.map f ≫ x) he
    _ = L.map (f ≫ d) ≫ eps := by rw [CategoryTheory.Functor.map_comp, Category.assoc]
    _ = L.map t ≫ eps := congrArg (fun x => L.map x ≫ eps) hf
    _ = _ := hr

private theorem section_by_adjunct {C D : Type v} [Category.{w} C] [Category.{w} D]
    (L : C ⥤ D) (R : D ⥤ C) (adj : L ⊣ R) {O M : C} {U : D}
    (unit : L.obj O ≅ U) (s : O ⟶ M) (e : L.obj M ⟶ U)
    (c : M ⟶ R.obj U) (r : U ⟶ U) (u : O ⟶ R.obj U)
    (he : adj.homEquiv M U e = c) (hu : adj.homEquiv O U unit.hom = u)
    (hs : s ≫ c = u ≫ R.map r) : unit.inv ≫ L.map s ≫ e = r := by
  have h : L.map s ≫ e = unit.hom ≫ r := by
    apply (adj.homEquiv O U).injective
    calc
      _ = s ≫ c := (adj.homEquiv_naturality_left s e).trans
        (congrArg (fun x => s ≫ x) he)
      _ = u ≫ R.map r := hs
      _ = adj.homEquiv O U (unit.hom ≫ r) :=
        (congrArg (fun x => x ≫ R.map r) hu.symm).trans
          (adj.homEquiv_naturality_right unit.hom r).symm
  simpa only [Category.assoc, Iso.inv_hom_id_assoc] using
    congrArg (fun x => unit.inv ≫ x) h

private theorem singleton_value {J : Type v} {A : Sort w}
    (j k : J) (hk : k ∈ ({j} : Finset J)) (f : ∀ l ∈ ({j} : Finset J), A) :
    f k hk = f j (Finset.mem_singleton_self j) := by
  have h : k = j := Finset.mem_singleton.mp hk
  subst k
  rfl

private theorem affine_smul_power (A : Type u) [CommRing A]
    (M : (Spec (.of A)).Modules) (x y : A) (n : ℕ) :
    Scheme.Modules.globalSectionsSmul M ((Scheme.ΓSpecIso (.of A)).inv (x ^ n)) ≫
        Scheme.Modules.globalSectionsSmul M ((Scheme.ΓSpecIso (.of A)).inv (y ^ n)) =
      Scheme.Modules.globalSectionsSmul M ((Scheme.ΓSpecIso (.of A)).inv ((x * y) ^ n)) := by
  have hp : (Scheme.ΓSpecIso (.of A)).inv ((x * y) ^ n) =
      (Scheme.ΓSpecIso (.of A)).inv (y ^ n) * (Scheme.ΓSpecIso (.of A)).inv (x ^ n) :=
    (congrArg (Scheme.ΓSpecIso (.of A)).inv.hom
      ((mul_pow x y n).trans (mul_comm _ _))).trans
      (map_mul (Scheme.ΓSpecIso (.of A)).inv.hom _ _)
  exact (Scheme.Modules.globalSectionsSmul_mul M _ _).symm.trans
    (congrArg (Scheme.Modules.globalSectionsSmul M) hp.symm)

private theorem mapped_frame_scalar {C D : Type v} [Category.{w} C] [Category.{w} D]
    (F : C ⥤ D) {M N : C} {P Q : D}
    (v : P ⟶ F.obj M) (e : M ⟶ N) (s : N ⟶ N)
    (u : F.obj N ⟶ Q) (t : Q ⟶ Q)
    (hs : F.map s ≫ u = u ≫ t) :
    v ≫ F.map (e ≫ s) ≫ u = (v ≫ F.map e ≫ u) ≫ t := by
  rw [CategoryTheory.Functor.map_comp]
  simp only [Category.assoc, hs]

private theorem square_frame_scalar {P X S T : Scheme.{u}}
    (q : T ⟶ S) (a : P ⟶ T) (b : X ⟶ S) (k : P ⟶ X)
    (h : k ≫ b = a ≫ q) (M : S.Modules)
    (e e' : (Scheme.Modules.pullback b).obj M ≅ SheafOfModules.unit X.ringCatSheaf)
    (r : Γ(X, ⊤))
    (he : e'.hom = e.hom ≫ Scheme.Modules.globalSectionsSmul
      (SheafOfModules.unit X.ringCatSheaf) r) :
    (squareFrameIso q a b k h M e').hom =
      (squareFrameIso q a b k h M e).hom ≫
        Scheme.Modules.globalSectionsSmul (SheafOfModules.unit P.ringCatSheaf) (k.appTop r) := by
  let v := (Scheme.Modules.pullbackComp a q).hom.app M ≫
    (Scheme.Modules.pullbackCongr h.symm).hom.app M ≫
      (Scheme.Modules.pullbackComp k b).inv.app M
  have hs := (congrArg (fun t => t ≫ (Scheme.Modules.pullbackObjUnitIso k).hom)
    (Scheme.Modules.pullback_map_globalSectionsSmul k
      (SheafOfModules.unit X.ringCatSheaf) r)).trans
        (Scheme.Modules.globalSectionsSmul_naturality
          (Scheme.Modules.pullbackObjUnitIso k).hom (k.appTop r))
  exact (congrArg (fun t => v ≫ (Scheme.Modules.pullback k).map t ≫
    (Scheme.Modules.pullbackObjUnitIso k).hom) he).trans
      (mapped_frame_scalar (Scheme.Modules.pullback k) v e.hom
        (Scheme.Modules.globalSectionsSmul (SheafOfModules.unit X.ringCatSheaf) r)
        (Scheme.Modules.pullbackObjUnitIso k).hom
        (Scheme.Modules.globalSectionsSmul (SheafOfModules.unit P.ringCatSheaf) (k.appTop r)) hs)

private theorem coefficient_power_scalar {A B : CommRingCat.{u}}
    (f : A ⟶ B) (y : A) (z : B) (h : f.hom y = z) (n : ℕ) :
    (Spec.map f).appTop ((Scheme.ΓSpecIso A).inv (y ^ n)) =
      (Scheme.ΓSpecIso B).inv (z ^ n) :=
  (coefficientSection_scalar f y n).trans
    (congrArg (Scheme.ΓSpecIso B).inv.hom (congrArg (fun t => t ^ n) h))

section Arithmetic
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

omit hopen hdir in
private theorem singleton_functions_id (j : J) :
    relativeFunctionsMap cN.pt.left
        (nodeMap N cN (singletonArrow (singletonIndex j) j (Finset.mem_singleton_self j))) =
      𝟙 (localFunctions N cN j) := by
  have hi : singletonArrow (singletonIndex j) j (Finset.mem_singleton_self j) =
      𝟙 (singletonIndex j) := Subsingleton.elim _ _
  have hm : nodeMap N cN
      (singletonArrow (singletonIndex j) j (Finset.mem_singleton_self j)) =
        𝟙 (node N cN (singletonIndex j)) := by
    apply Over.OverMorphism.ext
    let E := N.op ⋙ algSpec (.of R) ⋙ Over.forget (Spec (.of R))
    change E.map (singletonArrow (singletonIndex j) j (Finset.mem_singleton_self j)).op =
      𝟙 (E.obj (op (singletonIndex j)))
    rw [hi]
    exact CategoryTheory.Functor.map_id E _
  exact (congrArg (fun f : node N cN (singletonIndex j) ⟶ node N cN (singletonIndex j) =>
    relativeFunctionsMap cN.pt.left f) hm).trans
      (relativeFunctionsMap_id cN.pt.left (node N cN (singletonIndex j)))

private theorem singleton_frame_adjunct (j : J) :
    (Scheme.Modules.pullbackPushforwardAdjunction (cN.ι.app (op (singletonIndex j))).left).homEquiv
        (matchingModule N cN delta n)
        (SheafOfModules.unit (Spec (.of (N.obj (singletonIndex j)))).ringCatSheaf)
        (localCharacterTrivialization N cN hcN delta n hco hn
          (singletonIndex j) j (Finset.mem_singleton_self j)).hom =
      coordinate N cN delta n j := by
  exact coordinate_adjunct
    (Scheme.Modules.pullback (cN.ι.app (op (singletonIndex j))).left)
    (Scheme.Modules.pushforward (cN.ι.app (op (singletonIndex j))).left)
    (Scheme.Modules.pullbackPushforwardAdjunction (cN.ι.app (op (singletonIndex j))).left)
    (coordinate N cN delta n j)
    ((@Scheme.Modules.restrictFunctorIsoPullback _ _
      (originalLeg N cN (singletonIndex j)) (originalLegOpen N cN hcN (singletonIndex j))).inv.app
        (localFunctions N cN j) ≫
      (selectedFunctionsIso N cN hcN (singletonIndex j) j (Finset.mem_singleton_self j)).hom)
    (localCharacterTrivialization N cN hcN delta n hco hn
      (singletonIndex j) j (Finset.mem_singleton_self j)).hom
    (local_character_hom N cN hcN delta n hco hn
      (singletonIndex j) j (Finset.mem_singleton_self j))
    ((selected_pullback_adjunct N cN hcN (singletonIndex j) j
      (Finset.mem_singleton_self j)).trans (singleton_functions_id N cN j))

private theorem singleton_selected_frame (j : J) :
    localCharacterTrivialization N cN hcN delta n hco hn (singletonIndex j)
        (singletonIndex j).property.choose (singletonIndex j).property.choose_spec =
      localCharacterTrivialization N cN hcN delta n hco hn (singletonIndex j)
        j (Finset.mem_singleton_self j) := by
  exact singleton_value j (singletonIndex j).property.choose
    (singletonIndex j).property.choose_spec (fun k hk =>
      localCharacterTrivialization N cN hcN delta n hco hn (singletonIndex j) k hk)

/-- The retained degree-one unit adjusts the canonical arithmetic matching
coframe, on the same affine chart, at every character power. -/
def retainedUnitFrame (j : J) (d : (N.obj (singletonIndex j))ˣ) :
    (Scheme.Modules.pullback (cN.ι.app (op (singletonIndex j))).left).obj
      (matchingModule N cN delta n) ≅
        SheafOfModules.unit (Spec (.of (N.obj (singletonIndex j)))).ringCatSheaf :=
  localCharacterTrivialization N cN hcN delta n hco hn
    (singletonIndex j) j (Finset.mem_singleton_self j) ≪≫
  scalarIso (SheafOfModules.unit (Spec (.of (N.obj (singletonIndex j)))).ringCatSheaf)
    (Units.map (Scheme.ΓSpecIso (.of (N.obj (singletonIndex j)))).inv.hom.toMonoidHom (d ^ n))

private theorem retained_frame_hom (j : J) (d : (N.obj (singletonIndex j))ˣ) :
    (retainedUnitFrame N cN hcN delta n hco hn j d).hom =
      (localCharacterTrivialization N cN hcN delta n hco hn
        (singletonIndex j) j (Finset.mem_singleton_self j)).hom ≫
      Scheme.Modules.globalSectionsSmul
        (SheafOfModules.unit (Spec (.of (N.obj (singletonIndex j)))).ringCatSheaf)
        ((Scheme.ΓSpecIso (.of (N.obj (singletonIndex j)))).inv
          ((d : N.obj (singletonIndex j)) ^ n)) := by
  exact congrArg (fun x : N.obj (singletonIndex j) =>
    (localCharacterTrivialization N cN hcN delta n hco hn
      (singletonIndex j) j (Finset.mem_singleton_self j)).hom ≫
    Scheme.Modules.globalSectionsSmul
      (SheafOfModules.unit (Spec (.of (N.obj (singletonIndex j)))).ringCatSheaf)
      ((Scheme.ΓSpecIso (.of (N.obj (singletonIndex j)))).inv x))
        (Units.val_pow_eq_pow_val d n)

variable (r : ∀ j, N.obj (singletonIndex j))
    (hr : ∀ (s : {s : Finset J // s.Nonempty}) j (hj : j ∈ s.val) k (hk : k ∈ s.val),
      (N.map (singletonArrow s j hj)).hom (r j) =
        (N.map (singletonArrow s k hk)).hom (r k) * (delta s j hj k hk : N.obj s))

private theorem matching_section_coordinate (j : J) :
    pullSection (cN.ι.app (op (singletonIndex j))).left (matchingModule N cN delta n)
        (coefficientMatchingSection N cN delta r hr n) ≫
      (localCharacterTrivialization N cN hcN delta n hco hn
        (singletonIndex j) j (Finset.mem_singleton_self j)).hom =
      Scheme.Modules.globalSectionsSmul
        (SheafOfModules.unit (Spec (.of (N.obj (singletonIndex j)))).ringCatSheaf)
        ((Scheme.ΓSpecIso (.of (N.obj (singletonIndex j)))).inv ((r j) ^ n)) := by
  exact section_by_adjunct
    (Scheme.Modules.pullback (cN.ι.app (op (singletonIndex j))).left)
    (Scheme.Modules.pushforward (cN.ι.app (op (singletonIndex j))).left)
    (Scheme.Modules.pullbackPushforwardAdjunction (cN.ι.app (op (singletonIndex j))).left)
    (Scheme.Modules.pullbackObjUnitIso (cN.ι.app (op (singletonIndex j))).left)
    (coefficientMatchingSection N cN delta r hr n)
    (localCharacterTrivialization N cN hcN delta n hco hn
      (singletonIndex j) j (Finset.mem_singleton_self j)).hom
    (coordinate N cN delta n j)
    (Scheme.Modules.globalSectionsSmul
      (SheafOfModules.unit (Spec (.of (N.obj (singletonIndex j)))).ringCatSheaf)
      ((Scheme.ΓSpecIso (.of (N.obj (singletonIndex j)))).inv ((r j) ^ n)))
    (SheafOfModules.unitToPushforwardObjUnit
      (cN.ι.app (op (singletonIndex j))).left.toRingCatSheafHom)
    (singleton_frame_adjunct N cN hcN delta n hco hn j)
    (Scheme.Modules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitIso_hom
      (cN.ι.app (op (singletonIndex j))).left)
    (coefficientMatchingSection_coordinate N cN delta r hr n j)

/-- In the adjusted arithmetic coframe the retained section has coordinate
equal to the corresponding power of the coefficient times the retained unit. -/
theorem retainedUnitFrame_section (j : J) (d : (N.obj (singletonIndex j))ˣ) :
    pullSection (cN.ι.app (op (singletonIndex j))).left (matchingModule N cN delta n)
        (coefficientMatchingSection N cN delta r hr n) ≫
      (retainedUnitFrame N cN hcN delta n hco hn j d).hom =
      Scheme.Modules.globalSectionsSmul
        (SheafOfModules.unit (Spec (.of (N.obj (singletonIndex j)))).ringCatSheaf)
        ((Scheme.ΓSpecIso (.of (N.obj (singletonIndex j)))).inv
          ((r j * (d : N.obj (singletonIndex j))) ^ n)) := by
  have hc := congrArg (fun t => t ≫ Scheme.Modules.globalSectionsSmul
    (SheafOfModules.unit (Spec (.of (N.obj (singletonIndex j)))).ringCatSheaf)
    ((Scheme.ΓSpecIso (.of (N.obj (singletonIndex j)))).inv
      ((d : N.obj (singletonIndex j)) ^ n)))
    (matching_section_coordinate N cN hcN delta n hco hn r hr j)
  exact (congrArg (fun t =>
    pullSection (cN.ι.app (op (singletonIndex j))).left (matchingModule N cN delta n)
      (coefficientMatchingSection N cN delta r hr n) ≫ t)
    (retained_frame_hom N cN hcN delta n hco hn j d)).trans
    ((Category.assoc _ _ _).symm.trans (hc.trans (affine_smul_power (N.obj (singletonIndex j))
      (SheafOfModules.unit (Spec (.of (N.obj (singletonIndex j)))).ringCatSheaf)
        (r j) (d : N.obj (singletonIndex j)) n)))

end Arithmetic

section Scalar
variable {R K J : Type u} [CommRing R] [CommRing K]
    (N : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} R)
    (F : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} K)
    [hNopen : ∀ {s t} (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (N.map f).hom.toRingHom))]
    [hFopen : ∀ {s t} (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (F.map f).hom.toRingHom))]
    [hNdir : ((N.op ⋙ algSpec (.of R) ⋙ Over.forget (Spec (.of R))) ⋙
      Scheme.forget).IsLocallyDirected]
    [hFdir : ((F.op ⋙ algSpec (.of K) ⋙ Over.forget (Spec (.of K))) ⋙
      Scheme.forget).IsLocallyDirected]
    (cN : Cocone (N.op ⋙ algSpec (.of R))) (hcN : IsColimit cN)
    (cF : Cocone (F.op ⋙ algSpec (.of K))) (hcF : IsColimit cF)
    (v : N ⋙ forget₂ (CommAlgCat R) CommRingCat ⟶
      F ⋙ forget₂ (CommAlgCat K) CommRingCat)
    (q : cF.pt.left ⟶ cN.pt.left)
    (hq : ∀ s, Spec.map (v.app s) ≫ (cN.ι.app (op s)).left =
      (cF.ι.app (op s)).left ≫ q)
    (deltaN : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val)
      (k : J) (_ : k ∈ s.val), (N.obj s)ˣ)
    (deltaF : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val)
      (k : J) (_ : k ∈ s.val), (F.obj s)ˣ)
    (hd : ∀ s j hj k hk, (v.app s).hom (deltaN s j hj k hk : N.obj s) =
      (deltaF s j hj k hk : F.obj s)) (n : ℕ)
    (hcoN : ∀ s j hj k hk l hl,
      deltaN s j hj l hl = deltaN s k hk l hl * deltaN s j hj k hk)
    (hnN : ∀ s t (f : s ⟶ t) j hj k hk,
      Units.map (N.map f).hom.toMonoidHom (deltaN s j hj k hk) =
        deltaN t j ((leOfHom f) hj) k ((leOfHom f) hk))
    (hcoF : ∀ s j hj k hk l hl,
      deltaF s j hj l hl = deltaF s k hk l hl * deltaF s j hj k hk)
    (hnF : ∀ s t (f : s ⟶ t) j hj k hk,
      Units.map (F.map f).hom.toMonoidHom (deltaF s j hj k hk) =
        deltaF t j ((leOfHom f) hj) k ((leOfHom f) hk))

private theorem matching_frame_scalar (j : J) :
    (Scheme.Modules.pullback (cF.ι.app (op (singletonIndex j))).left).map
        (matchingPullbackIso N F cN hcN cF hcF v q hq deltaN deltaF hd n
          hcoN hnN hcoF hnF).hom ≫
      (localCharacterTrivialization F cF hcF deltaF n hcoF hnF
        (singletonIndex j) j (Finset.mem_singleton_self j)).hom =
      (squareFrameIso q (cF.ι.app (op (singletonIndex j))).left
        (cN.ι.app (op (singletonIndex j))).left (Spec.map (v.app (singletonIndex j)))
        (hq (singletonIndex j)) (matchingModule N cN deltaN n)
        (localCharacterTrivialization N cN hcN deltaN n hcoN hnN
          (singletonIndex j) j (Finset.mem_singleton_self j))).hom := by
  let : IsOpenImmersion (cN.ι.app (op (singletonIndex j))).left :=
    (retained_prior_charts N cN hcN).1 (singletonIndex j)
  let : IsOpenImmersion (cF.ι.app (op (singletonIndex j))).left :=
    (retained_prior_charts F cF hcF).1 (singletonIndex j)
  have hN := singleton_frame_adjunct N cN hcN deltaN n hcoN hnN j
  have hF := singleton_frame_adjunct F cF hcF deltaF n hcoF hnF j
  have ht := squareFrameIso_transpose q
    (cF.ι.app (op (singletonIndex j))).left (cN.ι.app (op (singletonIndex j))).left
    (Spec.map (v.app (singletonIndex j))) (hq (singletonIndex j))
    (matchingModule N cN deltaN n)
    (localCharacterTrivialization N cN hcN deltaN n hcoN hnN
      (singletonIndex j) j (Finset.mem_singleton_self j))
  have hs := congrArg (fun c =>
    (Scheme.Modules.pullback (cF.ι.app (op (singletonIndex j))).left).map
      (((Scheme.Modules.pullbackPushforwardAdjunction q).homEquiv (matchingModule N cN deltaN n)
        (relativeFunctionsObj cF.pt.left (node F cF (singletonIndex j)))).symm
          (c ≫ functionsScalarMap q (node F cF (singletonIndex j))
            (node N cN (singletonIndex j)) (Spec.map (v.app (singletonIndex j)))
            (hq (singletonIndex j)))) ≫
      (Scheme.Modules.pullbackPushforwardAdjunction
        (cF.ι.app (op (singletonIndex j))).left).counit.app
          (SheafOfModules.unit (Spec (.of (F.obj (singletonIndex j)))).ringCatSheaf)) hN
  exact coordinate_square
    (Scheme.Modules.pullback (cF.ι.app (op (singletonIndex j))).left)
    (matchingPullbackIso N F cN hcN cF hcF v q hq deltaN deltaF hd n hcoN hnN hcoF hnF).hom
    (coordinate F cF deltaF n j)
    (((Scheme.Modules.pullbackPushforwardAdjunction q).homEquiv (matchingModule N cN deltaN n)
      (relativeFunctionsObj cF.pt.left (node F cF (singletonIndex j)))).symm
        (coordinate N cN deltaN n j ≫ functionsScalarMap q (node F cF (singletonIndex j))
          (node N cN (singletonIndex j)) (Spec.map (v.app (singletonIndex j)))
          (hq (singletonIndex j))))
    (localCharacterTrivialization F cF hcF deltaF n hcoF hnF
      (singletonIndex j) j (Finset.mem_singleton_self j)).hom
    ((Scheme.Modules.pullbackPushforwardAdjunction
      (cF.ι.app (op (singletonIndex j))).left).counit.app
        (SheafOfModules.unit (Spec (.of (F.obj (singletonIndex j)))).ringCatSheaf))
    (squareFrameIso q (cF.ι.app (op (singletonIndex j))).left
      (cN.ι.app (op (singletonIndex j))).left (Spec.map (v.app (singletonIndex j)))
      (hq (singletonIndex j)) (matchingModule N cN deltaN n)
      (localCharacterTrivialization N cN hcN deltaN n hcoN hnN
        (singletonIndex j) j (Finset.mem_singleton_self j))).hom
    (frame_counit (Scheme.Modules.pullback (cF.ι.app (op (singletonIndex j))).left)
      (Scheme.Modules.pushforward (cF.ι.app (op (singletonIndex j))).left)
      (Scheme.Modules.pullbackPushforwardAdjunction (cF.ι.app (op (singletonIndex j))).left)
      (coordinate F cF deltaF n j)
      (localCharacterTrivialization F cF hcF deltaF n hcoF hnF
        (singletonIndex j) j (Finset.mem_singleton_self j)).hom hF)
    (matchingPullbackHom_coordinate N F cN cF v q hq deltaN deltaF hd n j)
    (hs.symm.trans ht)

/-- The adjusted arithmetic coframe has its prescribed scalar image under the
chosen matching-line comparison, for every power and without a flat scalar map. -/
theorem retainedUnitFrame_scalar (j : J)
    (dN : (N.obj (singletonIndex j))ˣ) (dF : (F.obj (singletonIndex j))ˣ)
    (hu : (v.app (singletonIndex j)).hom (dN : N.obj (singletonIndex j)) =
      (dF : F.obj (singletonIndex j))) :
    (Scheme.Modules.pullback (cF.ι.app (op (singletonIndex j))).left).map
        (matchingPullbackIso N F cN hcN cF hcF v q hq deltaN deltaF hd n hcoN hnN hcoF hnF).hom ≫
      (retainedUnitFrame F cF hcF deltaF n hcoF hnF j dF).hom =
      (squareFrameIso q (cF.ι.app (op (singletonIndex j))).left
        (cN.ι.app (op (singletonIndex j))).left (Spec.map (v.app (singletonIndex j)))
        (hq (singletonIndex j)) (matchingModule N cN deltaN n)
        (retainedUnitFrame N cN hcN deltaN n hcoN hnN j dN)).hom := by
  have hsquare := square_frame_scalar q
    (cF.ι.app (op (singletonIndex j))).left (cN.ι.app (op (singletonIndex j))).left
    (Spec.map (v.app (singletonIndex j))) (hq (singletonIndex j))
    (matchingModule N cN deltaN n)
    (localCharacterTrivialization N cN hcN deltaN n hcoN hnN
      (singletonIndex j) j (Finset.mem_singleton_self j))
    (retainedUnitFrame N cN hcN deltaN n hcoN hnN j dN)
    ((Scheme.ΓSpecIso (.of (N.obj (singletonIndex j)))).inv
      ((dN : N.obj (singletonIndex j)) ^ n))
    (retained_frame_hom N cN hcN deltaN n hcoN hnN j dN)
  have hvalue := coefficient_power_scalar (v.app (singletonIndex j))
    (dN : N.obj (singletonIndex j)) (dF : F.obj (singletonIndex j)) hu n
  have hright := hsquare.trans (congrArg (fun r =>
    (squareFrameIso q (cF.ι.app (op (singletonIndex j))).left
      (cN.ι.app (op (singletonIndex j))).left (Spec.map (v.app (singletonIndex j)))
      (hq (singletonIndex j)) (matchingModule N cN deltaN n)
      (localCharacterTrivialization N cN hcN deltaN n hcoN hnN
        (singletonIndex j) j (Finset.mem_singleton_self j))).hom ≫
      Scheme.Modules.globalSectionsSmul
        (SheafOfModules.unit (Spec (.of (F.obj (singletonIndex j)))).ringCatSheaf) r) hvalue)
  have hleft := congrArg (fun t =>
    (Scheme.Modules.pullback (cF.ι.app (op (singletonIndex j))).left).map
      (matchingPullbackIso N F cN hcN cF hcF v q hq deltaN deltaF hd n hcoN hnN hcoF hnF).hom ≫ t)
      (retained_frame_hom F cF hcF deltaF n hcoF hnF j dF)
  exact hleft.trans ((Category.assoc _ _ _).symm.trans
    ((congrArg (fun t => t ≫ Scheme.Modules.globalSectionsSmul
      (SheafOfModules.unit (Spec (.of (F.obj (singletonIndex j)))).ringCatSheaf)
      ((Scheme.ΓSpecIso (.of (F.obj (singletonIndex j)))).inv
        ((dF : F.obj (singletonIndex j)) ^ n)))
      (matching_frame_scalar N F cN hcN cF hcF v q hq deltaN deltaF hd n hcoN hnN hcoF hnF j)).trans
        hright.symm))

end Scalar

section Append
variable {R K J : Type u} [CommRing R] [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K) (word : List G.rootBase.support) (i : G.rootBase.support)
    (N : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} R)
    (F : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} K)
    [hNopen : ∀ {s t} (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (N.map f).hom.toRingHom))]
    [hFopen : ∀ {s t} (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (F.map f).hom.toRingHom))]
    [hNdir : ((N.op ⋙ algSpec (.of R) ⋙ Over.forget (Spec (.of R))) ⋙
      Scheme.forget).IsLocallyDirected]
    [hFdir : ((F.op ⋙ algSpec (.of K) ⋙ Over.forget (Spec (.of K))) ⋙
      Scheme.forget).IsLocallyDirected]
    (cN : Cocone (N.op ⋙ algSpec (.of R))) (hcN : IsColimit cN)
    (cF : Cocone (F.op ⋙ algSpec (.of K))) (hcF : IsColimit cF)
    (v : N ⋙ forget₂ (CommAlgCat R) CommRingCat ⟶
      F ⋙ forget₂ (CommAlgCat K) CommRingCat)
    (qN : cF.pt.left ⟶ cN.pt.left)
    (hqN : ∀ s, Spec.map (v.app s) ≫ (cN.ι.app (op s)).left =
      (cF.ι.app (op s)).left ≫ qN)
    (q : cF.pt.left ⟶ bsdhScheme G (word ++ [i]))
    (point : J → G.points)
    (a : ∀ j, (algSpec (.of K)).obj (op (F.obj (singletonIndex j))) ⟶
      (oppositeUnipotentVariety G).toOver)
    (ha : ∀ j, (a j).left ≫ (flagChartMorphism G (point j)).left =
      (cF.ι.app (op (singletonIndex j))).left ≫ (q ≫ bsdhMap G (word ++ [i])))
    (beta : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val)
      (k : J) (_ : k ∈ s.val),
      (algSpec (.of K)).obj (op (F.obj s)) ⟶ (borelVariety G).toOver)
    (hgroup : ∀ s j hj k hk,
      chartLift G F point a s j hj =
        chartLift G F point a s k hk * (beta s j hj k hk ≫ borelInclusion G))
    (hcoF : ∀ s j hj k hk l hl, wordTransitionUnit G F beta s j hj l hl =
      wordTransitionUnit G F beta s k hk l hl * wordTransitionUnit G F beta s j hj k hk)
    (hnF : ∀ s t (f : s ⟶ t) j hj k hk,
      Units.map (F.map f).hom.toMonoidHom (wordTransitionUnit G F beta s j hj k hk) =
        wordTransitionUnit G F beta t j ((leOfHom f) hj) k ((leOfHom f) hk))
    (deltaN : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val)
      (k : J) (_ : k ∈ s.val), (N.obj s)ˣ)
    (hd : ∀ s j hj k hk, (v.app s).hom (deltaN s j hj k hk : N.obj s) =
      (wordTransitionUnit G F beta s j hj k hk : F.obj s))
    (hcoN : ∀ s j hj k hk l hl,
      deltaN s j hj l hl = deltaN s k hk l hl * deltaN s j hj k hk)
    (hnN : ∀ s t (f : s ⟶ t) j hj k hk,
      Units.map (N.map f).hom.toMonoidHom (deltaN s j hj k hk) =
        deltaN t j ((leOfHom f) hj) k ((leOfHom f) hk))
    (l : J) (V : Over (Spec (.of K))) (g : G.points)
    (b : V ⟶ (oppositeUnipotentVariety G).toOver)
    (c : V ⊗ (schubertVariety G
      (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver ⟶
        Over.mk (bsdhToSpec G (word ++ [i])))
    (hend : c.left ≫ (bsdhAppendIso G word i).hom.left ≫
      pullback.snd (bsdhMap G word) (flagBundleProjection G
        (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val))) =
      (b ⊗ₘ 𝟙 (schubertVariety G
        (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver).left ≫
          flagBundleChart G _ g)
    (B : CommAlgCat.{u} K) (p : (algSpec (.of K)).obj (op B) ⟶ V)
    (j : Fin 2) (k : Spec (.of (F.obj (singletonIndex l))) ⟶ Spec (.of (Polynomial B)))
    (hk : (cF.ι.app (op (singletonIndex l))).left ≫ q =
      k ≫ projectiveLinePolynomialChart B ⟨j⟩ ≫ projectiveAppendChart G i B p c)
    (d : (N.obj (singletonIndex l))ˣ)
    (hu : (v.app (singletonIndex l)).hom (d : N.obj (singletonIndex l)) =
      (appendFrameUnit G word i F cF hcF q point a ha beta hgroup hcoF hnF
        (singletonIndex l) V g b c hend B p ⟨j⟩ k hk : F.obj (singletonIndex l)))

include hu in
/-- The adjusted arithmetic coframe has the prescribed polynomial append
coframe as its scalar image on the same fixed chart, for every character power. -/
theorem retainedAppendFrame_scalar (n : ℕ) :
    (Scheme.Modules.pullback (cF.ι.app (op (singletonIndex l))).left).map
        (matchingPullbackIso N F cN hcN cF hcF v qN hqN deltaN
          (wordTransitionUnit G F beta) hd n hcoN hnN hcoF hnF).hom ≫
      (appendPowerFrame G word i F cF hcF q point a ha beta hgroup hcoF hnF
        (singletonIndex l) V g b c hend B p j k hk n).hom =
      (squareFrameIso qN (cF.ι.app (op (singletonIndex l))).left
        (cN.ι.app (op (singletonIndex l))).left (Spec.map (v.app (singletonIndex l)))
        (hqN (singletonIndex l)) (matchingModule N cN deltaN n)
        (retainedUnitFrame N cN hcN deltaN n hcoN hnN l d)).hom := by
  let u := appendFrameUnit G word i F cF hcF q point a ha beta hgroup hcoF hnF
    (singletonIndex l) V g b c hend B p ⟨j⟩ k hk
  have hp := appendPowerFrame_unit G word i F cF hcF q point a ha beta hgroup hcoF hnF
    (singletonIndex l) V g b c hend B p j k hk n
  have hselected := congrArg (fun e :
    (Scheme.Modules.pullback (cF.ι.app (op (singletonIndex l))).left).obj
      (matchingModule F cF (wordTransitionUnit G F beta) n) ≅
        SheafOfModules.unit (Spec (.of (F.obj (singletonIndex l)))).ringCatSheaf => e.hom ≫
    Scheme.Modules.globalSectionsSmul
      (SheafOfModules.unit (Spec (.of (F.obj (singletonIndex l)))).ringCatSheaf)
      ((Scheme.ΓSpecIso (.of (F.obj (singletonIndex l)))).inv
        ((u : F.obj (singletonIndex l)) ^ n)))
    (singleton_selected_frame F cF hcF (wordTransitionUnit G F beta) n hcoF hnF l)
  have hframe := hp.trans (hselected.trans
    (retained_frame_hom F cF hcF (wordTransitionUnit G F beta) n hcoF hnF l u).symm)
  exact (congrArg (fun t =>
    (Scheme.Modules.pullback (cF.ι.app (op (singletonIndex l))).left).map
      (matchingPullbackIso N F cN hcN cF hcF v qN hqN deltaN
        (wordTransitionUnit G F beta) hd n hcoN hnN hcoF hnF).hom ≫ t) hframe).trans
    (retainedUnitFrame_scalar N F cN hcN cF hcF v qN hqN deltaN
      (wordTransitionUnit G F beta) hd n hcoN hnN hcoF hnF l d u hu)

end Append

end SchubertGeometry.RetainedCharacter
