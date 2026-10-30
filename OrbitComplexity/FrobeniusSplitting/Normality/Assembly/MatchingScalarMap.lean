import OrbitComplexity.FrobeniusSplitting.Normality.Assembly.FunctionsScalarMap
import OrbitComplexity.FrobeniusSplitting.Normality.Assembly.MatchingAdjunction
import OrbitComplexity.FrobeniusSplitting.Normality.Assembly.MatchingSections
import OrbitComplexity.FrobeniusSplitting.Modules.MatchingLimits
import TauCeti.AlgebraicGeometry.Modules.Pullback
import Mathlib.CategoryTheory.Adjunction.Limits
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-!
# Scalar morphisms of character matching modules

A natural map of affine coefficient diagrams preserving the transition units
induces a morphism from the pullback of the original matching module to the new
matching module. Its construction uses preservation of limits by pushforward.
The same morphism carries coefficient sections to their scalar images.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open FrobeniusSplitting.CharacterLine

noncomputable section

universe u

namespace FrobeniusSplitting.RetainedCharacter

open private singletonIndex singletonArrow localFunctions coefficientSection
  from OrbitComplexity.FrobeniusSplitting.Modules.MatchingModule

private theorem affine_scalar_square {I : Type u} [Category I]
    (N F : I ⥤ CommRingCat.{u}) (v : N ⟶ F) {s t : I} (f : s ⟶ t) :
    Spec.map (F.map f) ≫ Spec.map (v.app s) =
      Spec.map (v.app t) ≫ Spec.map (N.map f) := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  exact congrArg Spec.map (v.naturality f).symm

private theorem matching_scalar_rule {C : Type*} [Category C]
    {M A B D P Q T : C} (x : M ⟶ A) (y : M ⟶ B)
    (a : A ⟶ D) (b : B ⟶ D) (u : D ⟶ D)
    (f : A ⟶ P) (g : B ⟶ Q) (h : D ⟶ T)
    (c : P ⟶ T) (d : Q ⟶ T) (v : T ⟶ T)
    (ha : a ≫ h = f ≫ c) (hb : b ≫ h = g ≫ d)
    (hu : u ≫ h = h ≫ v) (hxy : x ≫ a = y ≫ b ≫ u) :
    (x ≫ f) ≫ c = (y ≫ g) ≫ d ≫ v := by
  calc
    (x ≫ f) ≫ c = x ≫ (f ≫ c) := Category.assoc _ _ _
    _ = x ≫ (a ≫ h) := congrArg (fun z => x ≫ z) ha.symm
    _ = (x ≫ a) ≫ h := (Category.assoc _ _ _).symm
    _ = (y ≫ b ≫ u) ≫ h := congrArg (fun z => z ≫ h) hxy
    _ = y ≫ b ≫ (u ≫ h) := by simp only [Category.assoc]
    _ = y ≫ b ≫ (h ≫ v) := congrArg (fun z => y ≫ b ≫ z) hu
    _ = y ≫ (b ≫ h) ≫ v := by simp only [Category.assoc]
    _ = y ≫ (g ≫ d) ≫ v := congrArg (fun z => y ≫ z ≫ v) hb
    _ = (y ≫ g) ≫ d ≫ v := by simp only [Category.assoc]

private theorem transport_property {T : Type*} (P : T → Prop) {x y : T}
    (h : x = y) (hx : P x) : P y := h ▸ hx

private theorem section_coordinate_rule {C D : Type*} [Category C] [Category D]
    (G : C ⥤ D) {Q M A : C} {P B L : D}
    (x : P ⟶ B) (f : B ⟶ G.obj M) (c : B ⟶ L) (h : L ⟶ G.obj A)
    (e : P ⟶ G.obj Q) (y : Q ⟶ M) (g : M ⟶ A) (r : P ⟶ L) (z : Q ⟶ A)
    (hf : f ≫ G.map g = c ≫ h) (hx : x ≫ c = r)
    (hr : r ≫ h = e ≫ G.map z) (hy : y ≫ g = z) :
    (x ≫ f) ≫ G.map g = (e ≫ G.map y) ≫ G.map g := by
  calc
    (x ≫ f) ≫ G.map g = x ≫ (f ≫ G.map g) := Category.assoc _ _ _
    _ = x ≫ (c ≫ h) := congrArg (fun t => x ≫ t) hf
    _ = (x ≫ c) ≫ h := (Category.assoc _ _ _).symm
    _ = r ≫ h := congrArg (fun t => t ≫ h) hx
    _ = e ≫ G.map z := hr
    _ = e ≫ G.map (y ≫ g) := congrArg (fun t => e ≫ G.map t) hy.symm
    _ = (e ≫ G.map y) ≫ G.map g :=
      (congrArg (fun t => e ≫ t) (G.map_comp y g)).trans (Category.assoc _ _ _).symm

variable {R K J : Type u} [CommRing R] [CommRing K]
    (N : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} R)
    (F : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} K)
    (cN : Cocone (N.op ⋙ algSpec (.of R)))
    (cF : Cocone (F.op ⋙ algSpec (.of K)))
    (v : N ⋙ forget₂ (CommAlgCat R) CommRingCat ⟶
      F ⋙ forget₂ (CommAlgCat K) CommRingCat)
    (q : cF.pt.left ⟶ cN.pt.left)
    (hq : ∀ s, Spec.map (v.app s) ≫ (cN.ι.app (op s)).left =
      (cF.ι.app (op s)).left ≫ q)

private def scalarNodeMap (s : {s : Finset J // s.Nonempty}) :
    relativeFunctionsObj cN.pt.left (node N cN s) ⟶
      (Scheme.Modules.pushforward q).obj (relativeFunctionsObj cF.pt.left (node F cF s)) :=
  functionsScalarMap q (node F cF s) (node N cN s) (Spec.map (v.app s)) (hq s)

private theorem scalarNodeMap_natural {s t : {s : Finset J // s.Nonempty}}
    (f : s ⟶ t) :
    relativeFunctionsMap cN.pt.left (nodeMap N cN f) ≫
        scalarNodeMap N F cN cF v q hq t =
      scalarNodeMap N F cN cF v q hq s ≫
        (Scheme.Modules.pushforward q).map
          (relativeFunctionsMap cF.pt.left (nodeMap F cF f)) :=
  functionsScalarMap_natural q (nodeMap F cF f) (nodeMap N cN f)
    (Spec.map (v.app t)) (Spec.map (v.app s)) (hq t) (hq s)
    (affine_scalar_square (N ⋙ forget₂ (CommAlgCat R) CommRingCat)
      (F ⋙ forget₂ (CommAlgCat K) CommRingCat) v f)

variable
    (deltaN : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val)
      (k : J) (_ : k ∈ s.val), (N.obj s)ˣ)
    (deltaF : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val)
      (k : J) (_ : k ∈ s.val), (F.obj s)ˣ)
    (hd : ∀ s j hj k hk, (v.app s).hom (deltaN s j hj k hk : N.obj s) =
      (deltaF s j hj k hk : F.obj s))
    (n : ℕ)

include hd in
private theorem scalarNodeMap_smul
    (s : {s : Finset J // s.Nonempty}) (j : J) (hj : j ∈ s.val)
    (k : J) (hk : k ∈ s.val) :
    relativeFunctionsSmul cN.pt.left (node N cN s)
        (coefficientSection N cN s ((deltaN s j hj k hk : N.obj s) ^ n)) ≫
        scalarNodeMap N F cN cF v q hq s =
      scalarNodeMap N F cN cF v q hq s ≫ (Scheme.Modules.pushforward q).map
        (relativeFunctionsSmul cF.pt.left (node F cF s)
          (coefficientSection F cF s ((deltaF s j hj k hk : F.obj s) ^ n))) := by
  have he := coefficientSection_scalar (v.app s) (deltaN s j hj k hk : N.obj s) n
  rw [hd s j hj k hk] at he
  change (Spec.map (v.app s)).appTop
      (coefficientSection N cN s ((deltaN s j hj k hk : N.obj s) ^ n)) =
    coefficientSection F cF s ((deltaF s j hj k hk : F.obj s) ^ n) at he
  have h := functionsScalarMap_smul q (node F cF s) (node N cN s)
    (Spec.map (v.app s)) (hq s)
      (coefficientSection N cN s ((deltaN s j hj k hk : N.obj s) ^ n))
  exact transport_property
    (fun z : Γ((node F cF s).left, ⊤) =>
      relativeFunctionsSmul cN.pt.left (node N cN s)
          (coefficientSection N cN s ((deltaN s j hj k hk : N.obj s) ^ n)) ≫
          scalarNodeMap N F cN cF v q hq s =
        scalarNodeMap N F cN cF v q hq s ≫ (Scheme.Modules.pushforward q).map
          (relativeFunctionsSmul cF.pt.left (node F cF s) z)) he h

include hd in
private theorem scalar_coordinates_match
    (s : {s : Finset J // s.Nonempty}) (j : J) (hj : j ∈ s.val)
    (k : J) (hk : k ∈ s.val) :
    (coordinate N cN deltaN n j ≫ scalarNodeMap N F cN cF v q hq (singletonIndex j)) ≫
        (Scheme.Modules.pushforward q).map
          (relativeFunctionsMap cF.pt.left (nodeMap F cF (singletonArrow s j hj))) =
      (coordinate N cN deltaN n k ≫ scalarNodeMap N F cN cF v q hq (singletonIndex k)) ≫
        (Scheme.Modules.pushforward q).map
          (relativeFunctionsMap cF.pt.left (nodeMap F cF (singletonArrow s k hk))) ≫
        (Scheme.Modules.pushforward q).map
          (relativeFunctionsSmul cF.pt.left (node F cF s)
            (coefficientSection F cF s ((deltaF s j hj k hk : F.obj s) ^ n))) :=
  matching_scalar_rule _ _ _ _ _ _ _ _ _ _ _
    (scalarNodeMap_natural N F cN cF v q hq (singletonArrow s j hj))
    (scalarNodeMap_natural N F cN cF v q hq (singletonArrow s k hk))
    (scalarNodeMap_smul N F cN cF v q hq deltaN deltaF hd n s j hj k hk)
    (coordinate_matching N cN deltaN n s j hj k hk)

/-- A scalar map of coefficient diagrams induces the matching-module morphism
into pushforward along the specified map of glued schemes. -/
def matchingPushforward : matchingModule N cN deltaN n ⟶
    (Scheme.Modules.pushforward q).obj (matchingModule F cF deltaF n) :=
  mappedLift F cF deltaF n (Scheme.Modules.pushforward q)
    (fun j => coordinate N cN deltaN n j ≫
      scalarNodeMap N F cN cF v q hq (singletonIndex j))
    (scalar_coordinates_match N F cN cF v q hq deltaN deltaF hd n)

/-- The pushed-forward matching morphism has the prescribed scalar coordinate. -/
theorem matchingPushforward_coordinate (j : J) :
    matchingPushforward N F cN cF v q hq deltaN deltaF hd n ≫
        (Scheme.Modules.pushforward q).map (coordinate F cF deltaF n j) =
      coordinate N cN deltaN n j ≫
        functionsScalarMap q (node F cF (singletonIndex j))
          (node N cN (singletonIndex j)) (Spec.map (v.app (singletonIndex j)))
            (hq (singletonIndex j)) :=
  mappedLift_coordinate F cF deltaF n (Scheme.Modules.pushforward q)
    (fun j => coordinate N cN deltaN n j ≫
      scalarNodeMap N F cN cF v q hq (singletonIndex j))
    (scalar_coordinates_match N F cN cF v q hq deltaN deltaF hd n) j

/-- Scalar comparison of matching modules, defined by transposition of the
matching morphism into pushforward. -/
def matchingPullbackHom :
    (Scheme.Modules.pullback q).obj (matchingModule N cN deltaN n) ⟶
      matchingModule F cF deltaF n :=
  ((Scheme.Modules.pullbackPushforwardAdjunction q).homEquiv _ _).symm
    (matchingPushforward N F cN cF v q hq deltaN deltaF hd n)

/-- Each coordinate of the pullback morphism is the transpose of its scalar
coordinate on the original matching module. -/
theorem matchingPullbackHom_coordinate (j : J) :
    matchingPullbackHom N F cN cF v q hq deltaN deltaF hd n ≫
        coordinate F cF deltaF n j =
      ((Scheme.Modules.pullbackPushforwardAdjunction q).homEquiv _ _).symm
        (coordinate N cN deltaN n j ≫
          functionsScalarMap q (node F cF (singletonIndex j))
            (node N cN (singletonIndex j)) (Spec.map (v.app (singletonIndex j)))
              (hq (singletonIndex j))) :=
  adjoint_coordinate (Scheme.Modules.pullbackPushforwardAdjunction q)
    (matchingPushforward N F cN cF v q hq deltaN deltaF hd n)
    (coordinate F cF deltaF n j) _
    (matchingPushforward_coordinate N F cN cF v q hq deltaN deltaF hd n j)

variable
    (rN : ∀ j : J, N.obj (singletonIndex j))
    (rF : ∀ j : J, F.obj (singletonIndex j))
    (hrN : ∀ (s : {s : Finset J // s.Nonempty}) j (hj : j ∈ s.val) k (hk : k ∈ s.val),
      (N.map (singletonArrow s j hj)).hom (rN j) =
        (N.map (singletonArrow s k hk)).hom (rN k) * (deltaN s j hj k hk : N.obj s))
    (hrF : ∀ (s : {s : Finset J // s.Nonempty}) j (hj : j ∈ s.val) k (hk : k ∈ s.val),
      (F.map (singletonArrow s j hj)).hom (rF j) =
        (F.map (singletonArrow s k hk)).hom (rF k) * (deltaF s j hj k hk : F.obj s))
    (hv : ∀ j, (v.app (singletonIndex j)).hom (rN j) = rF j)

include hv in
private theorem scalar_coefficient_section (j : J) :
    ringCoefficientSection N cN j ((rN j) ^ n) ≫
        scalarNodeMap N F cN cF v q hq (singletonIndex j) =
      SheafOfModules.unitToPushforwardObjUnit q.toRingCatSheafHom ≫
        (Scheme.Modules.pushforward q).map
          (ringCoefficientSection F cF j ((rF j) ^ n)) := by
  have he := coefficientSection_scalar (v.app (singletonIndex j)) (rN j) n
  rw [hv j] at he
  change (Spec.map (v.app (singletonIndex j))).appTop
      (coefficientSection N cN (singletonIndex j) ((rN j) ^ n)) =
    coefficientSection F cF (singletonIndex j) ((rF j) ^ n) at he
  have h := functionsScalarMap_coefficient q (node F cF (singletonIndex j))
    (node N cN (singletonIndex j)) (Spec.map (v.app (singletonIndex j)))
    (hq (singletonIndex j))
      (coefficientSection N cN (singletonIndex j) ((rN j) ^ n))
  exact transport_property
    (fun z : Γ((node F cF (singletonIndex j)).left, ⊤) =>
      ringCoefficientSection N cN j ((rN j) ^ n) ≫
          scalarNodeMap N F cN cF v q hq (singletonIndex j) =
        SheafOfModules.unitToPushforwardObjUnit q.toRingCatSheafHom ≫
          (Scheme.Modules.pushforward q).map
            (relativeCoefficient cF.pt.left (node F cF (singletonIndex j)) z)) he h

include hv in
private theorem matchingPushforward_section :
    coefficientMatchingSection N cN deltaN rN hrN n ≫
        matchingPushforward N F cN cF v q hq deltaN deltaF hd n =
      SheafOfModules.unitToPushforwardObjUnit q.toRingCatSheafHom ≫
        (Scheme.Modules.pushforward q).map
          (coefficientMatchingSection F cF deltaF rF hrF n) := by
  apply adjoint_coordinate_ext (Scheme.Modules.pullbackPushforwardAdjunction q)
    (fun j => localFunctions F cF j) (coordinate F cF deltaF n)
    (fun f g h => coordinate_hom_ext F cF deltaF n f g h)
  intro j
  exact section_coordinate_rule (C := cF.pt.left.Modules) (D := cN.pt.left.Modules)
    (Scheme.Modules.pushforward q)
    (Q := SheafOfModules.unit cF.pt.left.ringCatSheaf)
    (M := matchingModule F cF deltaF n) (A := localFunctions F cF j)
    (P := SheafOfModules.unit cN.pt.left.ringCatSheaf)
    (B := matchingModule N cN deltaN n) (L := localFunctions N cN j)
    (coefficientMatchingSection N cN deltaN rN hrN n)
    (matchingPushforward N F cN cF v q hq deltaN deltaF hd n)
    (coordinate N cN deltaN n j)
    (scalarNodeMap N F cN cF v q hq (singletonIndex j))
    (SheafOfModules.unitToPushforwardObjUnit q.toRingCatSheafHom)
    (coefficientMatchingSection F cF deltaF rF hrF n)
    (coordinate F cF deltaF n j)
    (ringCoefficientSection N cN j ((rN j) ^ n))
    (ringCoefficientSection F cF j ((rF j) ^ n))
    (matchingPushforward_coordinate N F cN cF v q hq deltaN deltaF hd n j)
    (coefficientMatchingSection_coordinate N cN deltaN rN hrN n j)
    (scalar_coefficient_section N F cN cF v q hq n rN rF hv j)
    (coefficientMatchingSection_coordinate F cF deltaF rF hrF n j)

include hv in
/-- Scalar comparison of matching modules carries the original coefficient
section to the new coefficient section through the pullback unit isomorphism. -/
theorem matchingPullback_section :
    (Scheme.Modules.pullbackObjUnitIso q).inv ≫
        (Scheme.Modules.pullback q).map
          (coefficientMatchingSection N cN deltaN rN hrN n) ≫
        matchingPullbackHom N F cN cF v q hq deltaN deltaF hd n =
      coefficientMatchingSection F cF deltaF rF hrF n :=
  adjoint_section (Scheme.Modules.pullbackPushforwardAdjunction q)
    (Scheme.Modules.pullbackObjUnitIso q)
    (SheafOfModules.unitToPushforwardObjUnit q.toRingCatSheafHom)
    (Scheme.Modules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitIso_hom q)
    (coefficientMatchingSection N cN deltaN rN hrN n)
    (coefficientMatchingSection F cF deltaF rF hrF n)
    (matchingPushforward N F cN cF v q hq deltaN deltaF hd n)
    (matchingPushforward_section N F cN cF v q hq deltaN deltaF hd n rN rF hrN hrF hv)

end FrobeniusSplitting.RetainedCharacter
