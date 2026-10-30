import OrbitComplexity.FrobeniusSplitting.Modules.RelativeCoefficients
import OrbitComplexity.FrobeniusSplitting.Modules.RelativeScalars
import Batteries.Tactic.Lint

/-!
# Scalar morphisms of relative function modules

A commuting square of schemes induces a morphism from relative functions on the
original base to the pushforward of relative functions on the new base. These
morphisms preserve restrictions and multiplication by global coefficients.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u

namespace FrobeniusSplitting.CharacterLine

private theorem assoc_four {C : Type*} [Category C] {A B D E F : C}
    (a : A ⟶ B) (b : B ⟶ D) (c : D ⟶ E) (d : E ⟶ F) :
    (a ≫ b ≫ c) ≫ d = a ≫ b ≫ c ≫ d :=
  (Category.assoc a (b ≫ c) d).trans
    (congrArg (fun z => a ≫ z) (Category.assoc b c d))

private theorem map_comp_right {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {X Y Z : C} {P : D}
    (u : P ⟶ F.obj X) (a : X ⟶ Y) (b : Y ⟶ Z) :
    (u ≫ F.map a) ≫ F.map b = u ≫ F.map (a ≫ b) :=
  (Category.assoc _ _ _).trans (congrArg (fun z => u ≫ z) (F.map_comp a b).symm)

private theorem compare_values {A B : Type*} (f g : A → B) (u : A → A) (v : B → B)
    (hf : ∀ a, f a = g a) (hu : ∀ a, u a = a) (hv : ∀ b, v b = b) (a : A) :
    v (f a) = g (u a) :=
  (hv (f a)).trans ((hf a).trans (congrArg g (hu a).symm))

private theorem composed_square {C : Type*} [Category C]
    {A₁ A₂ B₁ B₂ D₁ D₂ : C}
    (g : A₂ ⟶ A₁) (a₁ : A₁ ⟶ B₁) (a₂ : A₂ ⟶ B₂) (f : B₂ ⟶ B₁)
    (u₁ : B₁ ⟶ D₁) (u₂ : B₂ ⟶ D₂) (h : D₂ ⟶ D₁)
    (s₁ : A₁ ⟶ D₁) (s₂ : A₂ ⟶ D₂)
    (hmap : g ≫ a₁ = a₂ ≫ f) (hiso : f ≫ u₁ = u₂ ≫ h)
    (hs₁ : s₁ = a₁ ≫ u₁) (hs₂ : s₂ = a₂ ≫ u₂) : g ≫ s₁ = s₂ ≫ h := by
  calc
    g ≫ s₁ = g ≫ (a₁ ≫ u₁) := congrArg (fun z => g ≫ z) hs₁
    _ = (g ≫ a₁) ≫ u₁ := (Category.assoc _ _ _).symm
    _ = (a₂ ≫ f) ≫ u₁ := congrArg (fun z => z ≫ u₁) hmap
    _ = a₂ ≫ (f ≫ u₁) := Category.assoc _ _ _
    _ = a₂ ≫ (u₂ ≫ h) := congrArg (fun z => a₂ ≫ z) hiso
    _ = (a₂ ≫ u₂) ≫ h := (Category.assoc _ _ _).symm
    _ = s₂ ≫ h := congrArg (fun z => z ≫ h) hs₂.symm

private theorem pushforward_map_value {S T : Scheme.{u}} (q : T ⟶ S)
    {M N : T.Modules} (f : M ⟶ N) (V : S.Opens) (r : Γ(M, q ⁻¹ᵁ V)) :
    ((((Scheme.Modules.pushforward q).map f).val.app (op V)).hom) r =
      ((f.val.app (op (q ⁻¹ᵁ V))).hom) r := rfl

/-- Relative functions on a composite structure map identify with their iterated
pushforward to the same base. -/
def functionsPushforwardIso {S T : Scheme.{u}} (q : T ⟶ S) (X : Over T) :
    relativeFunctionsObj S (Over.mk (X.hom ≫ q)) ≅
      (Scheme.Modules.pushforward q).obj (relativeFunctionsObj T X) :=
  ((Scheme.Modules.pushforwardComp X.hom q).app
    (SheafOfModules.unit X.left.ringCatSheaf)).symm

private theorem functionsPushforwardIso_value {S T : Scheme.{u}} (q : T ⟶ S)
    (X : Over T) (V : S.Opens) (r : Γ(X.left, (X.hom ≫ q) ⁻¹ᵁ V)) :
    (((functionsPushforwardIso q X).hom).val.app (op V)).hom r = r := rfl

/-- Iterated pushforward of relative functions respects morphisms over the new base. -/
theorem functionsPushforwardIso_map {S T : Scheme.{u}} (q : T ⟶ S)
    {X Y : Over T} (f : X ⟶ Y) :
    relativeFunctionsMap S ((Over.map q).map f) ≫ (functionsPushforwardIso q X).hom =
      (functionsPushforwardIso q Y).hom ≫
        (Scheme.Modules.pushforward q).map (relativeFunctionsMap T f) := by
  apply Scheme.Modules.hom_ext
  intro V
  apply ConcreteCategory.hom_ext
  intro r
  change (((functionsPushforwardIso q X).hom).val.app (op V)).hom
      (((relativeFunctionsMap S ((Over.map q).map f)).val.app (op V)).hom r) =
    ((((Scheme.Modules.pushforward q).map (relativeFunctionsMap T f)).val.app (op V)).hom
      ((((functionsPushforwardIso q Y).hom).val.app (op V)).hom r))
  exact compare_values
    (fun z : Γ(Y.left, (Y.hom ≫ q) ⁻¹ᵁ V) =>
      ((relativeFunctionsMap S ((Over.map q).map f)).val.app (op V)).hom z)
    (fun z : Γ(Y.left, (Y.hom ≫ q) ⁻¹ᵁ V) =>
      (((Scheme.Modules.pushforward q).map (relativeFunctionsMap T f)).val.app (op V)).hom z)
    (fun z : Γ(Y.left, (Y.hom ≫ q) ⁻¹ᵁ V) =>
      (((functionsPushforwardIso q Y).hom).val.app (op V)).hom z)
    (fun z : Γ(X.left, (X.hom ≫ q) ⁻¹ᵁ V) =>
      (((functionsPushforwardIso q X).hom).val.app (op V)).hom z)
    (fun z => (relativeFunctionsMap_app S ((Over.map q).map f) V z).trans
      ((relativeFunctionsMap_app T f (q ⁻¹ᵁ V) z).symm.trans
        (pushforward_map_value q (relativeFunctionsMap T f) V z).symm))
    (functionsPushforwardIso_value q Y V) (functionsPushforwardIso_value q X V) r

/-- Iterated pushforward commutes with multiplication by a global coefficient. -/
theorem functionsPushforwardIso_smul {S T : Scheme.{u}} (q : T ⟶ S)
    (X : Over T) (r : Γ(X.left, ⊤)) :
    relativeFunctionsSmul S (Over.mk (X.hom ≫ q)) r ≫
        (functionsPushforwardIso q X).hom =
      (functionsPushforwardIso q X).hom ≫
        (Scheme.Modules.pushforward q).map (relativeFunctionsSmul T X r) :=
  (Scheme.Modules.pushforwardComp X.hom q).inv.naturality
    (Scheme.Modules.globalSectionsSmul (SheafOfModules.unit X.left.ringCatSheaf) r)

/-- A commuting square induces the scalar morphism on relative functions. -/
def functionsScalarMap {S T : Scheme.{u}} (q : T ⟶ S)
    (X : Over T) (Y : Over S) (k : X.left ⟶ Y.left)
    (hk : k ≫ Y.hom = X.hom ≫ q) :
    relativeFunctionsObj S Y ⟶ (Scheme.Modules.pushforward q).obj (relativeFunctionsObj T X) :=
  relativeFunctionsMap S (Over.homMk k hk) ≫ (functionsPushforwardIso q X).hom

/-- The scalar function morphism is the pushforward unit followed by the
specified composition and equality comparisons of structure maps. -/
theorem functionsScalarMap_expansion {P X S T : Scheme.{u}}
    (q : T ⟶ S) (a : P ⟶ T) (b : X ⟶ S) (k : P ⟶ X)
    (h : k ≫ b = a ≫ q) :
    functionsScalarMap q (Over.mk a) (Over.mk b) k h =
      (Scheme.Modules.pushforward b).map
          (SheafOfModules.unitToPushforwardObjUnit k.toRingCatSheafHom) ≫
        (Scheme.Modules.pushforwardComp k b).hom.app
          (SheafOfModules.unit P.ringCatSheaf) ≫
        (Scheme.Modules.pushforwardCongr h).hom.app
          (SheafOfModules.unit P.ringCatSheaf) ≫
        (Scheme.Modules.pushforwardComp a q).inv.app
          (SheafOfModules.unit P.ringCatSheaf) :=
  assoc_four
    ((Scheme.Modules.pushforward b).map
      (SheafOfModules.unitToPushforwardObjUnit k.toRingCatSheafHom))
    ((Scheme.Modules.pushforwardComp k b).hom.app (SheafOfModules.unit P.ringCatSheaf))
    ((Scheme.Modules.pushforwardCongr h).hom.app (SheafOfModules.unit P.ringCatSheaf))
    ((Scheme.Modules.pushforwardComp a q).inv.app (SheafOfModules.unit P.ringCatSheaf))

private theorem contravariant_square {C D : Type*} [Category C] [Category D]
    (F : Cᵒᵖ ⥤ D) {X₁ X₂ Y₁ Y₂ : C}
    (a : X₁ ⟶ Y₁) (b : X₂ ⟶ Y₂) (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂)
    (h : a ≫ g = f ≫ b) :
    F.map g.op ≫ F.map a.op = F.map b.op ≫ F.map f.op := by
  rw [← F.map_comp, ← F.map_comp]
  exact congrArg F.map (congrArg Quiver.Hom.op h)

private theorem relativeFunctions_square (S : Scheme.{u})
    {A₁ A₂ B₁ B₂ : Over S}
    (a : A₁ ⟶ B₁) (b : A₂ ⟶ B₂) (f : A₁ ⟶ A₂) (g : B₁ ⟶ B₂)
    (h : a ≫ g = f ≫ b) :
    relativeFunctionsMap S g ≫ relativeFunctionsMap S a =
      relativeFunctionsMap S b ≫ relativeFunctionsMap S f :=
  contravariant_square (relativeFunctions S) a b f g h

/-- Scalar morphisms on relative functions respect a commuting diagram of nodes. -/
theorem functionsScalarMap_natural {S T : Scheme.{u}} (q : T ⟶ S)
    {X₁ X₂ : Over T} {Y₁ Y₂ : Over S} (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂)
    (k₁ : X₁.left ⟶ Y₁.left) (k₂ : X₂.left ⟶ Y₂.left)
    (h₁ : k₁ ≫ Y₁.hom = X₁.hom ≫ q) (h₂ : k₂ ≫ Y₂.hom = X₂.hom ≫ q)
    (hk : f.left ≫ k₂ = k₁ ≫ g.left) :
    relativeFunctionsMap S g ≫ functionsScalarMap q X₁ Y₁ k₁ h₁ =
      functionsScalarMap q X₂ Y₂ k₂ h₂ ≫
        (Scheme.Modules.pushforward q).map (relativeFunctionsMap T f) := by
  have hsq : (Over.homMk k₁ h₁) ≫ g =
      (Over.map q).map f ≫ (Over.homMk k₂ h₂) :=
    Over.OverMorphism.ext hk.symm
  have hmap :
      relativeFunctionsMap S g ≫ relativeFunctionsMap S (Over.homMk k₁ h₁) =
        relativeFunctionsMap S (Over.homMk k₂ h₂) ≫
          relativeFunctionsMap S ((Over.map q).map f) :=
    relativeFunctions_square S
      (A₁ := (Over.map q).obj X₁) (A₂ := (Over.map q).obj X₂)
      (B₁ := Y₁) (B₂ := Y₂)
      (Over.homMk k₁ h₁) (Over.homMk k₂ h₂) ((Over.map q).map f) g hsq
  exact composed_square (C := S.Modules)
    (A₁ := relativeFunctionsObj S Y₁) (A₂ := relativeFunctionsObj S Y₂)
    (B₁ := relativeFunctionsObj S ((Over.map q).obj X₁))
    (B₂ := relativeFunctionsObj S ((Over.map q).obj X₂))
    (D₁ := (Scheme.Modules.pushforward q).obj (relativeFunctionsObj T X₁))
    (D₂ := (Scheme.Modules.pushforward q).obj (relativeFunctionsObj T X₂))
    (relativeFunctionsMap S g)
    (relativeFunctionsMap S (Over.homMk k₁ h₁))
    (relativeFunctionsMap S (Over.homMk k₂ h₂))
    (relativeFunctionsMap S ((Over.map q).map f))
    (functionsPushforwardIso q X₁).hom (functionsPushforwardIso q X₂).hom
    ((Scheme.Modules.pushforward q).map (relativeFunctionsMap T f))
    (functionsScalarMap q X₁ Y₁ k₁ h₁) (functionsScalarMap q X₂ Y₂ k₂ h₂)
    hmap (functionsPushforwardIso_map q f) rfl rfl

/-- Scalar morphisms on relative functions carry coefficient multiplication to
multiplication by the pulled-back coefficient. -/
theorem functionsScalarMap_smul {S T : Scheme.{u}} (q : T ⟶ S)
    (X : Over T) (Y : Over S) (k : X.left ⟶ Y.left)
    (hk : k ≫ Y.hom = X.hom ≫ q) (r : Γ(Y.left, ⊤)) :
    relativeFunctionsSmul S Y r ≫ functionsScalarMap q X Y k hk =
      functionsScalarMap q X Y k hk ≫
        (Scheme.Modules.pushforward q).map (relativeFunctionsSmul T X (k.appTop r)) := by
  let f : Over.mk (X.hom ≫ q) ⟶ Y := Over.homMk k hk
  calc
    relativeFunctionsSmul S Y r ≫ functionsScalarMap q X Y k hk =
        (relativeFunctionsSmul S Y r ≫ relativeFunctionsMap S f) ≫
          (functionsPushforwardIso q X).hom := (Category.assoc _ _ _).symm
    _ = (relativeFunctionsMap S f ≫
        relativeFunctionsSmul S (Over.mk (X.hom ≫ q)) (k.appTop r)) ≫
          (functionsPushforwardIso q X).hom :=
      congrArg (fun z => z ≫ (functionsPushforwardIso q X).hom)
        (relativeFunctionsMap_smul S f r)
    _ = relativeFunctionsMap S f ≫
        (relativeFunctionsSmul S (Over.mk (X.hom ≫ q)) (k.appTop r) ≫
          (functionsPushforwardIso q X).hom) := Category.assoc _ _ _
    _ = relativeFunctionsMap S f ≫ ((functionsPushforwardIso q X).hom ≫
        (Scheme.Modules.pushforward q).map (relativeFunctionsSmul T X (k.appTop r))) :=
      congrArg (fun z => relativeFunctionsMap S f ≫ z)
        (functionsPushforwardIso_smul q X (k.appTop r))
    _ = functionsScalarMap q X Y k hk ≫
        (Scheme.Modules.pushforward q).map (relativeFunctionsSmul T X (k.appTop r)) :=
      (Category.assoc _ _ _).symm

private theorem unit_map_composite {S T : Scheme.{u}} (q : T ⟶ S) (X : Over T) :
    SheafOfModules.unitToPushforwardObjUnit (X.hom ≫ q).toRingCatSheafHom ≫
        (functionsPushforwardIso q X).hom =
      SheafOfModules.unitToPushforwardObjUnit q.toRingCatSheafHom ≫
        (Scheme.Modules.pushforward q).map
          (SheafOfModules.unitToPushforwardObjUnit X.hom.toRingCatSheafHom) := by
  apply Scheme.Modules.hom_ext
  intro V
  apply ConcreteCategory.hom_ext
  intro r
  change (((functionsPushforwardIso q X).hom).val.app (op V)).hom
      ((X.hom ≫ q).app V r) = X.hom.app (q ⁻¹ᵁ V) (q.app V r)
  exact (functionsPushforwardIso_value q X V ((X.hom ≫ q).app V r)).trans rfl

/-- Scalar morphisms carry coefficient sections to their pushforward scalar
sections, through the canonical map of structure sheaves. -/
theorem functionsScalarMap_coefficient {S T : Scheme.{u}} (q : T ⟶ S)
    (X : Over T) (Y : Over S) (k : X.left ⟶ Y.left)
    (hk : k ≫ Y.hom = X.hom ≫ q) (r : Γ(Y.left, ⊤)) :
    relativeCoefficient S Y r ≫ functionsScalarMap q X Y k hk =
      SheafOfModules.unitToPushforwardObjUnit q.toRingCatSheafHom ≫
        (Scheme.Modules.pushforward q).map (relativeCoefficient T X (k.appTop r)) := by
  let f : Over.mk (X.hom ≫ q) ⟶ Y := Over.homMk k hk
  calc
    relativeCoefficient S Y r ≫ functionsScalarMap q X Y k hk =
        (relativeCoefficient S Y r ≫ relativeFunctionsMap S f) ≫
          (functionsPushforwardIso q X).hom := (Category.assoc _ _ _).symm
    _ = relativeCoefficient S (Over.mk (X.hom ≫ q)) (k.appTop r) ≫
        (functionsPushforwardIso q X).hom :=
      congrArg (fun z => z ≫ (functionsPushforwardIso q X).hom)
        (relativeCoefficient_pullback S f r)
    _ = (SheafOfModules.unitToPushforwardObjUnit (X.hom ≫ q).toRingCatSheafHom ≫
        (functionsPushforwardIso q X).hom) ≫
          (Scheme.Modules.pushforward q).map
            (relativeFunctionsSmul T X (k.appTop r)) := by
      change (_ ≫ relativeFunctionsSmul S (Over.mk (X.hom ≫ q)) (k.appTop r)) ≫ _ = _
      exact (Category.assoc _ _ _).trans
        ((congrArg (fun z =>
          SheafOfModules.unitToPushforwardObjUnit (X.hom ≫ q).toRingCatSheafHom ≫ z)
          (functionsPushforwardIso_smul q X (k.appTop r))).trans
            (Category.assoc _ _ _).symm)
    _ = SheafOfModules.unitToPushforwardObjUnit q.toRingCatSheafHom ≫
        (Scheme.Modules.pushforward q).map (relativeCoefficient T X (k.appTop r)) :=
      (congrArg (fun z : SheafOfModules.unit S.ringCatSheaf ⟶
          (Scheme.Modules.pushforward q).obj (relativeFunctionsObj T X) =>
        z ≫ (Scheme.Modules.pushforward q).map
          (relativeFunctionsSmul T X (k.appTop r))) (unit_map_composite q X)).trans
        (map_comp_right (Scheme.Modules.pushforward q)
          (SheafOfModules.unitToPushforwardObjUnit q.toRingCatSheafHom)
          (SheafOfModules.unitToPushforwardObjUnit X.hom.toRingCatSheafHom)
          (relativeFunctionsSmul T X (k.appTop r)))

end FrobeniusSplitting.CharacterLine
