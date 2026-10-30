import OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.FrameCoordinates
import OrbitComplexity.FrobeniusSplitting.Modules.OpenFunctions
import OrbitComplexity.FrobeniusSplitting.Modules.OpenFunctionMaps
import Batteries.Tactic.Lint

/-! # Regular functions on retained local frames -/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
noncomputable section
universe u
namespace SchubertGeometry.RetainedCharacter.BaseCoordinates

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "BaseCoordinates: unit"
    (← IO.getStderr).flush

/-- The structure-sheaf map as a relative-function morphism. -/
def unit (S : Scheme.{u}) (X : Over S) :
    SheafOfModules.unit S.ringCatSheaf ⟶
      FrobeniusSplitting.CharacterLine.relativeFunctionsObj S X :=
  SheafOfModules.unitToPushforwardObjUnit X.hom.toRingCatSheafHom

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "BaseCoordinates: appLE_comp_over"
    (← IO.getStderr).flush

private theorem appLE_comp_over {X Y S : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ S) (h : X ⟶ S) (hw : f ≫ g = h) (U : S.Opens) :
    g.app U ≫ f.appLE (g ⁻¹ᵁ U) (h ⁻¹ᵁ U) (by rw [← Scheme.Hom.comp_preimage, hw]) =
      h.app U := by
  subst h
  have hc := Scheme.Hom.comp_appLE f g U ((f ≫ g) ⁻¹ᵁ U) le_rfl
  exact hc.symm.trans (Scheme.Hom.appLE_eq_app (f ≫ g))

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "BaseCoordinates: unit_natural"
    (← IO.getStderr).flush

/-- Structure-sheaf pullback is natural for maps over the base. -/
theorem unit_natural {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y) :
    unit S Y ≫ FrobeniusSplitting.CharacterLine.relativeFunctionsMap S f = unit S X := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  let U : S.Opens := V.unop
  change Γ(S, U) at a
  have hpre : X.hom ⁻¹ᵁ U ≤ f.left ⁻¹ᵁ (Y.hom ⁻¹ᵁ U) := by
    rw [← Scheme.Hom.comp_preimage, f.w]
  change (f.left.appLE (Y.hom ⁻¹ᵁ U) (X.hom ⁻¹ᵁ U) hpre) ((Y.hom.app U) a) =
    (X.hom.app U) a
  have h : Y.hom.app U ≫ f.left.appLE (Y.hom ⁻¹ᵁ U) (X.hom ⁻¹ᵁ U) hpre = X.hom.app U :=
    appLE_comp_over f.left Y.hom X.hom f.w U
  exact congrArg (fun g : Γ(S, U) ⟶ Γ(X.left, X.hom ⁻¹ᵁ U) ↦ g a) h

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "BaseCoordinates: weighted"
    (← IO.getStderr).flush

/-- Cartesian base change transports a weighted regular-function coordinate. -/
def weighted {U Y P X : Scheme.{u}}
    (j : U ⟶ Y) [hj : IsOpenImmersion j] (p : P ⟶ U) (q : X ⟶ Y) (k : P ⟶ X)
    [hk : IsOpenImmersion k] (H : IsPullback p k j q) (r : Γ(P, ⊤)) :
    SheafOfModules.unit U.ringCatSheaf ⟶
      (@Scheme.Modules.restrictFunctor _ _ j hj).obj
        (FrobeniusSplitting.CharacterLine.relativeFunctionsObj Y (Over.mk q)) :=
  unit U (Over.mk p) ≫ FrobeniusSplitting.CharacterLine.relativeFunctionsSmul U (Over.mk p) r ≫
    (@FrobeniusSplitting.CharacterLine.openFunctionsBaseChange _ _ _ _ p k j q hj hk H).inv

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "BaseCoordinates: baseChange_smul"
    (← IO.getStderr).flush

/-- The Cartesian regular-function comparison respects scalar multiplication. -/
theorem baseChange_smul {U Y P X : Scheme.{u}}
    (j : U ⟶ Y) [hj : IsOpenImmersion j] (p : P ⟶ U) (q : X ⟶ Y) (k : P ⟶ X)
    [hk : IsOpenImmersion k] (H : IsPullback p k j q) (r : Γ(X, ⊤)) :
    (@Scheme.Modules.restrictFunctor _ _ j hj).map
        (FrobeniusSplitting.CharacterLine.relativeFunctionsSmul Y (Over.mk q) r) ≫
        (@FrobeniusSplitting.CharacterLine.openFunctionsBaseChange _ _ _ _ p k j q hj hk H).hom =
      (@FrobeniusSplitting.CharacterLine.openFunctionsBaseChange _ _ _ _ p k j q hj hk H).hom ≫
        FrobeniusSplitting.CharacterLine.relativeFunctionsSmul U (Over.mk p) (k.appTop r) := by
  let m := (@Scheme.Modules.restrictFunctor _ _ j hj).map
    (FrobeniusSplitting.CharacterLine.relativeFunctionsSmul Y (Over.mk q) r)
  let b := FrobeniusSplitting.CharacterLine.relativeFunctionsSmul U (Over.mk p) (k.appTop r)
  let e := @FrobeniusSplitting.CharacterLine.openFunctionsBaseChange _ _ _ _ p k j q hj hk H
  let a := @FrobeniusSplitting.CharacterLine.openFunctionsPullback _ _ _ _ p k j q hj H.w
  have he : e.hom = a := @FrobeniusSplitting.CharacterLine.openFunctionsBaseChange_hom _ _ _ _
    p k j q hj hk H
  have hn : m ≫ a = a ≫ b :=
    @FrobeniusSplitting.CharacterLine.openFunctionsPullback_smul _ _ _ _ p k j q hj H.w r
  exact (congrArg (fun z ↦ m ≫ z) he).trans
    (hn.trans (congrArg (fun z ↦ z ≫ b) he.symm))

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "BaseCoordinates: weighted_map"
    (← IO.getStderr).flush

/-- Cartesian base change carries weighted coordinates to their pullbacks. -/
theorem weighted_map {U Y P₁ P₂ X₁ X₂ : Scheme.{u}}
    (j : U ⟶ Y) [hj : IsOpenImmersion j]
    (p₁ : P₁ ⟶ U) (p₂ : P₂ ⟶ U) (q₁ : X₁ ⟶ Y) (q₂ : X₂ ⟶ Y)
    (k₁ : P₁ ⟶ X₁) (k₂ : P₂ ⟶ X₂)
    [hk₁ : IsOpenImmersion k₁] [hk₂ : IsOpenImmersion k₂]
    (H₁ : IsPullback p₁ k₁ j q₁) (H₂ : IsPullback p₂ k₂ j q₂)
    (M : Over.mk q₁ ⟶ Over.mk q₂) (T : Over.mk p₁ ⟶ Over.mk p₂)
    (hk : T.left ≫ k₂ = k₁ ≫ M.left) (r : Γ(P₂, ⊤)) :
    weighted j p₂ q₂ k₂ H₂ r ≫
        (@Scheme.Modules.restrictFunctor _ _ j hj).map
          (FrobeniusSplitting.CharacterLine.relativeFunctionsMap Y M) ≫
          (@FrobeniusSplitting.CharacterLine.openFunctionsBaseChange _ _ _ _
            p₁ k₁ j q₁ hj hk₁ H₁).hom =
      unit U (Over.mk p₁) ≫
        FrobeniusSplitting.CharacterLine.relativeFunctionsSmul U (Over.mk p₁)
          (T.left.appTop r) := by
  let e₁ := @FrobeniusSplitting.CharacterLine.openFunctionsBaseChange _ _ _ _ p₁ k₁ j q₁ hj hk₁ H₁
  let e₂ := @FrobeniusSplitting.CharacterLine.openFunctionsBaseChange _ _ _ _ p₂ k₂ j q₂ hj hk₂ H₂
  let m := (@Scheme.Modules.restrictFunctor _ _ j hj).map
          (FrobeniusSplitting.CharacterLine.relativeFunctionsMap Y M)
  let t := FrobeniusSplitting.CharacterLine.relativeFunctionsMap U T
  let a := unit U (Over.mk p₂)
  let b := FrobeniusSplitting.CharacterLine.relativeFunctionsSmul U (Over.mk p₂) r
  let c := FrobeniusSplitting.CharacterLine.relativeFunctionsSmul U (Over.mk p₁) (T.left.appTop r)
  have h₁ : e₁.hom =
      @FrobeniusSplitting.CharacterLine.openFunctionsPullback _ _ _ _ p₁ k₁ j q₁ hj H₁.w :=
    @FrobeniusSplitting.CharacterLine.openFunctionsBaseChange_hom _ _ _ _ p₁ k₁ j q₁ hj hk₁ H₁
  have h₂ : e₂.hom =
      @FrobeniusSplitting.CharacterLine.openFunctionsPullback _ _ _ _ p₂ k₂ j q₂ hj H₂.w :=
    @FrobeniusSplitting.CharacterLine.openFunctionsBaseChange_hom _ _ _ _ p₂ k₂ j q₂ hj hk₂ H₂
  have hn : m ≫ e₁.hom = e₂.hom ≫ t :=
    (congrArg (fun z ↦ m ≫ z) h₁).trans
      ((@FrobeniusSplitting.CharacterLine.openFunctionsPullback_natural _ _ _ _ _ _ j hj
        p₁ p₂ q₁ q₂ k₁ k₂ H₁.w H₂.w M T hk).trans
        (congrArg (fun z ↦ z ≫ t) h₂.symm))
  have hi : e₂.inv ≫ m ≫ e₁.hom = t :=
    (congrArg (fun z ↦ e₂.inv ≫ z) hn).trans (Iso.inv_hom_id_assoc e₂ t)
  have hb : b ≫ t = t ≫ c := FrobeniusSplitting.CharacterLine.relativeFunctionsMap_smul U T r
  have hu : a ≫ t = unit U (Over.mk p₁) := unit_natural T
  have h₀ : (a ≫ b ≫ e₂.inv) ≫ m ≫ e₁.hom = a ≫ b ≫ t :=
    ((Category.assoc a (b ≫ e₂.inv) (m ≫ e₁.hom)).trans
      (congrArg (fun z ↦ a ≫ z) (Category.assoc b e₂.inv (m ≫ e₁.hom)))).trans
        (congrArg (fun z ↦ a ≫ b ≫ z) hi)
  have h₁' : a ≫ b ≫ t = a ≫ t ≫ c := congrArg (fun z ↦ a ≫ z) hb
  have h₂' : a ≫ t ≫ c = unit U (Over.mk p₁) ≫ c :=
    (Category.assoc a t c).symm.trans (congrArg (fun z ↦ z ≫ c) hu)
  exact h₀.trans (h₁'.trans h₂')

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "BaseCoordinates: coefficient"
    (← IO.getStderr).flush

/-- The inverse transition coefficient on the singleton-union chart. -/
def coefficient {R J : Type u} [CommRing R]
    (N : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} R)
    (delta₀ : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val)
      (k : J) (_ : k ∈ s.val), (N.obj s)ˣ) (n : ℕ)
    (s : {s : Finset J // s.Nonempty}) (j : J) (hj : j ∈ s.val) (k : J) :
    Γ(Spec (.of (N.obj (unionIndex s ⟨{k}, Finset.singleton_nonempty k⟩))), ⊤) :=
  (inverseFrameUnit N delta₀ n s j hj k).val

end SchubertGeometry.RetainedCharacter.BaseCoordinates
