import OrbitComplexity.GroupActions.Rosenlicht.FunctionFields
import TauCeti.AlgebraicGeometry.Scheme.BaseAlgebra

/-!
# Function-field pullback over a base ring

Pullback along a dominant morphism over an affine base preserves the base-ring scalars.
Thus it is an algebra homomorphism on function fields, and an algebra isomorphism for
dominant open immersions.

## Main definitions

* `functionFieldAlgHom`: pullback on function fields as an algebra homomorphism.
* `openFunctionFieldAlgEquiv`: the algebra isomorphism of a dominant open immersion.

## Main results

* `functionFieldMap_algebraMap`: pullback commutes with the base-ring maps.
-/

namespace GroupActions

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

variable (K : Type u) [CommRing K]
variable {X Y : Scheme.{u}} [X.Over (Spec (.of K))] [Y.Over (Spec (.of K))]

private lemma baseGlobal_natural (f : X ⟶ Y) [f.IsOver (Spec (.of K))] (c : K) :
    f.appTop (Scheme.Modules.baseRingToGlobalSections K Y c) =
      Scheme.Modules.baseRingToGlobalSections K X c := by
  simp only [Scheme.Modules.baseRingToGlobalSections_apply, ← CommRingCat.comp_apply,
    ← Scheme.Hom.comp_appTop, CategoryTheory.comp_over]

private lemma baseStalk_natural (f : X ⟶ Y) [f.IsOver (Spec (.of K))] (x : X) (c : K) :
    f.stalkMap x (Scheme.baseRingToStalk K Y (f x) c) =
      Scheme.baseRingToStalk K X x c := by
  have h := congrArg (fun h : Γ(Y, ⊤) ⟶ X.presheaf.stalk x ↦
    h (Scheme.Modules.baseRingToGlobalSections K Y c))
      (f.germ_stalkMap (⊤ : Y.Opens) x (show f x ∈ ⊤ from trivial))
  exact h.trans (congrArg (fun a ↦ X.presheaf.germ ⊤ x trivial a)
    (baseGlobal_natural K f c))

private lemma stalkCongr_base (x y : Y) (hxy : x = y) (c : K) :
    (Y.presheaf.stalkCongr (.of_eq hxy)).hom (Scheme.baseRingToStalk K Y x c) =
      Scheme.baseRingToStalk K Y y c := by
  subst y
  change Y.presheaf.stalkSpecializes (specializes_refl x)
    (Scheme.baseRingToStalk K Y x c) = _
  rw [TopCat.Presheaf.stalkSpecializes_refl]
  rfl

variable [IsIntegral X] [IsIntegral Y]

/-- Pullback along a dominant morphism over an affine base commutes with base-ring scalars. -/
theorem functionFieldMap_algebraMap (f : X ⟶ Y) [IsDominant f]
    [f.IsOver (Spec (.of K))] (c : K) :
    functionFieldMap f (algebraMap K Y.functionField c) =
      algebraMap K X.functionField c := by
  change f.stalkMap (genericPoint X)
    ((Y.presheaf.stalkCongr (.of_eq (map_genericPoint f).symm)).hom
      (Scheme.baseRingToStalk K Y (genericPoint Y) c)) =
    Scheme.baseRingToStalk K X (genericPoint X) c
  exact (congrArg (f.stalkMap (genericPoint X))
    (stalkCongr_base K (genericPoint Y) (f (genericPoint X))
      (map_genericPoint f).symm c)).trans (baseStalk_natural K f (genericPoint X) c)

/-- Pullback along a dominant morphism over an affine base, as an algebra homomorphism. -/
def functionFieldAlgHom (f : X ⟶ Y) [IsDominant f] [f.IsOver (Spec (.of K))] :
    Y.functionField →ₐ[K] X.functionField where
  __ := functionFieldMap f
  commutes' := functionFieldMap_algebraMap K f

/-- A dominant open immersion over an affine base induces an algebra isomorphism
of function fields. -/
def openFunctionFieldAlgEquiv (f : X ⟶ Y) [IsDominant f] [IsOpenImmersion f]
    [f.IsOver (Spec (.of K))] : Y.functionField ≃ₐ[K] X.functionField where
  __ := openFunctionFieldEquiv f
  commutes' := functionFieldMap_algebraMap K f

end

end GroupActions
