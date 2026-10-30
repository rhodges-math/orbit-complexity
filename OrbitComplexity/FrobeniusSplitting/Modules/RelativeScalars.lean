import OrbitComplexity.FrobeniusSplitting.Modules.RelativeFunctions
import TauCeti.AlgebraicGeometry.Modules.GlobalSections

/-! # Multiplication on relative regular functions -/

open AlgebraicGeometry CategoryTheory Opposite

noncomputable section
universe u

namespace FrobeniusSplitting.CharacterLine

variable (S : Scheme.{u})

/-- A global function multiplies the functions on each original inverse-image open. -/
def relativeFunctionsSmul (X : Over S) (r : Γ(X.left, ⊤)) :
    FrobeniusSplitting.CharacterLine.relativeFunctionsObj S X ⟶
        FrobeniusSplitting.CharacterLine.relativeFunctionsObj S X :=
  (Scheme.Modules.pushforward X.hom).map
    (Scheme.Modules.globalSectionsSmul (SheafOfModules.unit X.left.ringCatSheaf) r)

/-- Relative multiplication is multiplication by the restriction on every open. -/
theorem relativeFunctionsSmul_app (X : Over S) (r : Γ(X.left, ⊤)) (V : S.Opens)
    (s : Γ(X.left, X.hom ⁻¹ᵁ V)) :
    ((FrobeniusSplitting.CharacterLine.relativeFunctionsSmul S X r).val.app (.op V)).hom s =
      X.left.presheaf.map (X.hom ⁻¹ᵁ V).leTop.op r * s := by
  rfl

private theorem appLE_global {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : Y.Opens) (V : X.Opens) (e : V ≤ f ⁻¹ᵁ U) (r : Γ(Y, ⊤)) :
    f.appLE U V e (Y.presheaf.map U.leTop.op r) =
      X.presheaf.map V.leTop.op (f.appTop r) := by
  have ht : (⊤ : X.Opens) ≤ f ⁻¹ᵁ (⊤ : Y.Opens) := by
    rw [Scheme.Hom.preimage_top]
  have htop : f.appLE ⊤ ⊤ ht = f.appTop := by
    unfold Scheme.Hom.appLE
    have hi : (homOfLE ht).op = 𝟙 (op (⊤ : X.Opens)) := Subsingleton.elim _ _
    rw [hi]
    exact (congrArg (fun k => f.appTop ≫ k)
      (CategoryTheory.Functor.map_id X.presheaf (op (⊤ : X.Opens)))).trans
        (Category.comp_id f.appTop)
  have h : Y.presheaf.map U.leTop.op ≫ f.appLE U V e =
      f.appTop ≫ X.presheaf.map V.leTop.op := by
    calc
      _ = f.appLE ⊤ V _ := f.map_appLE e U.leTop.op
      _ = f.appLE ⊤ ⊤ ht ≫ X.presheaf.map V.leTop.op :=
        (f.appLE_map ht V.leTop.op).symm
      _ = _ := congrArg (fun k => k ≫ X.presheaf.map V.leTop.op) htop
  exact ConcreteCategory.congr_hom h r

/-- Pullback of relative functions respects multiplication by the same pulled-back function. -/
theorem relativeFunctionsMap_smul {X Y : Over S} (f : X ⟶ Y) (r : Γ(Y.left, ⊤)) :
    FrobeniusSplitting.CharacterLine.relativeFunctionsSmul S Y r ≫
        FrobeniusSplitting.CharacterLine.relativeFunctionsMap S f =
      FrobeniusSplitting.CharacterLine.relativeFunctionsMap S f ≫
          FrobeniusSplitting.CharacterLine.relativeFunctionsSmul S X (f.left.appTop r) := by
  ext V s
  change Γ(Y.left, Y.hom ⁻¹ᵁ V) at s
  have e : X.hom ⁻¹ᵁ V ≤ f.left ⁻¹ᵁ (Y.hom ⁻¹ᵁ V) := by
    change X.hom ⁻¹ᵁ V ≤ (f.left ≫ Y.hom) ⁻¹ᵁ V
    rw [f.w]
  let phi : Γ(Y.left, Y.hom ⁻¹ᵁ V) →+* Γ(X.left, X.hom ⁻¹ᵁ V) :=
    (f.left.appLE (Y.hom ⁻¹ᵁ V) (X.hom ⁻¹ᵁ V) e).hom
  let rY : Γ(Y.left, Y.hom ⁻¹ᵁ V) := Y.left.presheaf.map (Y.hom ⁻¹ᵁ V).leTop.op r
  let rX : Γ(X.left, X.hom ⁻¹ᵁ V) :=
    X.left.presheaf.map (X.hom ⁻¹ᵁ V).leTop.op (f.left.appTop r)
  change phi (rY * s) = rX * phi s
  calc
    phi (rY * s) = phi rY * phi s := map_mul phi rY s
    _ = rX * phi s := congrArg (fun a => a * phi s)
      (FrobeniusSplitting.CharacterLine.appLE_global f.left (Y.hom ⁻¹ᵁ V) (X.hom ⁻¹ᵁ V) e r)

/-- Multiplication by one is the identity on the relative function sheaf. -/
theorem relativeFunctionsSmul_one (X : Over S) :
    FrobeniusSplitting.CharacterLine.relativeFunctionsSmul S X 1 = 𝟙
        (FrobeniusSplitting.CharacterLine.relativeFunctionsObj S X) := by
  exact (congrArg (fun k => (Scheme.Modules.pushforward X.hom).map k)
    (Scheme.Modules.globalSectionsSmul_one (SheafOfModules.unit X.left.ringCatSheaf))).trans
      (CategoryTheory.Functor.map_id (Scheme.Modules.pushforward X.hom) _)

/-- Successive relative scalar maps multiply their original global functions. -/
theorem relativeFunctionsSmul_mul (X : Over S) (r s : Γ(X.left, ⊤)) :
    FrobeniusSplitting.CharacterLine.relativeFunctionsSmul S X (r * s) =
      FrobeniusSplitting.CharacterLine.relativeFunctionsSmul S X s ≫
          FrobeniusSplitting.CharacterLine.relativeFunctionsSmul S X r := by
  exact (congrArg (fun k => (Scheme.Modules.pushforward X.hom).map k)
    (Scheme.Modules.globalSectionsSmul_mul (SheafOfModules.unit X.left.ringCatSheaf) r s)).trans
      (CategoryTheory.Functor.map_comp (Scheme.Modules.pushforward X.hom) _ _)

end FrobeniusSplitting.CharacterLine
