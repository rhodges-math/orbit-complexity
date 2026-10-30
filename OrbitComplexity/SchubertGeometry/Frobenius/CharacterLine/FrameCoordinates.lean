import OrbitComplexity.FrobeniusSplitting.Modules.MatchingModule
import OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.OverlapSquares
import OrbitComplexity.FrobeniusSplitting.Modules.RestrictionLimits
import OrbitComplexity.FrobeniusSplitting.Modules.FunctionsBaseChange
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-! # Inverse-character frame coordinates on the original retained charts -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
noncomputable section
universe u
namespace SchubertGeometry.RetainedCharacter

private def frameSingleton {J : Type u} (j : J) : {s : Finset J // s.Nonempty} :=
  ⟨{j}, Finset.singleton_nonempty j⟩

variable {R J : Type u} [CommRing R]
    (N : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} R)
    [hmapOpen : ∀ {s t} (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (N.map f).hom.toRingHom))]
    [hdirected : ((N.op ⋙ algSpec (.of R) ⋙ Over.forget (Spec (.of R))) ⋙
      Scheme.forget).IsLocallyDirected]
    (cG : Cocone (N.op ⋙ algSpec (.of R))) (hcG : IsColimit cG)
    (delta₀ : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val)
      (k : J) (_ : k ∈ s.val), (N.obj s)ˣ) (n : ℕ)

private def frameFunctions (k : J) : cG.pt.left.Modules :=
  FrobeniusSplitting.CharacterLine.relativeFunctionsObj cG.pt.left
    (FrobeniusSplitting.RetainedCharacter.node N cG (frameSingleton k))

/-- The inverse-character unit in the original overlap section ring.
The exponent is arbitrary and does not change the coefficient ring or diagram. -/
def inverseFrameUnit (s : {s : Finset J // s.Nonempty}) (j : J) (hj : j ∈ s.val)
    (k : J) : Γ(Spec (.of (N.obj (unionIndex s (frameSingleton k)))), ⊤)ˣ :=
  Units.map (Scheme.ΓSpecIso (.of (N.obj (unionIndex s (frameSingleton k))))).inv.hom.toMonoidHom
    ((delta₀ (unionIndex s (frameSingleton k))
      j ((leOfHom (unionLeft s (frameSingleton k))) hj)
      k ((leOfHom (unionRight s (frameSingleton k))) (Finset.mem_singleton_self k)))⁻¹ ^ n)

/-- On a specified original chart, the kth coordinate of its candidate unit
frame is the overlap unit delta_jk^(-n), transported by the Cartesian
regular-function comparison. No line triviality is used as an input. -/
def inverseFrameCoordinate (s : {s : Finset J // s.Nonempty}) (j : J) (hj : j ∈ s.val)
    (k : J) :
    SheafOfModules.unit (Spec (.of (N.obj s))).ringCatSheaf ⟶
      (Scheme.Modules.pullback (cG.ι.app (.op s)).left).obj (frameFunctions N cG k) := by
  let w := unionIndex s (frameSingleton k)
  let p := Spec.map (CommRingCat.ofHom (N.map (unionLeft s (frameSingleton k))).hom.toRingHom)
  let r := Spec.map (CommRingCat.ofHom (N.map (unionRight s (frameSingleton k))).hom.toRingHom)
  let a := (cG.ι.app (.op s)).left
  let b := (cG.ι.app (.op (frameSingleton k))).left
  let ha : IsOpenImmersion a := (retained_prior_charts N cG hcG).1 s
  let hr : IsOpenImmersion r := hmapOpen (unionRight s (frameSingleton k))
  let H : IsPullback p r a b := retained_overlap_square N cG hcG s (frameSingleton k)
  let e := @FrobeniusSplitting.CharacterLine.openFunctionsBaseChange _ _ _ _ p r a b ha hr H
  let q : Over (Spec (.of (N.obj s))) := Over.mk p
  let f : SheafOfModules.unit (Spec (.of (N.obj s))).ringCatSheaf ⟶
      FrobeniusSplitting.CharacterLine.relativeFunctionsObj (Spec (.of (N.obj s))) q :=
    SheafOfModules.unitToPushforwardObjUnit p.toRingCatSheafHom
  exact f ≫ FrobeniusSplitting.CharacterLine.relativeFunctionsSmul (Spec (.of (N.obj s))) q
      (inverseFrameUnit N delta₀ n s j hj k : Γ(Spec (.of (N.obj w)), ⊤)) ≫
    e.inv ≫ (@Scheme.Modules.restrictFunctorIsoPullback _ _ a ha).hom.app
      (frameFunctions N cG k)

include hmapOpen hdirected hcG in
private theorem framePullbackPreserved (s : {s : Finset J // s.Nonempty}) :
    PreservesLimit (Discrete.functor (frameFunctions N cG))
      (Scheme.Modules.pullback (cG.ι.app (.op s)).left) := by
  let a := (cG.ι.app (.op s)).left
  let ha : IsOpenImmersion a := (retained_prior_charts N cG hcG).1 s
  let F := @Scheme.Modules.restrictFunctor _ _ a ha
  let hSize : PreservesLimitsOfSize.{u, u} F :=
    @FrobeniusSplitting.RetainedCharacter.restrictPreservesLimits _ _ a ha
  let hShape : PreservesLimitsOfShape (Discrete J) F :=
    hSize.preservesLimitsOfShape (J := Discrete J)
  let : PreservesLimit (Discrete.functor (frameFunctions N cG)) F := hShape.preservesLimit
  exact preservesLimit_of_natIso (Discrete.functor (frameFunctions N cG))
    (@Scheme.Modules.restrictFunctorIsoPullback _ _ a ha)

/-- These are the coordinate morphisms into the restricted product used
by the matching equalizer; every component uses the same original chart leg. -/
def inverseFrameProduct (s : {s : Finset J // s.Nonempty}) (j : J) (hj : j ∈ s.val) :
    SheafOfModules.unit (Spec (.of (N.obj s))).ringCatSheaf ⟶
      (Scheme.Modules.pullback (cG.ι.app (.op s)).left).obj (∏ᶜ frameFunctions N cG) := by
  let a := (cG.ι.app (.op s)).left
  let F := Scheme.Modules.pullback a
  let hProduct : PreservesLimit (Discrete.functor (frameFunctions N cG)) F :=
    framePullbackPreserved N cG hcG s
  let e := @PreservesProduct.iso _ _ _ _ F J (frameFunctions N cG)
    inferInstance inferInstance hProduct
  exact Pi.lift (inverseFrameCoordinate N cG hcG delta₀ n s j hj) ≫ e.inv

/-- Projection recovers the original inverse-character overlap coordinate. -/
theorem inverseFrameProduct_coordinate (s : {s : Finset J // s.Nonempty})
    (j : J) (hj : j ∈ s.val) (k : J) :
    inverseFrameProduct N cG hcG delta₀ n s j hj ≫
        (Scheme.Modules.pullback (cG.ι.app (.op s)).left).map
          (Pi.π (frameFunctions N cG) k) =
      inverseFrameCoordinate N cG hcG delta₀ n s j hj k := by
  let a := (cG.ι.app (.op s)).left
  let F := Scheme.Modules.pullback a
  let hProduct : PreservesLimit (Discrete.functor (frameFunctions N cG)) F :=
    framePullbackPreserved N cG hcG s
  let e := @PreservesProduct.iso _ _ _ _ F J (frameFunctions N cG)
    inferInstance inferInstance hProduct
  let f := inverseFrameCoordinate N cG hcG delta₀ n s j hj
  have he : e.inv ≫ F.map (Pi.π (frameFunctions N cG) k) =
      Pi.π (fun x ↦ F.obj (frameFunctions N cG x)) k := by
    apply (cancel_epi e.hom).mp
    exact (Iso.hom_inv_id_assoc e _).trans
      (piComparison_comp_π F (frameFunctions N cG) k).symm
  change (Pi.lift f ≫ e.inv) ≫ F.map (Pi.π (frameFunctions N cG) k) = f k
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun z ↦ Pi.lift f ≫ z) he).trans (Pi.lift_comp_π f k))

end SchubertGeometry.RetainedCharacter
