import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits

/-! # Restriction of the character matching equalizer -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
noncomputable section
universe u
namespace FrobeniusSplitting.RetainedCharacter

/-- Restriction along the open chart preserves the products and equalizer
used to construct the character module. Section evaluation reduces this to
restriction of scalars along the chart's structure-sheaf isomorphism. -/
instance restrictPreservesLimits {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] :
    PreservesLimitsOfSize.{u, u} (Scheme.Modules.restrictFunctor j) := by
  constructor
  intro D instD
  constructor
  intro F
  constructor
  intro c hc
  refine ⟨?_⟩
  let hShape : ReflectsLimitsOfShape D (SheafOfModules.forget.{u} X.ringCatSheaf) :=
    (fullyFaithful_reflectsLimits (SheafOfModules.forget.{u} X.ringCatSheaf) :
      ReflectsLimitsOfSize.{u, u} _).reflectsLimitsOfShape (J := D)
  let hReflect : ReflectsLimit (F ⋙ Scheme.Modules.restrictFunctor j)
      (SheafOfModules.forget.{u} X.ringCatSheaf) :=
    hShape.reflectsLimit (K := F ⋙ Scheme.Modules.restrictFunctor j)
  refine (hReflect.reflects (c := (Scheme.Modules.restrictFunctor j).mapCone c) ?_).some
  refine PresheafOfModules.evaluationJointlyReflectsLimits _ _ (fun U ↦ ?_)
  let q : Γ(X, U.unop) →+* Γ(Y, j ''ᵁ U.unop) := (j.appIso U.unop).inv.hom
  change IsLimit ((ModuleCat.restrictScalars q).mapCone
    ((SheafOfModules.evaluation Y.ringCatSheaf (.op (j ''ᵁ U.unop))).mapCone c))
  let E := SheafOfModules.evaluation.{u} Y.ringCatSheaf (.op (j ''ᵁ U.unop))
  let hEval : PreservesLimit F E :=
    SheafOfModules.evaluationPreservesLimit F (.op (j ''ᵁ U.unop))
  let hcEval : IsLimit (E.mapCone c) := (hEval.preserves hc).some
  let hScalars : PreservesLimit (F ⋙ E) (ModuleCat.restrictScalars.{u} q) :=
    ModuleCat.preservesLimit_restrictScalars q (F ⋙ E)
  exact (hScalars.preserves hcEval).some

end FrobeniusSplitting.RetainedCharacter
