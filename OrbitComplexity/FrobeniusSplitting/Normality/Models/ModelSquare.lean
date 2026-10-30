import OrbitComplexity.FrobeniusSplitting.Normality.Limits.ModelMorphismDescent
import Batteries.Tactic.Lint

/-! # Scalar pullback squares

The cone legs preserve the original scheme and finite-stage coefficient projections.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace FrobeniusSplitting

noncomputable section

universe u

/-- The canonical cone leg is the scalar pullback at every finite
coefficient stage. No flatness or geometric property of the model is required. -/
theorem modelScalarCartesian {K : Type u} [CommRing K]
    (S : Subalgebra ℤ K) {X : Scheme.{u}} (a : X ⟶ Spec (.of S))
    (i : CoefficientStage S) :
    IsPullback ((modelScalarCone S a).π.app (op i))
      (genericScalarModel S a).hom (stageScalarModel S a i).hom
      (Spec.map (CommRingCat.ofHom (algebraMap i.val K))) := by
  let κ := Spec.map (CommRingCat.ofHom (algebraMap S K))
  let ρ := Spec.map (CommRingCat.ofHom
    (Subalgebra.inclusion i.property.2).toRingHom)
  let ε := Spec.map (CommRingCat.ofHom (algebraMap i.val K))
  let m := (modelScalarCone S a).π.app (op i)
  have hcoeff : ε ≫ ρ = κ := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  have hfst : m ≫ pullback.fst ρ a = pullback.fst κ a ≫ ε := by
    change (pullback.lift _ _ _) ≫ pullback.fst ρ a = _
    exact pullback.lift_fst _ _ _
  have hsnd : m ≫ pullback.snd ρ a = pullback.snd κ a := by
    change (pullback.lift _ _ _) ≫ pullback.snd ρ a = _
    exact pullback.lift_snd _ _ _
  have houter : IsPullback (m ≫ pullback.snd ρ a) (pullback.fst κ a)
      a (ε ≫ ρ) := by
    rw [hsnd, hcoeff]
    exact (IsPullback.of_hasPullback κ a).flip
  exact houter.of_right hfst (IsPullback.of_hasPullback ρ a).flip

end
end FrobeniusSplitting
