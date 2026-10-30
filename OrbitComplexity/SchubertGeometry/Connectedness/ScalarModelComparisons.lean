import OrbitComplexity.SchubertGeometry.Connectedness.AppendSchubertConnected
import OrbitComplexity.FrobeniusSplitting.Normality.Limits.ModelStageMaps
import OrbitComplexity.FrobeniusSplitting.Normality.Connectedness.IntegralFamily

/-! # Comparisons of iterated scalar models

Two coefficient extensions of a prescribed model identify with its extension
to the final coefficient stage. The comparison retains the old projection,
commutes with every prescribed arrow, and transports endpoint and structure
morphism properties.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open FrobeniusSplitting

noncomputable section
universe u v
namespace SchubertGeometry

open private scalar_model scalar_tower_iso scalar_tower_original scalar_tower_natural
  scalar_tower_gc
  from OrbitComplexity.SchubertGeometry.Connectedness.AppendSchubertConnected

private def towerIso {B T U : Scheme.{u}} (κ : T ⟶ B) (τ : U ⟶ T)
    (ρ : U ⟶ B) (h : τ ≫ κ = ρ) (X : Over B) :
    scalar_model τ (scalar_model κ X) ≅ scalar_model ρ X :=
  scalar_tower_iso τ κ X ≪≫ eqToIso (congrArg (fun a => scalar_model a X) h)

private theorem tower_original {B T U : Scheme.{u}} (κ : T ⟶ B) (τ : U ⟶ T)
    (ρ : U ⟶ B) (h : τ ≫ κ = ρ) (X : Over B) :
    (towerIso κ τ ρ h X).hom.left ≫ pullback.snd ρ X.hom =
      pullback.snd τ (scalar_model κ X).hom ≫ pullback.snd κ X.hom := by
  cases h
  change (scalar_tower_iso τ κ X).hom.left ≫ pullback.snd (τ ≫ κ) X.hom = _
  exact scalar_tower_original τ κ X

private theorem conjugate {A : Type v} [Category A]
    {X Y X' Y' : A} (E : X ≅ X') (F : Y ≅ Y')
    (f : X ⟶ Y) (g : X' ⟶ Y') (h : E.hom ≫ g = f ≫ F.hom) :
    g = E.inv ≫ f ≫ F.hom := by
  calc
    g = E.inv ≫ (E.hom ≫ g) := (Iso.inv_hom_id_assoc E g).symm
    _ = E.inv ≫ (f ≫ F.hom) := congrArg (fun t => E.inv ≫ t) h
    _ = E.inv ≫ f ≫ F.hom := rfl

private theorem proper_square {X Y X' Y' : Scheme.{u}} (E : X ≅ X') (F : Y ≅ Y')
    (f : X ⟶ Y) (g : X' ⟶ Y') (h : E.hom ≫ g = f ≫ F.hom)
    (hp : IsProper f) : IsProper g := by
  let : IsProper f := hp
  rw [conjugate E F f g h]
  infer_instance

private theorem over_proper {B : Scheme.{u}} {X Y X' Y' : Over B}
    (E : X ≅ X') (F : Y ≅ Y') (f : X ⟶ Y) (g : X' ⟶ Y')
    (h : E.hom ≫ g = f ≫ F.hom) (hp : IsProper f.left) : IsProper g.left :=
  proper_square ((Over.forget B).mapIso E) ((Over.forget B).mapIso F)
    f.left g.left (congrArg Over.Hom.left h) hp

private theorem tower_properties {B T U : Scheme.{u}} (κ : T ⟶ B) (τ : U ⟶ T)
    (ρ : U ⟶ B) (h : τ ≫ κ = ρ) {X Y : Over B} (f : X ⟶ Y)
    (hp : IsProper (chosenScalarArrow τ (chosenScalarArrow κ f)).left)
    (hc : GeometricallyConnected (chosenScalarArrow τ (chosenScalarArrow κ f)).left)
    (ht : GeometricallyConnected (scalar_model τ (scalar_model κ Y)).hom) :
    IsProper (chosenScalarArrow ρ f).left ∧
      GeometricallyConnected (chosenScalarArrow ρ f).left ∧
      GeometricallyConnected (scalar_model ρ Y).hom := by
  cases h
  exact ⟨over_proper (scalar_tower_iso τ κ X) (scalar_tower_iso τ κ Y) _ _
      (scalar_tower_natural τ κ f) hp,
    scalar_tower_gc τ κ f hc,
    geomConnected_over_iso (scalar_tower_iso τ κ Y) ht⟩

/-- Two successive coefficient stages determine one stage over the original
coefficient algebra, with the same final subalgebra. -/
abbrev singleScalarStage {K : Type u} [CommRing K] (S : Subalgebra ℤ K)
    (k : CoefficientStage S) (l : CoefficientStage k.val) : CoefficientStage S :=
  ⟨l.val, l.property.1, le_trans k.property.2 l.property.2⟩

private theorem stage_composite {K : Type u} [CommRing K] (S : Subalgebra ℤ K)
    (k : CoefficientStage S) (l : CoefficientStage k.val) :
    Spec.map (CommRingCat.ofHom (Subalgebra.inclusion l.property.2).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom) =
        Spec.map (CommRingCat.ofHom
          (Subalgebra.inclusion (singleScalarStage S k l).property.2).toRingHom) := by
  rw [← Spec.map_comp]
  rfl

/-- Iterated extension of a prescribed model is isomorphic over the final
coefficient base to its extension along the composite coefficient inclusion. -/
def scalarModelIso {K : Type u} [CommRing K] (S : Subalgebra ℤ K)
    (k : CoefficientStage S) (l : CoefficientStage k.val)
    (X : Over (Spec (.of S))) :
    stageScalarModel k.val (stageScalarModel S X.hom k).hom l ≅
      stageScalarModel S X.hom (singleScalarStage S k l) :=
  towerIso
    (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom))
    (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion l.property.2).toRingHom))
    (Spec.map (CommRingCat.ofHom
      (Subalgebra.inclusion (singleScalarStage S k l).property.2).toRingHom))
    (stage_composite S k l) X

/-- The iterated-model comparison retains the projection to the original model. -/
theorem scalarModelIso_original {K : Type u} [CommRing K] (S : Subalgebra ℤ K)
    (k : CoefficientStage S) (l : CoefficientStage k.val)
    (X : Over (Spec (.of S))) :
    (scalarModelIso S k l X).hom.left ≫
      pullback.snd (Spec.map (CommRingCat.ofHom
        (Subalgebra.inclusion (singleScalarStage S k l).property.2).toRingHom)) X.hom =
      pullback.snd
        (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion l.property.2).toRingHom))
        (stageScalarModel S X.hom k).hom ≫
          pullback.snd
            (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom))
            X.hom :=
  tower_original _ _ _ (stage_composite S k l) X

/-- Properness and geometrically connected endpoint and target fibres pass
from the iterated coefficient model to the same single-stage model. -/
theorem scalarModelIso_properties {K : Type u} [CommRing K] (S : Subalgebra ℤ K)
    (k : CoefficientStage S) (l : CoefficientStage k.val)
    {X Y : Over (Spec (.of S))} (f : X ⟶ Y)
    (hp : IsProper (chosenScalarArrow
      (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion l.property.2).toRingHom))
      (chosenScalarArrow
        (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom)) f)).left)
    (hc : GeometricallyConnected (chosenScalarArrow
      (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion l.property.2).toRingHom))
      (chosenScalarArrow
        (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom)) f)).left)
    (ht : GeometricallyConnected (stageScalarModel k.val
      (stageScalarModel S Y.hom k).hom l).hom) :
    IsProper (chosenScalarArrow
      (Spec.map (CommRingCat.ofHom
        (Subalgebra.inclusion (singleScalarStage S k l).property.2).toRingHom)) f).left ∧
    GeometricallyConnected (chosenScalarArrow
      (Spec.map (CommRingCat.ofHom
        (Subalgebra.inclusion (singleScalarStage S k l).property.2).toRingHom)) f).left ∧
    GeometricallyConnected (stageScalarModel S Y.hom (singleScalarStage S k l)).hom :=
  tower_properties
    (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom))
    (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion l.property.2).toRingHom))
    (Spec.map (CommRingCat.ofHom
      (Subalgebra.inclusion (singleScalarStage S k l).property.2).toRingHom))
    (stage_composite S k l) f hp hc ht

end SchubertGeometry
