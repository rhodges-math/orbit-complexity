import Batteries.Tactic.Lint
import OrbitComplexity.FrobeniusSplitting.Normality.Connectedness.RetainedIsomorphisms

/-!
# Retaining full equations of specified stage arrows

-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace FrobeniusSplitting

universe u v

variable {K : Type u} [CommRing K] (S : Subalgebra ℤ K)

private theorem stage_arrow_base
    {X Y : Scheme.{u}} (a : X ⟶ Spec (.of S)) (b : Y ⟶ Spec (.of S))
    (i : CoefficientStage S) (f : stageScalarModel S a i ⟶ stageScalarModel S b i) :
    (f.left ≫ pullback.snd _ b) ≫ b = (modelScalarBase S a).app (op i) := by
  let κ := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion i.property.2).toRingHom)
  let f₀ : pullback κ a ⟶ pullback κ b := f.left
  have hw : f₀ ≫ pullback.fst κ b = pullback.fst κ a := f.w
  change (f₀ ≫ pullback.snd κ b) ≫ b = pullback.snd κ a ≫ a
  calc
    (f₀ ≫ pullback.snd κ b) ≫ b = f₀ ≫ (pullback.snd κ b ≫ b) :=
      Category.assoc _ _ _
    _ = f₀ ≫ (pullback.fst κ b ≫ κ) :=
      congrArg (fun q => f₀ ≫ q) (pullback.condition (f := κ) (g := b)).symm
    _ = (f₀ ≫ pullback.fst κ b) ≫ κ := (Category.assoc _ _ _).symm
    _ = pullback.fst κ a ≫ κ := congrArg (fun q => q ≫ κ) hw
    _ = pullback.snd κ a ≫ a := pullback.condition

private theorem projected_generic_eq
    {A B C D : Scheme.{u}} (q : A ⟶ B) (f g : B ⟶ C) (p : C ⟶ D)
    (h : q ≫ f = q ≫ g) : q ≫ (f ≫ p) = q ≫ (g ≫ p) := by
  calc
    q ≫ (f ≫ p) = (q ≫ f) ≫ p := (Category.assoc _ _ _).symm
    _ = (q ≫ g) ≫ p := congrArg (fun k => k ≫ p) h
    _ = q ≫ (g ≫ p) := Category.assoc _ _ _

private theorem extended_original_projection
    {X Y : Scheme.{u}} (a : X ⟶ Spec (.of S)) (b : Y ⟶ Spec (.of S))
    {i j : CoefficientStage S} (hij : i ≤ j)
    (f : stageScalarModel S a i ⟶ stageScalarModel S b i) :
    (extendModelMorphism S a b hij f).left ≫ pullback.snd _ b =
      stageScalarTransition S a hij ≫ (f.left ≫ pullback.snd _ b) := by
  let κi := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion i.property.2).toRingHom)
  let κj := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion j.property.2).toRingHom)
  let f₀ : pullback κi a ⟶ pullback κi b := f.left
  let f₁ : pullback κj a ⟶ pullback κj b := (extendModelMorphism S a b hij f).left
  let tA : pullback κj a ⟶ pullback κi a := stageScalarTransition S a hij
  let tB : pullback κj b ⟶ pullback κi b := stageScalarTransition S b hij
  have ht : f₁ ≫ tB = tA ≫ f₀ := extendModelMorphism_transition S a b hij f
  have hs : tB ≫ pullback.snd κi b = pullback.snd κj b :=
    stageScalarTransition_snd S b hij
  change f₁ ≫ pullback.snd κj b = tA ≫ (f₀ ≫ pullback.snd κi b)
  calc
    f₁ ≫ pullback.snd κj b = f₁ ≫ (tB ≫ pullback.snd κi b) :=
      congrArg (fun q => f₁ ≫ q) hs.symm
    _ = (f₁ ≫ tB) ≫ pullback.snd κi b := (Category.assoc _ _ _).symm
    _ = (tA ≫ f₀) ≫ pullback.snd κi b :=
      congrArg (fun q => q ≫ pullback.snd κi b) ht
    _ = tA ≫ (f₀ ≫ pullback.snd κi b) := Category.assoc _ _ _

/-- Equality of original-target projections after scalar restriction determines
the full extended Over arrows, using their same target Cartesian square. -/
theorem stage_arrow_eq_of_projection
    {X Y : Scheme.{u}} (a : X ⟶ Spec (.of S)) (b : Y ⟶ Spec (.of S))
    {i j : CoefficientStage S} (hij : i ≤ j)
    (f g : stageScalarModel S a i ⟶ stageScalarModel S b i)
    (h : stageScalarTransition S a hij ≫ (f.left ≫ pullback.snd _ b) =
      stageScalarTransition S a hij ≫ (g.left ≫ pullback.snd _ b)) :
    extendModelMorphism S a b hij f = extendModelMorphism S a b hij g := by
  let κj := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion j.property.2).toRingHom)
  apply Over.OverMorphism.ext
  apply (IsPullback.of_hasPullback κj b).hom_ext
  · exact (extendModelMorphism S a b hij f).w.trans
      (extendModelMorphism S a b hij g).w.symm
  · exact (extended_original_projection S a b hij f).trans
      (h.trans (extended_original_projection S a b hij g).symm)

/-- Two specified stage arrows with equal generic precompositions become
equal as the specified extended Over arrows at a later finite stage. -/
theorem exists_stage_arrow_eq
    (hS : S.FG) {X Y : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (a : X ⟶ Spec (.of S)) (b : Y ⟶ Spec (.of S)) [LocallyOfFiniteType b]
    (i : CoefficientStage S)
    (f g : stageScalarModel S a i ⟶ stageScalarModel S b i)
    (hfg : (modelScalarCone S a).π.app (op i) ≫ f.left =
      (modelScalarCone S a).π.app (op i) ≫ g.left) :
    ∃ (j : CoefficientStage S) (hij : i ≤ j),
      extendModelMorphism S a b hij f = extendModelMorphism S a b hij g := by
  obtain ⟨j, hij, h⟩ := exists_scalar_equality S hS a b i
    (f.left ≫ pullback.snd _ b) (g.left ≫ pullback.snd _ b)
    (stage_arrow_base S a b i f) (stage_arrow_base S a b i g)
    (projected_generic_eq _ _ _ _ hfg)
  exact ⟨j, hij, stage_arrow_eq_of_projection S a b hij f g h⟩

/-- A finite heterogeneous family of specified stage-arrow equations is
retained jointly above the given stage, as full equations in Over. -/
theorem exists_stage_arrow_eqs
    {I : Type v} [Fintype I] (hS : S.FG) (X Y : I → Scheme.{u})
    [∀ r, CompactSpace (X r)] [∀ r, QuasiSeparatedSpace (X r)]
    (a : ∀ r, X r ⟶ Spec (.of S)) (b : ∀ r, Y r ⟶ Spec (.of S))
    [∀ r, LocallyOfFiniteType (b r)]
    (i : CoefficientStage S)
    (f g : ∀ r, stageScalarModel S (a r) i ⟶ stageScalarModel S (b r) i)
    (hfg : ∀ r, (modelScalarCone S (a r)).π.app (op i) ≫ (f r).left =
      (modelScalarCone S (a r)).π.app (op i) ≫ (g r).left) :
    ∃ (j : CoefficientStage S) (hij : i ≤ j), ∀ r,
      extendModelMorphism S (a r) (b r) hij (f r) =
        extendModelMorphism S (a r) (b r) hij (g r) := by
  let f₀ r := (f r).left ≫ pullback.snd _ (b r)
  let g₀ r := (g r).left ≫ pullback.snd _ (b r)
  obtain ⟨j, hij, h⟩ := exists_retained_equations S hS X Y a b i f₀ g₀
    (fun r => stage_arrow_base S (a r) (b r) i (f r))
    (fun r => stage_arrow_base S (a r) (b r) i (g r))
    (fun r => projected_generic_eq _ _ _ _ (hfg r))
  exact ⟨j, hij, fun r => stage_arrow_eq_of_projection S (a r) (b r) hij (f r) (g r) (h r)⟩

end FrobeniusSplitting
