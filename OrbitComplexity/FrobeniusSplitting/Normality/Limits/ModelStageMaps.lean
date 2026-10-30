import OrbitComplexity.FrobeniusSplitting.Normality.Limits.ModelMorphismDescent

/-! # restriction of the retained maps to a larger coefficient stage -/

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace FrobeniusSplitting

universe u

/-- This is the original transition in the scalar-pullback diagram. -/
def stageScalarTransition {K : Type u} [CommRing K] (S : Subalgebra ℤ K)
    {X : Scheme.{u}} (a : X ⟶ Spec (.of S))
    {i j : CoefficientStage S} (hij : i ≤ j) :
    (stageScalarModel S a j).left ⟶ (stageScalarModel S a i).left :=
  (modelScalarStages S a).map (homOfLE hij).op

/-- A scalar transition commutes with the coefficient-base projections. -/
theorem stageScalarTransition_fst {K : Type u} [CommRing K] (S : Subalgebra ℤ K)
    {X : Scheme.{u}} (a : X ⟶ Spec (.of S))
    {i j : CoefficientStage S} (hij : i ≤ j) :
    stageScalarTransition S a hij ≫ (stageScalarModel S a i).hom =
      (stageScalarModel S a j).hom ≫
        Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hij).toRingHom) := by
  change pullback.lift _ _ _ ≫ pullback.fst _ a = _
  exact pullback.lift_fst _ _ _

/-- A scalar transition preserves the projection to the original scheme. -/
theorem stageScalarTransition_snd {K : Type u} [CommRing K] (S : Subalgebra ℤ K)
    {X : Scheme.{u}} (a : X ⟶ Spec (.of S))
    {i j : CoefficientStage S} (hij : i ≤ j) :
    stageScalarTransition S a hij ≫ pullback.snd _ a = pullback.snd _ a := by
  change pullback.lift _ _ _ ≫ pullback.snd _ a = _
  exact pullback.lift_snd _ _ _

/-- Increasing the coefficient stage is an Cartesian base change. -/
theorem stageScalarCartesian {K : Type u} [CommRing K] (S : Subalgebra ℤ K)
    {X : Scheme.{u}} (a : X ⟶ Spec (.of S))
    {i j : CoefficientStage S} (hij : i ≤ j) :
    IsPullback (stageScalarTransition S a hij) (stageScalarModel S a j).hom
      (stageScalarModel S a i).hom
      (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hij).toRingHom)) := by
  let κi := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion i.property.2).toRingHom)
  let κj := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion j.property.2).toRingHom)
  let ρ := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hij).toRingHom)
  have hρ : ρ ≫ κi = κj := by
    rw [← Spec.map_comp]
    rfl
  have houter : IsPullback (stageScalarTransition S a hij ≫ pullback.snd κi a)
      (stageScalarModel S a j).hom a (ρ ≫ κi) := by
    rw [stageScalarTransition_snd, hρ]
    exact (IsPullback.of_hasPullback κj a).flip
  exact houter.of_right (stageScalarTransition_fst S a hij)
    (IsPullback.of_hasPullback κi a).flip

/-- The retained map is restricted by the Cartesian square itself. -/
def extendModelMorphism {K : Type u} [CommRing K] (S : Subalgebra ℤ K)
    {X Y : Scheme.{u}} (a : X ⟶ Spec (.of S)) (b : Y ⟶ Spec (.of S))
    {i j : CoefficientStage S} (hij : i ≤ j)
    (f : stageScalarModel S a i ⟶ stageScalarModel S b i) :
    stageScalarModel S a j ⟶ stageScalarModel S b j :=
  Over.homMk ((stageScalarCartesian S b hij).lift
    (stageScalarTransition S a hij ≫ f.left) (stageScalarModel S a j).hom
    (by rw [Category.assoc, f.w]; exact stageScalarTransition_fst S a hij))
    ((stageScalarCartesian S b hij).lift_snd _ _ _)

/-- Extending a model morphism commutes with its stage transitions. -/
theorem extendModelMorphism_transition
    {K : Type u} [CommRing K] (S : Subalgebra ℤ K)
    {X Y : Scheme.{u}} (a : X ⟶ Spec (.of S)) (b : Y ⟶ Spec (.of S))
    {i j : CoefficientStage S} (hij : i ≤ j)
    (f : stageScalarModel S a i ⟶ stageScalarModel S b i) :
    (extendModelMorphism S a b hij f).left ≫ stageScalarTransition S b hij =
      stageScalarTransition S a hij ≫ f.left :=
  (stageScalarCartesian S b hij).lift_fst _ _ _

private theorem scalarLeg_fst
    {K : Type u} [CommRing K] (S : Subalgebra ℤ K)
    {X : Scheme.{u}} (a : X ⟶ Spec (.of S)) (i : CoefficientStage S) :
    (modelScalarCone S a).π.app (op i) ≫ (stageScalarModel S a i).hom =
      (genericScalarModel S a).hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap i.val K)) := by
  change pullback.lift _ _ _ ≫ pullback.fst _ a = _
  exact pullback.lift_fst _ _ _

/-- The extension keeps the specified original map, without using
injectivity or cancellation of the coefficient transition. -/
theorem extendModelMorphism_baseChange
    {K : Type u} [CommRing K] (S : Subalgebra ℤ K)
    {X Y : Scheme.{u}} (a : X ⟶ Spec (.of S)) (b : Y ⟶ Spec (.of S))
    {i j : CoefficientStage S} (hij : i ≤ j)
    (f : stageScalarModel S a i ⟶ stageScalarModel S b i)
    (g : genericScalarModel S a ⟶ genericScalarModel S b)
    (hg : (modelScalarCone S a).π.app (op i) ≫ f.left =
      g.left ≫ (modelScalarCone S b).π.app (op i)) :
    (modelScalarCone S a).π.app (op j) ≫ (extendModelMorphism S a b hij f).left =
      g.left ≫ (modelScalarCone S b).π.app (op j) := by
  let κ := Spec.map (CommRingCat.ofHom (algebraMap S K))
  let κi := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion i.property.2).toRingHom)
  let κj := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion j.property.2).toRingHom)
  let ρ := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hij).toRingHom)
  let κKj := Spec.map (CommRingCat.ofHom (algebraMap j.val K))
  let qXi : pullback κ a ⟶ pullback κi a := (modelScalarCone S a).π.app (op i)
  let qXj : pullback κ a ⟶ pullback κj a := (modelScalarCone S a).π.app (op j)
  let qYi : pullback κ b ⟶ pullback κi b := (modelScalarCone S b).π.app (op i)
  let qYj : pullback κ b ⟶ pullback κj b := (modelScalarCone S b).π.app (op j)
  let tA : pullback κj a ⟶ pullback κi a := stageScalarTransition S a hij
  let tB : pullback κj b ⟶ pullback κi b := stageScalarTransition S b hij
  let fI : pullback κi a ⟶ pullback κi b := f.left
  let fJ : pullback κj a ⟶ pullback κj b :=
    (extendModelMorphism S a b hij f).left
  let gK : pullback κ a ⟶ pullback κ b := g.left
  have hqX : qXj ≫ tA = qXi := (modelScalarCone S a).w ((homOfLE hij).op)
  have hqY : qYj ≫ tB = qYi := (modelScalarCone S b).w ((homOfLE hij).op)
  have ht : fJ ≫ tB = tA ≫ fI := extendModelMorphism_transition S a b hij f
  have hn : qXi ≫ fI = gK ≫ qYi := hg
  have hfJ : fJ ≫ pullback.fst κj b = pullback.fst κj a :=
    (extendModelMorphism S a b hij f).w
  have hgK : gK ≫ pullback.fst κ b = pullback.fst κ a := g.w
  have hqXfst : qXj ≫ pullback.fst κj a = pullback.fst κ a ≫ κKj :=
    scalarLeg_fst S a j
  have hqYfst : qYj ≫ pullback.fst κj b = pullback.fst κ b ≫ κKj :=
    scalarLeg_fst S b j
  have hsquare : IsPullback tB (pullback.fst κj b) (pullback.fst κi b) ρ :=
    stageScalarCartesian S b hij
  change qXj ≫ fJ = gK ≫ qYj
  apply hsquare.hom_ext
  · calc
      (qXj ≫ fJ) ≫ tB = qXj ≫ (fJ ≫ tB) := Category.assoc _ _ _
      _ = qXj ≫ (tA ≫ fI) := congrArg (fun q => qXj ≫ q) ht
      _ = (qXj ≫ tA) ≫ fI := (Category.assoc _ _ _).symm
      _ = qXi ≫ fI := congrArg (fun q => q ≫ fI) hqX
      _ = gK ≫ qYi := hn
      _ = gK ≫ (qYj ≫ tB) := congrArg (fun q => gK ≫ q) hqY.symm
      _ = (gK ≫ qYj) ≫ tB := (Category.assoc _ _ _).symm
  · calc
      (qXj ≫ fJ) ≫ pullback.fst κj b = qXj ≫ (fJ ≫ pullback.fst κj b) :=
        Category.assoc _ _ _
      _ = qXj ≫ pullback.fst κj a := congrArg (fun q => qXj ≫ q) hfJ
      _ = pullback.fst κ a ≫ κKj := hqXfst
      _ = (gK ≫ pullback.fst κ b) ≫ κKj := congrArg (fun q => q ≫ κKj) hgK.symm
      _ = gK ≫ (pullback.fst κ b ≫ κKj) := Category.assoc _ _ _
      _ = gK ≫ (qYj ≫ pullback.fst κj b) := congrArg (fun q => gK ≫ q) hqYfst.symm
      _ = (gK ≫ qYj) ≫ pullback.fst κj b := (Category.assoc _ _ _).symm


end FrobeniusSplitting
