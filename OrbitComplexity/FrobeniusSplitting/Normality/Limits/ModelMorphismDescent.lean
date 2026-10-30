import OrbitComplexity.FrobeniusSplitting.Normality.Limits.ModelScalarLimit

/-! # morphisms between the specified scalar models -/

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace FrobeniusSplitting

universe u

/-- The original model after extension to the given coefficient ring K. -/
def genericScalarModel {K : Type u} [CommRing K] (S : Subalgebra ℤ K)
    {X : Scheme.{u}} (a : X ⟶ Spec (.of S)) : Over (Spec (.of K)) :=
  Over.mk (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap S K))) a)

/-- The same model after extension to one of the prescribed finite stages. -/
def stageScalarModel {K : Type u} [CommRing K] (S : Subalgebra ℤ K)
    {X : Scheme.{u}} (a : X ⟶ Spec (.of S)) (i : CoefficientStage S) :
    Over (Spec (.of i.val)) :=
  Over.mk (pullback.fst (Spec.map (CommRingCat.ofHom
    (Subalgebra.inclusion i.property.2).toRingHom)) a)

private theorem scalarLeg_fst {K : Type u} [CommRing K] (S : Subalgebra ℤ K)
    {X : Scheme.{u}} (a : X ⟶ Spec (.of S)) (i : CoefficientStage S) :
    (modelScalarCone S a).π.app (op i) ≫ (stageScalarModel S a i).hom =
      (genericScalarModel S a).hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap i.val K)) := by
  change pullback.lift _ _ _ ≫ pullback.fst _ a = _
  exact pullback.lift_fst _ _ _

private theorem scalarLeg_snd {K : Type u} [CommRing K] (S : Subalgebra ℤ K)
    {X : Scheme.{u}} (a : X ⟶ Spec (.of S)) (i : CoefficientStage S) :
    (modelScalarCone S a).π.app (op i) ≫ pullback.snd _ a =
      pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap S K))) a := by
  change pullback.lift _ _ _ ≫ pullback.snd _ a = _
  exact pullback.lift_snd _ _ _

/-- A map over K descends as a map over one enlarged coefficient ring
between the pullbacks of the same two models. Its generic square is
the specified original map, including both scalar projections. -/
theorem exists_model_morphism
    {K : Type u} [CommRing K] (S : Subalgebra ℤ K) (hS : S.FG)
    {X Y : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (a : X ⟶ Spec (.of S)) (b : Y ⟶ Spec (.of S))
    [LocallyOfFinitePresentation b]
    (g : genericScalarModel S a ⟶ genericScalarModel S b) :
    ∃ (i : CoefficientStage S) (f : stageScalarModel S a i ⟶ stageScalarModel S b i),
      (modelScalarCone S a).π.app (op i) ≫ f.left =
        g.left ≫ (modelScalarCone S b).π.app (op i) := by
  let κ := Spec.map (CommRingCat.ofHom (algebraMap S K))
  let gK : pullback κ a ⟶ pullback κ b := g.left
  have hgw : gK ≫ pullback.fst κ b = pullback.fst κ a := g.w
  have hg : (gK ≫ pullback.snd κ b) ≫ b = pullback.snd κ a ≫ a := by
    calc
      (gK ≫ pullback.snd κ b) ≫ b = gK ≫ (pullback.snd κ b ≫ b) :=
        Category.assoc _ _ _
      _ = gK ≫ (pullback.fst κ b ≫ κ) :=
        congrArg (fun q => gK ≫ q) (pullback.condition (f := κ) (g := b)).symm
      _ = (gK ≫ pullback.fst κ b) ≫ κ :=
        (Category.assoc _ _ _).symm
      _ = pullback.fst κ a ≫ κ := congrArg (fun q => q ≫ κ) hgw
      _ = pullback.snd κ a ≫ a := pullback.condition
  obtain ⟨i, f, hnative, hbase⟩ :=
    exists_scalar_morphism S hS a b (gK ≫ pullback.snd κ b) hg
  let κi := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion i.property.2).toRingHom)
  let κKi := Spec.map (CommRingCat.ofHom (algebraMap i.val K))
  let fi : pullback κi a ⟶ Y := f
  let qA : pullback κ a ⟶ pullback κi a := (modelScalarCone S a).π.app (op i)
  let qB : pullback κ b ⟶ pullback κi b := (modelScalarCone S b).π.app (op i)
  have hfi : fi ≫ b = pullback.snd κi a ≫ a := hbase
  have hnativei : qA ≫ fi = gK ≫ pullback.snd κ b := hnative
  have hqA : qA ≫ pullback.fst κi a = pullback.fst κ a ≫ κKi :=
    scalarLeg_fst S a i
  have hqB : qB ≫ pullback.fst κi b = pullback.fst κ b ≫ κKi :=
    scalarLeg_fst S b i
  have hqBsnd : qB ≫ pullback.snd κi b = pullback.snd κ b :=
    scalarLeg_snd S b i
  have hcomm : pullback.fst κi a ≫ κi = fi ≫ b :=
    (pullback.condition (f := κi) (g := a)).trans hfi.symm
  let fRi : pullback κi a ⟶ pullback κi b :=
    pullback.lift (pullback.fst κi a) fi hcomm
  have hfRfst : fRi ≫ pullback.fst κi b = pullback.fst κi a :=
    pullback.lift_fst _ _ _
  have hfRsnd : fRi ≫ pullback.snd κi b = fi := pullback.lift_snd _ _ _
  let fR : stageScalarModel S a i ⟶ stageScalarModel S b i :=
    Over.homMk fRi hfRfst
  refine ⟨i, fR, ?_⟩
  change qA ≫ fRi = gK ≫ qB
  apply pullback.hom_ext
  · calc
      (qA ≫ fRi) ≫ pullback.fst κi b = qA ≫ (fRi ≫ pullback.fst κi b) :=
        Category.assoc _ _ _
      _ = qA ≫ pullback.fst κi a := congrArg (fun q => qA ≫ q) hfRfst
      _ = pullback.fst κ a ≫ κKi := hqA
      _ = (gK ≫ pullback.fst κ b) ≫ κKi :=
        congrArg (fun q => q ≫ κKi) hgw.symm
      _ = gK ≫ (pullback.fst κ b ≫ κKi) := Category.assoc _ _ _
      _ = gK ≫ (qB ≫ pullback.fst κi b) := congrArg (fun q => gK ≫ q) hqB.symm
      _ = (gK ≫ qB) ≫ pullback.fst κi b := (Category.assoc _ _ _).symm
  · calc
      (qA ≫ fRi) ≫ pullback.snd κi b = qA ≫ (fRi ≫ pullback.snd κi b) :=
        Category.assoc _ _ _
      _ = qA ≫ fi := congrArg (fun q => qA ≫ q) hfRsnd
      _ = gK ≫ pullback.snd κ b := hnativei
      _ = gK ≫ (qB ≫ pullback.snd κi b) := congrArg (fun q => gK ≫ q) hqBsnd.symm
      _ = (gK ≫ qB) ≫ pullback.snd κi b := (Category.assoc _ _ _).symm

/-- Equality of maps is retained at a later finite coefficient
stage. Both maps are restricted along the original transition of the model. -/
@[nolint unusedArguments]
theorem exists_scalar_equality
    {K : Type u} [CommRing K] (S : Subalgebra ℤ K) (hS : S.FG)
    {X Y : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (a : X ⟶ Spec (.of S)) (b : Y ⟶ Spec (.of S)) [LocallyOfFiniteType b]
    (i : CoefficientStage S) (f g : (modelScalarStages S a).obj (op i) ⟶ Y)
    (hf : f ≫ b = (modelScalarBase S a).app (op i))
    (hg : g ≫ b = (modelScalarBase S a).app (op i))
    (hfg : (modelScalarCone S a).π.app (op i) ≫ f =
      (modelScalarCone S a).π.app (op i) ≫ g) :
    ∃ (j : CoefficientStage S) (hij : i ≤ j),
      (modelScalarStages S a).map (homOfLE hij).op ≫ f =
        (modelScalarStages S a).map (homOfLE hij).op ≫ g := by
  let : Nonempty (CoefficientStage S) := ⟨⟨S, hS, le_rfl⟩⟩
  obtain ⟨j, hji, h⟩ := Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType
    (modelScalarStages S a) (modelScalarBase S a) b
    (modelScalarCone S a) (modelScalarLimit S hS a) f g hf.symm hg.symm hfg
  exact ⟨j.unop, leOfHom hji.unop, h⟩


end FrobeniusSplitting
