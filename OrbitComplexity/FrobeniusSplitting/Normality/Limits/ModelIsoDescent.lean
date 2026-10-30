import OrbitComplexity.FrobeniusSplitting.Normality.Limits.ModelStageMaps

/-! # Retaining an isomorphism on the same two models -/

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace FrobeniusSplitting

universe u

private theorem modelMap_base {K : Type u} [CommRing K] (S : Subalgebra ℤ K)
    {X Y : Scheme.{u}} (a : X ⟶ Spec (.of S)) (b : Y ⟶ Spec (.of S))
    (i : CoefficientStage S) (f : stageScalarModel S a i ⟶ stageScalarModel S b i) :
    (f.left ≫ pullback.snd _ b) ≫ b = (modelScalarBase S a).app (op i) := by
  let κi := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion i.property.2).toRingHom)
  let fI : pullback κi a ⟶ pullback κi b := f.left
  have hw : fI ≫ pullback.fst κi b = pullback.fst κi a := f.w
  change (fI ≫ pullback.snd κi b) ≫ b = pullback.snd κi a ≫ a
  calc
    (fI ≫ pullback.snd κi b) ≫ b = fI ≫ (pullback.snd κi b ≫ b) :=
      Category.assoc _ _ _
    _ = fI ≫ (pullback.fst κi b ≫ κi) :=
      congrArg (fun q => fI ≫ q) (pullback.condition (f := κi) (g := b)).symm
    _ = (fI ≫ pullback.fst κi b) ≫ κi := (Category.assoc _ _ _).symm
    _ = pullback.fst κi a ≫ κi := congrArg (fun q => q ≫ κi) hw
    _ = pullback.snd κi a ≫ a := pullback.condition

private theorem generic_inverse_projection
    {K : Type u} [CommRing K] (S : Subalgebra ℤ K)
    {X Y : Scheme.{u}} (a : X ⟶ Spec (.of S)) (b : Y ⟶ Spec (.of S))
    (i : CoefficientStage S)
    (E : genericScalarModel S a ≅ genericScalarModel S b)
    (f : stageScalarModel S a i ⟶ stageScalarModel S b i)
    (g : stageScalarModel S b i ⟶ stageScalarModel S a i)
    (hf : (modelScalarCone S a).π.app (op i) ≫ f.left =
      E.hom.left ≫ (modelScalarCone S b).π.app (op i))
    (hg : (modelScalarCone S b).π.app (op i) ≫ g.left =
      E.inv.left ≫ (modelScalarCone S a).π.app (op i)) :
    (modelScalarCone S a).π.app (op i) ≫
        ((f ≫ g).left ≫ pullback.snd _ a) =
      (modelScalarCone S a).π.app (op i) ≫ pullback.snd _ a := by
  let κ := Spec.map (CommRingCat.ofHom (algebraMap S K))
  let κi := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion i.property.2).toRingHom)
  let qX : pullback κ a ⟶ pullback κi a := (modelScalarCone S a).π.app (op i)
  let qY : pullback κ b ⟶ pullback κi b := (modelScalarCone S b).π.app (op i)
  let fI : pullback κi a ⟶ pullback κi b := f.left
  let gI : pullback κi b ⟶ pullback κi a := g.left
  let eh : pullback κ a ⟶ pullback κ b := E.hom.left
  let ei : pullback κ b ⟶ pullback κ a := E.inv.left
  have hf0 : qX ≫ fI = eh ≫ qY := hf
  have hg0 : qY ≫ gI = ei ≫ qX := hg
  have hE : eh ≫ ei = 𝟙 _ := congrArg Over.Hom.left E.hom_inv_id
  have hq : qX ≫ (fI ≫ gI) = qX := by
    calc
      qX ≫ (fI ≫ gI) = (qX ≫ fI) ≫ gI := (Category.assoc _ _ _).symm
      _ = (eh ≫ qY) ≫ gI := congrArg (fun q => q ≫ gI) hf0
      _ = eh ≫ (qY ≫ gI) := Category.assoc _ _ _
      _ = eh ≫ (ei ≫ qX) := congrArg (fun q => eh ≫ q) hg0
      _ = (eh ≫ ei) ≫ qX := (Category.assoc _ _ _).symm
      _ = 𝟙 _ ≫ qX := congrArg (fun q => q ≫ qX) hE
      _ = qX := Category.id_comp _
  change qX ≫ ((fI ≫ gI) ≫ pullback.snd κi a) = qX ≫ pullback.snd κi a
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (fun q => q ≫ pullback.snd κi a) hq)

private theorem transition_comp {K : Type u} [CommRing K] (S : Subalgebra ℤ K)
    {X : Scheme.{u}} (a : X ⟶ Spec (.of S))
    {i j k : CoefficientStage S} (hij : i ≤ j) (hjk : j ≤ k) :
    stageScalarTransition S a hjk ≫ stageScalarTransition S a hij =
      stageScalarTransition S a (hij.trans hjk) := by
  let D := modelScalarStages S a
  have h : (homOfLE hjk).op ≫ (homOfLE hij).op =
      (homOfLE (hij.trans hjk)).op := Subsingleton.elim _ _
  exact (D.map_comp ((homOfLE hjk).op) ((homOfLE hij).op)).symm.trans
    (congrArg (fun q => D.map q) h)

private theorem later_projection_identity
    {K : Type u} [CommRing K] (S : Subalgebra ℤ K)
    {X : Scheme.{u}} (a : X ⟶ Spec (.of S))
    {i j k : CoefficientStage S} (hij : i ≤ j) (hjk : j ≤ k)
    (f : (stageScalarModel S a i).left ⟶ X)
    (h : stageScalarTransition S a hij ≫ f =
      stageScalarTransition S a hij ≫ pullback.snd _ a) :
    stageScalarTransition S a (hij.trans hjk) ≫ f = pullback.snd _ a := by
  let κi := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion i.property.2).toRingHom)
  let κj := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion j.property.2).toRingHom)
  let κk := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom)
  let tij : pullback κj a ⟶ pullback κi a := stageScalarTransition S a hij
  let tjk : pullback κk a ⟶ pullback κj a := stageScalarTransition S a hjk
  let tik : pullback κk a ⟶ pullback κi a := stageScalarTransition S a (hij.trans hjk)
  let fI : pullback κi a ⟶ X := f
  have hc : tjk ≫ tij = tik := transition_comp S a hij hjk
  have h0 : tij ≫ fI = tij ≫ pullback.snd κi a := h
  have hi : tij ≫ pullback.snd κi a = pullback.snd κj a :=
    stageScalarTransition_snd S a hij
  have hj : tjk ≫ pullback.snd κj a = pullback.snd κk a :=
    stageScalarTransition_snd S a hjk
  change tik ≫ fI = pullback.snd κk a
  calc
    tik ≫ fI = (tjk ≫ tij) ≫ fI := congrArg (fun q => q ≫ fI) hc.symm
    _ = tjk ≫ (tij ≫ fI) := Category.assoc _ _ _
    _ = tjk ≫ (tij ≫ pullback.snd κi a) := congrArg (fun q => tjk ≫ q) h0
    _ = tjk ≫ pullback.snd κj a := congrArg (fun q => tjk ≫ q) hi
    _ = pullback.snd κk a := hj

private theorem inverse_of_original_projection
    {K : Type u} [CommRing K] (S : Subalgebra ℤ K)
    {X Y : Scheme.{u}} (a : X ⟶ Spec (.of S)) (b : Y ⟶ Spec (.of S))
    {i j : CoefficientStage S} (hij : i ≤ j)
    (f : stageScalarModel S a i ⟶ stageScalarModel S b i)
    (g : stageScalarModel S b i ⟶ stageScalarModel S a i)
    (h : stageScalarTransition S a hij ≫ ((f ≫ g).left ≫ pullback.snd _ a) =
      pullback.snd _ a) :
    extendModelMorphism S a b hij f ≫ extendModelMorphism S b a hij g = 𝟙 _ := by
  let κi := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion i.property.2).toRingHom)
  let κj := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion j.property.2).toRingHom)
  let tA : pullback κj a ⟶ pullback κi a := stageScalarTransition S a hij
  let tB : pullback κj b ⟶ pullback κi b := stageScalarTransition S b hij
  let fI : pullback κi a ⟶ pullback κi b := f.left
  let gI : pullback κi b ⟶ pullback κi a := g.left
  let fJ : pullback κj a ⟶ pullback κj b := (extendModelMorphism S a b hij f).left
  let gJ : pullback κj b ⟶ pullback κj a := (extendModelMorphism S b a hij g).left
  have hf : fJ ≫ tB = tA ≫ fI := extendModelMorphism_transition S a b hij f
  have hg : gJ ≫ tA = tB ≫ gI := extendModelMorphism_transition S b a hij g
  have hs : tA ≫ pullback.snd κi a = pullback.snd κj a :=
    stageScalarTransition_snd S a hij
  have h0 : tA ≫ ((fI ≫ gI) ≫ pullback.snd κi a) = pullback.snd κj a := h
  have hw : (fJ ≫ gJ) ≫ pullback.fst κj a = pullback.fst κj a :=
    (extendModelMorphism S a b hij f ≫ extendModelMorphism S b a hij g).w
  have hc : (fJ ≫ gJ) ≫ tA = tA ≫ (fI ≫ gI) := by
    calc
      (fJ ≫ gJ) ≫ tA = fJ ≫ (gJ ≫ tA) := Category.assoc _ _ _
      _ = fJ ≫ (tB ≫ gI) := congrArg (fun q => fJ ≫ q) hg
      _ = (fJ ≫ tB) ≫ gI := (Category.assoc _ _ _).symm
      _ = (tA ≫ fI) ≫ gI := congrArg (fun q => q ≫ gI) hf
      _ = tA ≫ (fI ≫ gI) := Category.assoc _ _ _
  apply Over.OverMorphism.ext
  change fJ ≫ gJ = 𝟙 (pullback κj a)
  apply pullback.hom_ext
  · exact hw.trans (Category.id_comp _).symm
  · calc
      (fJ ≫ gJ) ≫ pullback.snd κj a = (fJ ≫ gJ) ≫ (tA ≫ pullback.snd κi a) :=
        congrArg (fun q => (fJ ≫ gJ) ≫ q) hs.symm
      _ = ((fJ ≫ gJ) ≫ tA) ≫ pullback.snd κi a := (Category.assoc _ _ _).symm
      _ = (tA ≫ (fI ≫ gI)) ≫ pullback.snd κi a :=
        congrArg (fun q => q ≫ pullback.snd κi a) hc
      _ = tA ≫ ((fI ≫ gI) ≫ pullback.snd κi a) := Category.assoc _ _ _
      _ = pullback.snd κj a := h0
      _ = 𝟙 _ ≫ pullback.snd κj a := (Category.id_comp _).symm

/-- A specified isomorphism is retained on coefficient pullbacks
of the same two finitely presented qcqs models. Both original maps are
retained. The two inverse equations are proved after coefficient enlargement. -/
theorem exists_model_iso
    {K : Type u} [CommRing K] (S : Subalgebra ℤ K) (hS : S.FG)
    {X Y : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    (a : X ⟶ Spec (.of S)) (b : Y ⟶ Spec (.of S))
    [LocallyOfFinitePresentation a] [LocallyOfFinitePresentation b]
    (E : genericScalarModel S a ≅ genericScalarModel S b) :
    ∃ (i : CoefficientStage S) (E₀ : stageScalarModel S a i ≅ stageScalarModel S b i),
      ((modelScalarCone S a).π.app (op i) ≫ E₀.hom.left =
        E.hom.left ≫ (modelScalarCone S b).π.app (op i)) ∧
      ((modelScalarCone S b).π.app (op i) ≫ E₀.inv.left =
        E.inv.left ≫ (modelScalarCone S a).π.app (op i)) := by
  obtain ⟨i, fi, hfi⟩ := exists_model_morphism S hS a b E.hom
  obtain ⟨j, gj, hgj⟩ := exists_model_morphism S hS b a E.inv
  obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
  let f := extendModelMorphism S a b hik fi
  let g := extendModelMorphism S b a hjk gj
  have hf : (modelScalarCone S a).π.app (op k) ≫ f.left =
      E.hom.left ≫ (modelScalarCone S b).π.app (op k) :=
    FrobeniusSplitting.extendModelMorphism_baseChange S a b hik fi E.hom hfi
  have hg : (modelScalarCone S b).π.app (op k) ≫ g.left =
      E.inv.left ≫ (modelScalarCone S a).π.app (op k) :=
    FrobeniusSplitting.extendModelMorphism_baseChange S b a hjk gj E.inv hgj
  obtain ⟨l, hkl, hx⟩ := exists_scalar_equality S hS a a k
    ((f ≫ g).left ≫ pullback.snd _ a) (pullback.snd _ a)
    (modelMap_base S a a k (f ≫ g)) rfl
    (generic_inverse_projection S a b k E f g hf hg)
  obtain ⟨n, hkn, hy⟩ := exists_scalar_equality S hS b b k
    ((g ≫ f).left ≫ pullback.snd _ b) (pullback.snd _ b)
    (modelMap_base S b b k (g ≫ f)) rfl
    (generic_inverse_projection S b a k E.symm g f hg hf)
  obtain ⟨m, hlm, hnm⟩ := exists_ge_ge l n
  have hkm : k ≤ m := hkl.trans hlm
  have hx' : stageScalarTransition S a hkm ≫
      ((f ≫ g).left ≫ pullback.snd _ a) = pullback.snd _ a :=
    later_projection_identity S a hkl hlm _ hx
  have hy' : stageScalarTransition S b hkm ≫
      ((g ≫ f).left ≫ pullback.snd _ b) = pullback.snd _ b :=
    later_projection_identity S b hkn hnm _ hy
  let E₀ : stageScalarModel S a m ≅ stageScalarModel S b m :=
    { hom := extendModelMorphism S a b hkm f
      inv := extendModelMorphism S b a hkm g
      hom_inv_id := inverse_of_original_projection S a b hkm f g hx'
      inv_hom_id := inverse_of_original_projection S b a hkm g f hy' }
  exact ⟨m, E₀, FrobeniusSplitting.extendModelMorphism_baseChange S a b hkm f E.hom hf,
    FrobeniusSplitting.extendModelMorphism_baseChange S b a hkm g E.inv hg⟩


end FrobeniusSplitting
