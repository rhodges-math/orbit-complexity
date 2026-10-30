import Batteries.Tactic.Lint
import OrbitComplexity.FrobeniusSplitting.Normality.Connectedness.RetainedIsomorphisms
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! # Retaining the chosen paired source and its endpoint

Two Cartesian comparisons from the same source give an isomorphism between
the scalar extensions of the two chosen models. Equations to their common
endpoint descend together with this isomorphism, on the original coefficient
pullbacks and above a prescribed coefficient stage.
-/

open FrobeniusSplitting

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace SchubertGeometry

universe u

/-- The specified endpoint after an arbitrary scalar base change, with the
coefficient projection as the structure morphism. -/
def chosenScalarArrow {B T : Scheme.{u}} (κ : T ⟶ B)
    {C D : Over B} (e : C ⟶ D) :
    Over.mk (pullback.fst κ C.hom) ⟶ Over.mk (pullback.fst κ D.hom) :=
  Over.homMk
    (pullback.lift (pullback.fst κ C.hom) (pullback.snd κ C.hom ≫ e.left)
      (by rw [Category.assoc, e.w]; exact pullback.condition))
    (pullback.lift_fst _ _ _)

/-- Scalar extension of an endpoint retains its projection to the original
endpoint model. -/
theorem chosenScalarArrow_snd {B T : Scheme.{u}} (κ : T ⟶ B)
    {C D : Over B} (e : C ⟶ D) :
    (chosenScalarArrow κ e).left ≫ pullback.snd κ D.hom =
      pullback.snd κ C.hom ≫ e.left := by
  change pullback.lift _ _ _ ≫ pullback.snd κ D.hom = _
  exact pullback.lift_snd _ _ _

/-- Scalar extension of an endpoint is a Cartesian square with the two
projections to its original source and target. -/
theorem chosenScalarArrow_cartesian {B T : Scheme.{u}} (κ : T ⟶ B)
    {C D : Over B} (e : C ⟶ D) :
    IsPullback (chosenScalarArrow κ e).left (pullback.snd κ C.hom)
      (pullback.snd κ D.hom) e.left := by
  have he : (chosenScalarArrow κ e).left ≫ pullback.fst κ D.hom =
      pullback.fst κ C.hom := (chosenScalarArrow κ e).w
  have h : IsPullback ((chosenScalarArrow κ e).left ≫ pullback.fst κ D.hom)
      (pullback.snd κ C.hom) κ (e.left ≫ D.hom) := by
    rw [he, e.w]
    exact IsPullback.of_hasPullback κ C.hom
  exact h.of_right (chosenScalarArrow_snd κ e) (IsPullback.of_hasPullback κ D.hom)

/-- The two prescribed Cartesian comparisons from a common source identify
the scalar pullbacks of the same two models, over the scalar base. -/
def chosenPairIso {B T N : Scheme.{u}} (κ : T ⟶ B)
    (C P : Over B) (n : N ⟶ T) (qC : N ⟶ C.left) (qP : N ⟶ P.left)
    (hC : IsPullback qC n C.hom κ) (hP : IsPullback qP n P.hom κ) :
    Over.mk (pullback.fst κ C.hom) ≅ Over.mk (pullback.fst κ P.hom) :=
  hC.flip.isoOverPullback.symm ≪≫ hP.flip.isoOverPullback

/-- The isomorphism given by the common source retains its specified endpoint
when both original endpoint equations have the same right-hand side. -/
theorem chosenPairIso_endpoint {B T N Q : Scheme.{u}} (κ : T ⟶ B)
    (C P D : Over B) (n : N ⟶ T) (qC : N ⟶ C.left) (qP : N ⟶ P.left)
    (hC : IsPullback qC n C.hom κ) (hP : IsPullback qP n P.hom κ)
    (eC : C ⟶ D) (eP : P ⟶ D) (eN : N ⟶ Q) (qD : Q ⟶ D.left)
    (heC : qC ≫ eC.left = eN ≫ qD) (heP : qP ≫ eP.left = eN ≫ qD) :
    (chosenPairIso κ C P n qC qP hC hP).hom ≫ chosenScalarArrow κ eP =
      chosenScalarArrow κ eC := by
  let EC : Over.mk n ≅ Over.mk (pullback.fst κ C.hom) :=
    hC.flip.isoOverPullback
  let EP : Over.mk n ≅ Over.mk (pullback.fst κ P.hom) :=
    hP.flip.isoOverPullback
  have hc : EC.hom.left ≫ pullback.snd κ C.hom = qC :=
    hC.flip.isoOverPullback_hom_left_comp_snd
  have hp : EP.hom.left ≫ pullback.snd κ P.hom = qP :=
    hP.flip.isoOverPullback_hom_left_comp_snd
  have hnative : EP.hom ≫ chosenScalarArrow κ eP =
      EC.hom ≫ chosenScalarArrow κ eC := by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · exact (EP.hom ≫ chosenScalarArrow κ eP).w.trans
        (EC.hom ≫ chosenScalarArrow κ eC).w.symm
    · change (EP.hom.left ≫ (chosenScalarArrow κ eP).left) ≫
          pullback.snd κ D.hom =
        (EC.hom.left ≫ (chosenScalarArrow κ eC).left) ≫ pullback.snd κ D.hom
      calc
        (EP.hom.left ≫ (chosenScalarArrow κ eP).left) ≫ pullback.snd κ D.hom =
            EP.hom.left ≫ (pullback.snd κ P.hom ≫ eP.left) := by
          rw [Category.assoc, chosenScalarArrow_snd]
        _ = (EP.hom.left ≫ pullback.snd κ P.hom) ≫ eP.left :=
          (Category.assoc _ _ _).symm
        _ = qP ≫ eP.left := congrArg (fun k => k ≫ eP.left) hp
        _ = eN ≫ qD := heP
        _ = qC ≫ eC.left := heC.symm
        _ = (EC.hom.left ≫ pullback.snd κ C.hom) ≫ eC.left :=
          congrArg (fun k => k ≫ eC.left) hc.symm
        _ = EC.hom.left ≫ (pullback.snd κ C.hom ≫ eC.left) :=
          Category.assoc _ _ _
        _ = (EC.hom.left ≫ (chosenScalarArrow κ eC).left) ≫
            pullback.snd κ D.hom := by
          rw [Category.assoc, chosenScalarArrow_snd]
  change (EC.inv ≫ EP.hom) ≫ chosenScalarArrow κ eP = chosenScalarArrow κ eC
  calc
    (EC.inv ≫ EP.hom) ≫ chosenScalarArrow κ eP =
        EC.inv ≫ (EP.hom ≫ chosenScalarArrow κ eP) := Category.assoc _ _ _
    _ = EC.inv ≫ (EC.hom ≫ chosenScalarArrow κ eC) :=
      congrArg (fun k => EC.inv ≫ k) hnative
    _ = chosenScalarArrow κ eC := by
      rw [← Category.assoc, EC.inv_hom_id, Category.id_comp]

private theorem chosenArrow_projection {B T : Scheme.{u}} (κ : T ⟶ B)
    {C P D : Over B} (eC : C ⟶ D) (eP : P ⟶ D)
    (E : Over.mk (pullback.fst κ C.hom) ≅ Over.mk (pullback.fst κ P.hom))
    (hE : E.hom ≫ chosenScalarArrow κ eP = chosenScalarArrow κ eC) :
    E.hom.left ≫ (pullback.snd κ P.hom ≫ eP.left) =
      pullback.snd κ C.hom ≫ eC.left := by
  have h := congrArg
    (fun f : Over.mk (pullback.fst κ C.hom) ⟶
      Over.mk (pullback.fst κ D.hom) => f.left ≫ pullback.snd κ D.hom) hE
  change (E.hom.left ≫ (chosenScalarArrow κ eP).left) ≫
      pullback.snd κ D.hom =
    (chosenScalarArrow κ eC).left ≫ pullback.snd κ D.hom at h
  simp only [Category.assoc, chosenScalarArrow_snd] at h
  exact h

private theorem chosenArrow_base {B T : Scheme.{u}} (κ : T ⟶ B)
    {C P D : Over B}
    (f : Over.mk (pullback.fst κ C.hom) ⟶ Over.mk (pullback.fst κ P.hom))
    (eP : P ⟶ D) :
    (f.left ≫ (pullback.snd κ P.hom ≫ eP.left)) ≫ D.hom =
      pullback.snd κ C.hom ≫ C.hom := by
  calc
    (f.left ≫ (pullback.snd κ P.hom ≫ eP.left)) ≫ D.hom =
        f.left ≫ (pullback.snd κ P.hom ≫ P.hom) := by
      simp only [Category.assoc, eP.w]
    _ = f.left ≫ (pullback.fst κ P.hom ≫ κ) :=
      congrArg (fun k => f.left ≫ k) (pullback.condition (f := κ) (g := P.hom)).symm
    _ = (f.left ≫ pullback.fst κ P.hom) ≫ κ := (Category.assoc _ _ _).symm
    _ = pullback.fst κ C.hom ≫ κ := congrArg (fun k => k ≫ κ) f.w
    _ = pullback.snd κ C.hom ≫ C.hom := pullback.condition

private theorem chosenScalarLeg_snd {K : Type u} [CommRing K]
    (S : Subalgebra ℤ K) {X : Scheme.{u}} (a : X ⟶ Spec (.of S))
    (i : CoefficientStage S) :
    (modelScalarCone S a).π.app (op i) ≫ pullback.snd _ a =
      pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap S K))) a := by
  change pullback.lift _ _ _ ≫ pullback.snd _ a = _
  exact pullback.lift_snd _ _ _

private theorem chosenEndpoint_later {K : Type u} [CommRing K]
    (S : Subalgebra ℤ K) (C P D : Over (Spec (.of S)))
    (eC : C ⟶ D) (eP : P ⟶ D)
    {i j : CoefficientStage S} (hij : i ≤ j)
    (E : stageScalarModel S C.hom i ≅ stageScalarModel S P.hom i)
    (h : stageScalarTransition S C.hom hij ≫
          (E.hom.left ≫ (pullback.snd _ P.hom ≫ eP.left)) =
        stageScalarTransition S C.hom hij ≫
          (pullback.snd _ C.hom ≫ eC.left)) :
    (retainedIsoExtend S C.hom P.hom hij E).hom ≫
        chosenScalarArrow
          (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion j.property.2).toRingHom)) eP =
      chosenScalarArrow
        (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion j.property.2).toRingHom)) eC := by
  let κi := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion i.property.2).toRingHom)
  let κj := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion j.property.2).toRingHom)
  let tC : pullback κj C.hom ⟶ pullback κi C.hom :=
    stageScalarTransition S C.hom hij
  let tP : pullback κj P.hom ⟶ pullback κi P.hom :=
    stageScalarTransition S P.hom hij
  let fi : pullback κi C.hom ⟶ pullback κi P.hom := E.hom.left
  let F : stageScalarModel S C.hom j ≅ stageScalarModel S P.hom j :=
    retainedIsoExtend S C.hom P.hom hij E
  let fj : pullback κj C.hom ⟶ pullback κj P.hom := F.hom.left
  have ht : fj ≫ tP = tC ≫ fi :=
    extendModelMorphism_transition S C.hom P.hom hij E.hom
  have hsP : tP ≫ pullback.snd κi P.hom = pullback.snd κj P.hom :=
    stageScalarTransition_snd S P.hom hij
  have hsC : tC ≫ pullback.snd κi C.hom = pullback.snd κj C.hom :=
    stageScalarTransition_snd S C.hom hij
  have heq : tC ≫ (fi ≫ (pullback.snd κi P.hom ≫ eP.left)) =
      tC ≫ (pullback.snd κi C.hom ≫ eC.left) := h
  change F.hom ≫ chosenScalarArrow κj eP = chosenScalarArrow κj eC
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · exact (F.hom ≫ chosenScalarArrow κj eP).w.trans (chosenScalarArrow κj eC).w.symm
  · change (fj ≫ (chosenScalarArrow κj eP).left) ≫ pullback.snd κj D.hom =
      (chosenScalarArrow κj eC).left ≫ pullback.snd κj D.hom
    calc
      (fj ≫ (chosenScalarArrow κj eP).left) ≫ pullback.snd κj D.hom =
          fj ≫ (pullback.snd κj P.hom ≫ eP.left) := by
        rw [Category.assoc, chosenScalarArrow_snd]
      _ = fj ≫ ((tP ≫ pullback.snd κi P.hom) ≫ eP.left) :=
        congrArg (fun k => fj ≫ (k ≫ eP.left)) hsP.symm
      _ = (fj ≫ tP) ≫ (pullback.snd κi P.hom ≫ eP.left) := by
        simp only [Category.assoc]
      _ = (tC ≫ fi) ≫ (pullback.snd κi P.hom ≫ eP.left) :=
        congrArg (fun k => k ≫ (pullback.snd κi P.hom ≫ eP.left)) ht
      _ = tC ≫ (fi ≫ (pullback.snd κi P.hom ≫ eP.left)) := Category.assoc _ _ _
      _ = tC ≫ (pullback.snd κi C.hom ≫ eC.left) := heq
      _ = (tC ≫ pullback.snd κi C.hom) ≫ eC.left := (Category.assoc _ _ _).symm
      _ = pullback.snd κj C.hom ≫ eC.left := congrArg (fun k => k ≫ eC.left) hsC
      _ = (chosenScalarArrow κj eC).left ≫ pullback.snd κj D.hom :=
        (chosenScalarArrow_snd κj eC).symm

private theorem chosenEndpointCone
    {T : Type*} [Category T] {A B A₀ B₀ X Y Z : T}
    (qA : A ⟶ A₀) (qB : B ⟶ B₀) (f : A ⟶ B) (f₀ : A₀ ⟶ B₀)
    (pA : A ⟶ X) (pA₀ : A₀ ⟶ X) (pB : B ⟶ Y) (pB₀ : B₀ ⟶ Y)
    (eA : X ⟶ Z) (eB : Y ⟶ Z)
    (hf : qA ≫ f₀ = f ≫ qB) (hA : qA ≫ pA₀ = pA) (hB : qB ≫ pB₀ = pB)
    (he : f ≫ (pB ≫ eB) = pA ≫ eA) :
    qA ≫ (f₀ ≫ (pB₀ ≫ eB)) = qA ≫ (pA₀ ≫ eA) := by
  calc
    qA ≫ (f₀ ≫ (pB₀ ≫ eB)) = (qA ≫ f₀) ≫ pB₀ ≫ eB := by
      simp only [Category.assoc]
    _ = (f ≫ qB) ≫ pB₀ ≫ eB :=
      congrArg (fun k : A ⟶ B₀ => k ≫ pB₀ ≫ eB) hf
    _ = f ≫ ((qB ≫ pB₀) ≫ eB) := by simp only [Category.assoc]
    _ = f ≫ (pB ≫ eB) := congrArg (fun k : B ⟶ Y => f ≫ (k ≫ eB)) hB
    _ = pA ≫ eA := he
    _ = (qA ≫ pA₀) ≫ eA := congrArg (fun k : A ⟶ X => k ≫ eA) hA.symm
    _ = qA ≫ (pA₀ ≫ eA) := Category.assoc _ _ _

/-- An endpoint-preserving generic isomorphism descends above a prescribed
stage on the same two models, retaining both original coefficient projections
and the equality of the specified scalar endpoint maps. -/
theorem exists_chosen_endpoint_iso {K : Type u} [CommRing K]
    (S : Subalgebra ℤ K) (hS : S.FG) (C P D : Over (Spec (.of S)))
    [CompactSpace C.left] [QuasiSeparatedSpace C.left]
    [CompactSpace P.left] [QuasiSeparatedSpace P.left]
    [LocallyOfFinitePresentation C.hom] [LocallyOfFinitePresentation P.hom]
    [LocallyOfFiniteType D.hom] (eC : C ⟶ D) (eP : P ⟶ D)
    (E : genericScalarModel S C.hom ≅ genericScalarModel S P.hom)
    (hE : E.hom ≫ chosenScalarArrow
        (Spec.map (CommRingCat.ofHom (algebraMap S K))) eP =
      chosenScalarArrow (Spec.map (CommRingCat.ofHom (algebraMap S K))) eC)
    (start : CoefficientStage S) :
    ∃ (j : CoefficientStage S) (_ : start ≤ j)
      (E₀ : stageScalarModel S C.hom j ≅ stageScalarModel S P.hom j),
      ((modelScalarCone S C.hom).π.app (op j) ≫ E₀.hom.left =
        E.hom.left ≫ (modelScalarCone S P.hom).π.app (op j)) ∧
      ((modelScalarCone S P.hom).π.app (op j) ≫ E₀.inv.left =
        E.inv.left ≫ (modelScalarCone S C.hom).π.app (op j)) ∧
      E₀.hom ≫ chosenScalarArrow
          (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion j.property.2).toRingHom)) eP =
        chosenScalarArrow
          (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion j.property.2).toRingHom)) eC := by
  obtain ⟨i, Ei, hhom, hinv⟩ := exists_model_iso S hS C.hom P.hom E
  obtain ⟨k, hstart, hik⟩ := exists_ge_ge start i
  let Ek : stageScalarModel S C.hom k ≅ stageScalarModel S P.hom k :=
    retainedIsoExtend S C.hom P.hom hik Ei
  have hhomk : (modelScalarCone S C.hom).π.app (op k) ≫ Ek.hom.left =
      E.hom.left ≫ (modelScalarCone S P.hom).π.app (op k) :=
    extendModelMorphism_baseChange S C.hom P.hom hik Ei.hom E.hom hhom
  have hinvk : (modelScalarCone S P.hom).π.app (op k) ≫ Ek.inv.left =
      E.inv.left ≫ (modelScalarCone S C.hom).π.app (op k) :=
    extendModelMorphism_baseChange S P.hom C.hom hik Ei.inv E.inv hinv
  let κ := Spec.map (CommRingCat.ofHom (algebraMap S K))
  let κk := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom)
  let qC : pullback κ C.hom ⟶ pullback κk C.hom :=
    (modelScalarCone S C.hom).π.app (op k)
  let qP : pullback κ P.hom ⟶ pullback κk P.hom :=
    (modelScalarCone S P.hom).π.app (op k)
  let f : pullback κk C.hom ⟶ D.left :=
    Ek.hom.left ≫ (pullback.snd κk P.hom ≫ eP.left)
  let g : pullback κk C.hom ⟶ D.left := pullback.snd κk C.hom ≫ eC.left
  have hf : f ≫ D.hom = (modelScalarBase S C.hom).app (op k) :=
    chosenArrow_base κk Ek.hom eP
  have hg : g ≫ D.hom = (modelScalarBase S C.hom).app (op k) := by
    change (pullback.snd κk C.hom ≫ eC.left) ≫ D.hom =
      pullback.snd κk C.hom ≫ C.hom
    rw [Category.assoc, eC.w]
  have hprojection : E.hom.left ≫ (pullback.snd κ P.hom ≫ eP.left) =
      pullback.snd κ C.hom ≫ eC.left := chosenArrow_projection κ eC eP E hE
  have hqC : qC ≫ pullback.snd κk C.hom = pullback.snd κ C.hom :=
    chosenScalarLeg_snd S C.hom k
  have hqP : qP ≫ pullback.snd κk P.hom = pullback.snd κ P.hom :=
    chosenScalarLeg_snd S P.hom k
  have hfg : qC ≫ f = qC ≫ g := by
    exact chosenEndpointCone qC qP E.hom.left Ek.hom.left
      (pullback.snd κ C.hom) (pullback.snd κk C.hom)
      (pullback.snd κ P.hom) (pullback.snd κk P.hom) eC.left eP.left
      hhomk hqC hqP hprojection
  obtain ⟨j, hkj, heq⟩ := exists_scalar_equality S hS C.hom D.hom k f g hf hg hfg
  let E₀ : stageScalarModel S C.hom j ≅ stageScalarModel S P.hom j :=
    retainedIsoExtend S C.hom P.hom hkj Ek
  refine ⟨j, hstart.trans hkj, E₀, ?_, ?_, ?_⟩
  · exact extendModelMorphism_baseChange S C.hom P.hom hkj Ek.hom E.hom hhomk
  · exact extendModelMorphism_baseChange S P.hom C.hom hkj Ek.inv E.inv hinvk
  · exact chosenEndpoint_later S C P D eC eP hkj Ek heq

/-- Specified Cartesian comparisons and original endpoint equations retain a
single endpoint-preserving isomorphism on coefficient pullbacks of the chosen
source and the raw paired source, above the requested starting stage. -/
theorem exists_chosen_paired_retention {K : Type u} [CommRing K]
    (S : Subalgebra ℤ K) (hS : S.FG) (C P D : Over (Spec (.of S)))
    [CompactSpace C.left] [QuasiSeparatedSpace C.left]
    [CompactSpace P.left] [QuasiSeparatedSpace P.left]
    [LocallyOfFinitePresentation C.hom] [LocallyOfFinitePresentation P.hom]
    [LocallyOfFiniteType D.hom]
    {N Q : Scheme.{u}} (n : N ⟶ Spec (.of K))
    (qC : N ⟶ C.left) (qP : N ⟶ P.left)
    (hC : IsPullback qC n C.hom (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hP : IsPullback qP n P.hom (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (eC : C ⟶ D) (eP : P ⟶ D) (eN : N ⟶ Q) (qD : Q ⟶ D.left)
    (heC : qC ≫ eC.left = eN ≫ qD) (heP : qP ≫ eP.left = eN ≫ qD)
    (start : CoefficientStage S) :
    let E := chosenPairIso (Spec.map (CommRingCat.ofHom (algebraMap S K)))
      C P n qC qP hC hP
    ∃ (j : CoefficientStage S) (_ : start ≤ j)
      (E₀ : stageScalarModel S C.hom j ≅ stageScalarModel S P.hom j),
      ((modelScalarCone S C.hom).π.app (op j) ≫ E₀.hom.left =
        E.hom.left ≫ (modelScalarCone S P.hom).π.app (op j)) ∧
      ((modelScalarCone S P.hom).π.app (op j) ≫ E₀.inv.left =
        E.inv.left ≫ (modelScalarCone S C.hom).π.app (op j)) ∧
      E₀.hom ≫ chosenScalarArrow
          (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion j.property.2).toRingHom)) eP =
        chosenScalarArrow
          (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion j.property.2).toRingHom)) eC := by
  dsimp only
  exact exists_chosen_endpoint_iso S hS C P D eC eP
    (chosenPairIso (Spec.map (CommRingCat.ofHom (algebraMap S K))) C P n qC qP hC hP)
    (chosenPairIso_endpoint (Spec.map (CommRingCat.ofHom (algebraMap S K)))
      C P D n qC qP hC hP eC eP eN qD heC heP) start

-- GAP: C6-STAGE. Supply the specified finitely presented qcqs raw arithmetic
-- paired model P, its specified endpoint eP into the same chosen target D,
-- the Cartesian comparison hP from the same original source as hC, and the
-- equation qP ≫ eP.left = eN ≫ qD. The theorem above retains those data;
-- it does not construct the raw paired diagram from the original word models.

end SchubertGeometry
