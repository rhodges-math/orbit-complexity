import OrbitComplexity.SchubertGeometry.Connectedness.ProjectiveCurveRetention
import OrbitComplexity.SchubertGeometry.Connectedness.ScalarArrowSquares
import Batteries.Tactic.Lint
import OrbitComplexity.SchubertGeometry.BSDH.Construction
import OrbitComplexity.SchubertGeometry.Parabolics.SimpleIncidence
import OrbitComplexity.SchubertGeometry.Connectedness.ChosenPairedRetention
import OrbitComplexity.FrobeniusSplitting.Normality.Products.PairedScalarComparison
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

set_option autoImplicit false

/-! # Incidence models for appending a simple reflection

The prefix endpoint and the simple partial-flag projection determine the
incidence model. Its two projections and the appended endpoint are preserved
when its comparison isomorphism is extended to a coefficient stage.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReductiveGroups
open FrobeniusSplitting Opposite

namespace SchubertGeometry

universe u

private theorem bind_witness {A : Type*} {P : A → Prop} {Q : Prop}
    (h : ∃ a, P a) (next : ∀ a, P a → Q) : Q := by
  obtain ⟨a, ha⟩ := h
  exact next a ha

private theorem incidence_base {T : Type*} [Category T] [HasPullbacks T]
    {A F Q B : T} (a : A ⟶ F) (π : F ⟶ Q)
    (bA : A ⟶ B) (bF : F ⟶ B) (bQ : Q ⟶ B)
    (ha : a ≫ bF = bA) (hπ : π ≫ bQ = bF) :
    pullback.snd (a ≫ π) π ≫ bF = pullback.fst (a ≫ π) π ≫ bA := by
  calc
    pullback.snd (a ≫ π) π ≫ bF =
        pullback.snd (a ≫ π) π ≫ (π ≫ bQ) :=
      congrArg (fun k => pullback.snd (a ≫ π) π ≫ k) hπ.symm
    _ = (pullback.snd (a ≫ π) π ≫ π) ≫ bQ := (Category.assoc _ _ _).symm
    _ = (pullback.fst (a ≫ π) π ≫ (a ≫ π)) ≫ bQ :=
      congrArg (fun k => k ≫ bQ) (pullback.condition (f := a ≫ π) (g := π)).symm
    _ = pullback.fst (a ≫ π) π ≫ bA := by
      simp only [Category.assoc, hπ, ha]

/-- The incidence model of an endpoint and a simple partial-flag projection. -/
def appendIncidenceModel {B : Scheme.{u}} {A F Q : Over B}
    (a : A ⟶ F) (π : F ⟶ Q) : Over B :=
  Over.mk (pullback.fst (a.left ≫ π.left) π.left ≫ A.hom)

/-- The prefix projection of the incidence model. -/
def appendIncidenceFst {B : Scheme.{u}} {A F Q : Over B}
    (a : A ⟶ F) (π : F ⟶ Q) : appendIncidenceModel a π ⟶ A :=
  Over.homMk (pullback.fst (a.left ≫ π.left) π.left) rfl

/-- The endpoint projection of the incidence model. -/
def appendIncidenceSnd {B : Scheme.{u}} {A F Q : Over B}
    (a : A ⟶ F) (π : F ⟶ Q) : appendIncidenceModel a π ⟶ F :=
  Over.homMk (pullback.snd (a.left ≫ π.left) π.left)
    (incidence_base a.left π.left A.hom F.hom Q.hom a.w π.w)

private theorem append_square_of_incidence {T : Type*} [Category T] [HasPullbacks T]
    {A F Q J N : T} (a : A ⟶ F) (π : F ⟶ Q)
    (p e : J ⟶ F) (hJ : IsPullback p e π π)
    (E : N ≅ pullback a p) (d : N ⟶ A) (n : N ⟶ F)
    (hd : E.hom ≫ pullback.fst a p = d)
    (hn : E.hom ≫ (pullback.snd a p ≫ e) = n) :
    IsPullback d n (a ≫ π) π :=
  curveModel_pullback
    (((IsPullback.of_hasPullback a p).flip.paste_horiz hJ.flip).flip)
    E d n hd hn

/-- Appending a simple reflection is the complete-flag incidence pullback. -/
theorem bsdhAppend_cartesian
    {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K) (word : List G.rootBase.support)
    (i : G.rootBase.support) :
    IsPullback (bsdhAppendFst G word i) (bsdhMap G (word ++ [i]))
      (bsdhMap G word ≫ (partialFlagMorphism G {i}).left)
      (partialFlagMorphism G {i}).left := by
  apply bind_witness (simpleSchubert_incidence G i)
  intro e he
  have hJ := curveModel_pullback
    (IsPullback.of_hasPullback (partialFlagMorphism G {i}).left
      (partialFlagMorphism G {i}).left)
    e _ _ he.1 he.2
  exact append_square_of_incidence (bsdhMap G word) (partialFlagMorphism G {i}).left
    _ _ hJ ((Over.forget (flagVariety G).scheme).mapIso (bsdhAppendIso G word i))
    (bsdhAppendFst G word i) (bsdhMap G (word ++ [i])) rfl
    (bsdhAppendIso_endpoint G word i)

private theorem incidence_properties {R : Type u} [CommRing R] [IsNoetherianRing R]
    {A F Q : Over (Spec (.of R))}
    [CompactSpace A.left] [CompactSpace F.left]
    [LocallyOfFinitePresentation A.hom] [LocallyOfFinitePresentation F.hom]
    [LocallyOfFinitePresentation Q.hom] (a : A ⟶ F) (π : F ⟶ Q) :
    LocallyOfFinitePresentation (appendIncidenceModel a π).hom ∧
      CompactSpace (appendIncidenceModel a π).left ∧
      QuasiSeparatedSpace (appendIncidenceModel a π).left := by
  let : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
  let : IsLocallyNoetherian F.left := LocallyOfFiniteType.isLocallyNoetherian F.hom
  let : IsLocallyNoetherian Q.left := LocallyOfFiniteType.isLocallyNoetherian Q.hom
  let : AlgebraicGeometry.IsNoetherian F.left := AlgebraicGeometry.IsNoetherian.mk
  let : LocallyOfFiniteType (π.left ≫ Q.hom) := π.w.symm ▸ inferInstanceAs
    (LocallyOfFiniteType F.hom)
  let : LocallyOfFiniteType π.left := locallyOfFiniteType_of_comp π.left Q.hom
  let : LocallyOfFinitePresentation π.left := inferInstance
  let : QuasiCompact π.left := inferInstance
  have hQC : QuasiCompact (pullback.fst (a.left ≫ π.left) π.left) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback (a.left ≫ π.left) π.left).flip
      (inferInstanceAs (QuasiCompact π.left))
  let : LocallyOfFinitePresentation (appendIncidenceModel a π).hom := inferInstanceAs
    (LocallyOfFinitePresentation (pullback.fst (a.left ≫ π.left) π.left ≫ A.hom))
  let : CompactSpace (appendIncidenceModel a π).left :=
    @QuasiCompact.compactSpace_of_compactSpace
      (pullback (a.left ≫ π.left) π.left) A.left
      (pullback.fst (a.left ≫ π.left) π.left) hQC
      (inferInstanceAs (CompactSpace A.left))
  let : IsLocallyNoetherian (appendIncidenceModel a π).left :=
    LocallyOfFiniteType.isLocallyNoetherian (appendIncidenceModel a π).hom
  exact ⟨inferInstance, inferInstance, inferInstance⟩

private theorem scalar_projection_eq {B T Z : Scheme.{u}} (κ : T ⟶ B)
    {P A : Over B} (f : P ⟶ A)
    (E : Z ≅ pullback κ P.hom) (t : Z ⟶ T) (q : Z ⟶ P.left)
    (ht : E.hom ≫ pullback.fst κ P.hom = t)
    (hq : E.hom ≫ pullback.snd κ P.hom = q)
    (d : Z ⟶ pullback κ A.hom)
    (hd : d ≫ pullback.fst κ A.hom = t)
    (hdo : d ≫ pullback.snd κ A.hom = q ≫ f.left) :
    E.hom ≫ (chosenScalarArrow κ f).left = d := by
  apply pullback.hom_ext
  · calc
      (E.hom ≫ (chosenScalarArrow κ f).left) ≫ pullback.fst κ A.hom =
          E.hom ≫ pullback.fst κ P.hom :=
        (Category.assoc _ _ _).trans
          (congrArg (fun k => E.hom ≫ k) (chosenScalarArrow κ f).w)
      _ = t := ht
      _ = d ≫ pullback.fst κ A.hom := hd.symm
  · calc
      (E.hom ≫ (chosenScalarArrow κ f).left) ≫ pullback.snd κ A.hom =
          E.hom ≫ (pullback.snd κ P.hom ≫ f.left) :=
        (Category.assoc _ _ _).trans
          (congrArg (fun k => E.hom ≫ k) (chosenScalarArrow_snd κ f))
      _ = q ≫ f.left := (Category.assoc _ _ _).symm.trans
        (congrArg (fun k => k ≫ f.left) hq)
      _ = d ≫ pullback.snd κ A.hom := hdo.symm

private theorem scalar_incidence_cartesian {B T : Scheme.{u}} (κ : T ⟶ B)
    {A F Q : Over B} (a : A ⟶ F) (π : F ⟶ Q) :
    IsPullback (chosenScalarArrow κ (appendIncidenceFst a π)).left
      (chosenScalarArrow κ (appendIncidenceSnd a π)).left
      ((chosenScalarArrow κ a).left ≫ (chosenScalarArrow κ π).left)
      (chosenScalarArrow κ π).left := by
  let Aₜ : Over T := Over.mk (pullback.fst κ A.hom)
  let Fₜ : Over T := Over.mk (pullback.fst κ F.hom)
  let Qₜ : Over T := Over.mk (pullback.fst κ Q.hom)
  let aₜ : Aₜ ⟶ Fₜ := chosenScalarArrow κ a
  let πₜ : Fₜ ⟶ Qₜ := chosenScalarArrow κ π
  have hcomp : (aₜ.left ≫ πₜ.left) ≫ pullback.snd κ Q.hom =
      pullback.snd κ A.hom ≫ (a.left ≫ π.left) :=
    scalarArrow_composite_square aₜ.left πₜ.left a.left π.left
      (pullback.snd κ A.hom) (pullback.snd κ F.hom) (pullback.snd κ Q.hom)
      (chosenScalarArrow_snd κ a) (chosenScalarArrow_snd κ π)
  have hbcomp : (aₜ.left ≫ πₜ.left) ≫ Qₜ.hom = Aₜ.hom := by
    rw [Category.assoc, πₜ.w, aₜ.w]
  have hbasecomp : (a.left ≫ π.left) ≫ Q.hom = A.hom := by
    rw [Category.assoc, π.w, a.w]
  have h := paired_model_scalar_pullback κ Aₜ.hom Fₜ.hom Qₜ.hom A.hom F.hom Q.hom
    (aₜ.left ≫ πₜ.left) πₜ.left (a.left ≫ π.left) π.left
    hbcomp πₜ.w hbasecomp π.w
    (pullback.snd κ A.hom) (pullback.snd κ F.hom) (pullback.snd κ Q.hom)
    (IsPullback.of_hasPullback κ A.hom).flip
    (IsPullback.of_hasPullback κ F.hom).flip
    (IsPullback.of_hasPullback κ Q.hom).flip hcomp (chosenScalarArrow_snd κ π)
  let E := h.1.flip.isoPullback
  have hfst : E.hom ≫ (chosenScalarArrow κ (appendIncidenceFst a π)).left =
      pullback.fst (aₜ.left ≫ πₜ.left) πₜ.left := by
    apply scalar_projection_eq κ (appendIncidenceFst a π) E _ _
      h.1.flip.isoPullback_hom_fst h.1.flip.isoPullback_hom_snd
    · rfl
    · exact h.2.1.symm
  have hsnd : E.hom ≫ (chosenScalarArrow κ (appendIncidenceSnd a π)).left =
      pullback.snd (aₜ.left ≫ πₜ.left) πₜ.left := by
    apply scalar_projection_eq κ (appendIncidenceSnd a π) E _ _
      h.1.flip.isoPullback_hom_fst h.1.flip.isoPullback_hom_snd
    · exact incidence_base aₜ.left πₜ.left Aₜ.hom Fₜ.hom Qₜ.hom aₜ.w πₜ.w
    · exact h.2.2.symm
  exact (IsPullback.of_hasPullback (aₜ.left ≫ πₜ.left) πₜ.left).of_iso E
    (Iso.refl _) (Iso.refl _) (Iso.refl _)
    ((Category.comp_id _).trans hfst.symm) ((Category.comp_id _).trans hsnd.symm)
    ((Category.comp_id _).trans (Category.id_comp _).symm)
    ((Category.comp_id _).trans (Category.id_comp _).symm)

private theorem incidence_coefficient_square
    {B T N X F Q : Scheme.{u}} (κ : T ⟶ B)
    (bN : N ⟶ T) (bX : X ⟶ T) (bF : F ⟶ T) (bQ : Q ⟶ T)
    (f : X ⟶ F) (π : F ⟶ Q) (u : N ⟶ X) (v : N ⟶ F)
    (hf : f ≫ bF = bX) (hπ : π ≫ bQ = bF) (hu : u ≫ bX = bN)
    (hN : IsPullback u v (f ≫ π) π)
    {X₀ F₀ Q₀ : Over B} (f₀ : X₀ ⟶ F₀) (π₀ : F₀ ⟶ Q₀)
    (qX : X ⟶ X₀.left) (qF : F ⟶ F₀.left) (qQ : Q ⟶ Q₀.left)
    (hX : IsPullback qX bX X₀.hom κ) (hF : IsPullback qF bF F₀.hom κ)
    (hQ : IsPullback qQ bQ Q₀.hom κ)
    (hfx : f ≫ qF = qX ≫ f₀.left) (hπq : π ≫ qQ = qF ≫ π₀.left) :
    ∃ qP : N ⟶ (appendIncidenceModel f₀ π₀).left,
      IsPullback qP bN (appendIncidenceModel f₀ π₀).hom κ ∧
      qP ≫ (appendIncidenceFst f₀ π₀).left = u ≫ qX ∧
      qP ≫ (appendIncidenceSnd f₀ π₀).left = v ≫ qF := by
  have hfb : (f ≫ π) ≫ bQ = bX := by
    rw [Category.assoc, hπ, hf]
  have hf₀b : (f₀.left ≫ π₀.left) ≫ Q₀.hom = X₀.hom := by
    rw [Category.assoc, π₀.w, f₀.w]
  have hcomp := scalarArrow_composite_square f π f₀.left π₀.left qX qF qQ hfx hπq
  have h := paired_model_scalar_pullback κ bX bF bQ X₀.hom F₀.hom Q₀.hom
    (f ≫ π) π (f₀.left ≫ π₀.left) π₀.left hfb hπ hf₀b π₀.w
    qX qF qQ hX hF hQ hcomp hπq
  let qR := pullback.map (f ≫ π) π (f₀.left ≫ π₀.left) π₀.left
    qX qF qQ hcomp hπq
  let E : N ≅ pullback (f ≫ π) π := hN.isoPullback
  let qP : N ⟶ (appendIncidenceModel f₀ π₀).left := E.hom ≫ qR
  have hb : E.hom ≫ (pullback.fst (f ≫ π) π ≫ bX) = bN :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun k => k ≫ bX) hN.isoPullback_hom_fst).trans hu)
  have hP : IsPullback qP bN (appendIncidenceModel f₀ π₀).hom κ :=
    curveModel_pullback h.1 E qP bN rfl hb
  have hfirst : qP ≫ (appendIncidenceFst f₀ π₀).left = u ≫ qX := by
    calc
      qP ≫ (appendIncidenceFst f₀ π₀).left =
          E.hom ≫ (qR ≫ (appendIncidenceFst f₀ π₀).left) := Category.assoc _ _ _
      _ = E.hom ≫ (pullback.fst (f ≫ π) π ≫ qX) :=
        congrArg (fun k => E.hom ≫ k) h.2.1
      _ = u ≫ qX := (Category.assoc _ _ _).symm.trans
        (congrArg (fun k => k ≫ qX) hN.isoPullback_hom_fst)
  have hlast : qP ≫ (appendIncidenceSnd f₀ π₀).left = v ≫ qF := by
    calc
      qP ≫ (appendIncidenceSnd f₀ π₀).left =
          E.hom ≫ (qR ≫ (appendIncidenceSnd f₀ π₀).left) := Category.assoc _ _ _
      _ = E.hom ≫ (pullback.snd (f ≫ π) π ≫ qF) :=
        congrArg (fun k => E.hom ≫ k) h.2.2
      _ = v ≫ qF := (Category.assoc _ _ _).symm.trans
        (congrArg (fun k => k ≫ qF) hN.isoPullback_hom_snd)
  exact ⟨qP, hP, hfirst, hlast⟩

private def retained_incidence_result
    {K : Type u} [CommRing K] (S : Subalgebra ℤ K)
    {N A F Q : Over (Spec (.of S))} (n : N ⟶ F) (a : A ⟶ F) (π : F ⟶ Q)
    {NK AK FK : Scheme.{u}} (bN : NK ⟶ Spec (.of K))
    (u : NK ⟶ AK) (v : NK ⟶ FK) (qN : NK ⟶ N.left)
    (qA : AK ⟶ A.left) (qF : FK ⟶ F.left)
    (hN : IsPullback qN bN N.hom (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (start : CoefficientStage S) : Prop :=
  ∃ (qP : NK ⟶ (appendIncidenceModel a π).left)
    (hP : IsPullback qP bN (appendIncidenceModel a π).hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (k : CoefficientStage S) (_ : start ≤ k)
    (E : stageScalarModel S N.hom k ≅
      stageScalarModel S (appendIncidenceModel a π).hom k)
    (d : stageScalarModel S N.hom k ⟶ stageScalarModel S A.hom k),
    qP ≫ (appendIncidenceFst a π).left = u ≫ qA ∧
    qP ≫ (appendIncidenceSnd a π).left = v ≫ qF ∧
    ((modelScalarCone S N.hom).π.app (op k) ≫ E.hom.left =
      (chosenPairIso (Spec.map (CommRingCat.ofHom (algebraMap S K)))
        N (appendIncidenceModel a π) bN qN qP hN hP).hom.left ≫
          (modelScalarCone S (appendIncidenceModel a π).hom).π.app (op k)) ∧
    ((modelScalarCone S (appendIncidenceModel a π).hom).π.app (op k) ≫ E.inv.left =
      (chosenPairIso (Spec.map (CommRingCat.ofHom (algebraMap S K)))
        N (appendIncidenceModel a π) bN qN qP hN hP).inv.left ≫
          (modelScalarCone S N.hom).π.app (op k)) ∧
    E.hom ≫ chosenScalarArrow
      (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom))
        (appendIncidenceSnd a π) =
      chosenScalarArrow
        (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom)) n ∧
    d = E.hom ≫ chosenScalarArrow
      (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom))
        (appendIncidenceFst a π) ∧
    IsPullback d.left
      (chosenScalarArrow
        (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom)) n).left
      ((chosenScalarArrow
          (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom)) a).left ≫
        (chosenScalarArrow
          (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom)) π).left)
      (chosenScalarArrow
        (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom)) π).left

private theorem retain_incidence
    {K : Type u} [CommRing K] (S : Subalgebra ℤ K) (hS : S.FG)
    {N A F Q : Over (Spec (.of S))}
    [CompactSpace N.left] [QuasiSeparatedSpace N.left]
    [CompactSpace A.left] [CompactSpace F.left]
    [LocallyOfFinitePresentation N.hom] [LocallyOfFinitePresentation A.hom]
    [LocallyOfFinitePresentation F.hom] [LocallyOfFinitePresentation Q.hom]
    (n : N ⟶ F) (a : A ⟶ F) (π : F ⟶ Q)
    {NK AK FK : Scheme.{u}} (bN : NK ⟶ Spec (.of K))
    (u : NK ⟶ AK) (v : NK ⟶ FK) (qN : NK ⟶ N.left)
    (qA : AK ⟶ A.left) (qF : FK ⟶ F.left)
    (hN : IsPullback qN bN N.hom (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hn : qN ≫ n.left = v ≫ qF)
    (hraw : ∃ qP : NK ⟶ (appendIncidenceModel a π).left,
      IsPullback qP bN (appendIncidenceModel a π).hom
        (Spec.map (CommRingCat.ofHom (algebraMap S K))) ∧
      qP ≫ (appendIncidenceFst a π).left = u ≫ qA ∧
      qP ≫ (appendIncidenceSnd a π).left = v ≫ qF)
    (start : CoefficientStage S) :
    retained_incidence_result S n a π bN u v qN qA qF hN start := by
  let : Algebra.FiniteType ℤ S := (Subalgebra.fg_iff_finiteType S).mp hS
  let : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing ℤ S
  have hprops := incidence_properties a π
  let : LocallyOfFinitePresentation (appendIncidenceModel a π).hom := hprops.1
  let : CompactSpace (appendIncidenceModel a π).left := hprops.2.1
  let : QuasiSeparatedSpace (appendIncidenceModel a π).left := hprops.2.2
  apply bind_witness hraw
  intro qP hp
  let E := chosenPairIso (Spec.map (CommRingCat.ofHom (algebraMap S K)))
    N (appendIncidenceModel a π) bN qN qP hN hp.1
  have hE : E.hom ≫ chosenScalarArrow
      (Spec.map (CommRingCat.ofHom (algebraMap S K))) (appendIncidenceSnd a π) =
      chosenScalarArrow (Spec.map (CommRingCat.ofHom (algebraMap S K))) n :=
    chosenPairIso_endpoint _ N (appendIncidenceModel a π) F bN qN qP hN hp.1
      n (appendIncidenceSnd a π) v qF hn hp.2.2
  apply bind_witness (exists_chosen_endpoint_iso S hS N (appendIncidenceModel a π) F
    n (appendIncidenceSnd a π) E hE start)
  intro k hk
  obtain ⟨hstart, E₀, hhom, hinv, hend⟩ := hk
  let κ := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom)
  let d : stageScalarModel S N.hom k ⟶ stageScalarModel S A.hom k :=
    E₀.hom ≫ chosenScalarArrow κ (appendIncidenceFst a π)
  have hpb : IsPullback d.left (chosenScalarArrow κ n).left
      ((chosenScalarArrow κ a).left ≫ (chosenScalarArrow κ π).left)
      (chosenScalarArrow κ π).left :=
    curveModel_pullback (scalar_incidence_cartesian κ a π)
      ((Over.forget (Spec (.of k.val))).mapIso E₀)
      d.left (chosenScalarArrow κ n).left rfl
      (congrArg (fun f => f.left) hend)
  exact ⟨qP, hp.1, k, hstart, E₀, d, hp.2.1, hp.2.2, hhom, hinv, hend, rfl, hpb⟩

/-- The appended incidence comparison, with both original projections and
its endpoint equation, extends to a common coefficient stage. -/
theorem exists_append_incidence_stage
    {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (S : Subalgebra ℤ K) (hS : S.FG) (G : ReductiveGroupData K)
    (word : List G.rootBase.support) (i : G.rootBase.support)
    {N A F Q : Over (Spec (.of S))}
    [CompactSpace N.left] [QuasiSeparatedSpace N.left]
    [CompactSpace A.left] [CompactSpace F.left]
    [LocallyOfFinitePresentation N.hom] [LocallyOfFinitePresentation A.hom]
    [LocallyOfFinitePresentation F.hom] [LocallyOfFinitePresentation Q.hom]
    (n : N ⟶ F) (a : A ⟶ F) (π : F ⟶ Q)
    (qN : bsdhScheme G (word ++ [i]) ⟶ N.left)
    (qA : bsdhScheme G word ⟶ A.left) (qF : (flagVariety G).scheme ⟶ F.left)
    (qQ : (partialFlagVariety G {i}).scheme ⟶ Q.left)
    (hN : IsPullback qN (bsdhToSpec G (word ++ [i])) N.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hA : IsPullback qA (bsdhToSpec G word) A.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hF : IsPullback qF (flagVariety G).toSpec F.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hQ : IsPullback qQ (partialFlagVariety G {i}).toSpec Q.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hn : qN ≫ n.left = bsdhMap G (word ++ [i]) ≫ qF)
    (ha : bsdhMap G word ≫ qF = qA ≫ a.left)
    (hπ : (partialFlagMorphism G {i}).left ≫ qQ = qF ≫ π.left)
    (start : CoefficientStage S) :
    retained_incidence_result S n a π (bsdhToSpec G (word ++ [i]))
      (bsdhAppendFst G word i) (bsdhMap G (word ++ [i])) qN qA qF hN start := by
  exact retain_incidence S hS n a π (bsdhToSpec G (word ++ [i]))
    (bsdhAppendFst G word i) (bsdhMap G (word ++ [i])) qN qA qF hN hn
    (incidence_coefficient_square
      (Spec.map (CommRingCat.ofHom (algebraMap S K)))
      (bsdhToSpec G (word ++ [i])) (bsdhToSpec G word)
      (flagVariety G).toSpec (partialFlagVariety G {i}).toSpec
      (bsdhMap G word) (partialFlagMorphism G {i}).left
      (bsdhAppendFst G word i) (bsdhMap G (word ++ [i]))
      rfl (partialFlagMorphism G {i}).w
      (bsdhAppendFst_toSpec G word i) (bsdhAppend_cartesian G word i)
      a π qA qF qQ hA hF hQ ha hπ) start

-- GAP: C6-STAGE. Retain the finite cell trivializations, their original
-- sections and the simpleCurve_finite_cases alternatives at one coefficient
-- stage, using exists_append_incidence_stage without changing its models.
-- The whole-projective-line and restricted-intersection certificates must
-- then be applied to these same fibres before endpoint induction is concluded.

end SchubertGeometry
