import OrbitComplexity.SchubertGeometry.BSDH.Paired
import OrbitComplexity.SchubertGeometry.Connectedness.ChosenPairedRetention
import OrbitComplexity.FrobeniusSplitting.Normality.Products.PairedModelGeometry
import OrbitComplexity.FrobeniusSplitting.Normality.Products.PairedScalarComparison
import Batteries.Tactic.Lint

/-! # The paired incidence model and its prescribed source comparison

The fibre product of the two retained endpoints has its original two projections.
Its scalar comparison is constructed over arbitrary schemes. A common coefficient
extension identifies it with the prescribed paired source and preserves the flag
endpoint; the prescribed source, target and endpoint are not replaced.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open ReductiveGroups FrobeniusSplitting

noncomputable section
universe u

namespace SchubertGeometry

/-- The incidence of the two prescribed endpoints over their common target. -/
def pairedIncidenceModel {B : Scheme.{u}} {X Y F : Over B}
    (f : X ⟶ F) (g : Y ⟶ F) : Over B :=
  Over.mk (pullback.fst f.left g.left ≫ X.hom)

/-- The incidence endpoint in the original common target. -/
def pairedIncidenceEndpoint {B : Scheme.{u}} {X Y F : Over B}
    (f : X ⟶ F) (g : Y ⟶ F) : pairedIncidenceModel f g ⟶ F :=
  Over.homMk (pullback.fst f.left g.left ≫ f.left)
    (by
      change (pullback.fst f.left g.left ≫ f.left) ≫ F.hom =
        pullback.fst f.left g.left ≫ X.hom
      rw [Category.assoc, f.w])

private theorem source_square {B T : Scheme.{u}} (κ : T ⟶ B)
    {N P : Scheme.{u}} (n : N ⟶ T) (a : P ⟶ T)
    {Q : Scheme.{u}} (q : P ⟶ Q) (b : Q ⟶ B)
    (h : IsPullback q a b κ) (E : N ≅ P) (hE : E.hom ≫ a = n) :
    IsPullback (E.hom ≫ q) n b κ := by
  exact h.of_iso' E (Iso.refl Q) (Iso.refl T) (Iso.refl B)
    (by simp only [Iso.refl_hom, Category.comp_id])
    (by simpa only [Iso.refl_hom, Category.comp_id] using hE)
    (by simp only [Iso.refl_hom, Category.id_comp, Category.comp_id])
    (by simp only [Iso.refl_hom, Category.id_comp, Category.comp_id])

private theorem composite_projection {C : Type*} [Category C]
    {N P Q X : C} (e : N ⟶ P) (q : P ⟶ Q) (r : Q ⟶ X)
    (a : P ⟶ X) (b : N ⟶ X) (hq : q ≫ r = a) (he : e ≫ a = b) :
    (e ≫ q) ≫ r = b := by
  rw [Category.assoc, hq, he]

private theorem raw_pair_comparison {B T : Scheme.{u}} (κ : T ⟶ B)
    (X Y F : Over B) (XK YK FK : Over T)
    (f : X ⟶ F) (g : Y ⟶ F) (fK : XK ⟶ FK) (gK : YK ⟶ FK)
    (qX : XK.left ⟶ X.left) (qY : YK.left ⟶ Y.left) (qF : FK.left ⟶ F.left)
    (hX : IsPullback qX XK.hom X.hom κ)
    (hY : IsPullback qY YK.hom Y.hom κ)
    (hF : IsPullback qF FK.hom F.hom κ)
    (hf : fK.left ≫ qF = qX ≫ f.left)
    (hg : gK.left ≫ qF = qY ≫ g.left) :
    ∃ q : (pullback fK gK).left ⟶ (pairedIncidenceModel f g).left,
      IsPullback q (pullback fK gK).hom (pairedIncidenceModel f g).hom κ ∧
      q ≫ pullback.fst f.left g.left = (pullback.fst fK gK).left ≫ qX ∧
      q ≫ pullback.snd f.left g.left = (pullback.snd fK gK).left ≫ qY ∧
      q ≫ (pairedIncidenceEndpoint f g).left =
        (pullback.fst fK gK).left ≫ fK.left ≫ qF := by
  let hN := (IsPullback.of_hasPullback fK gK).map (Over.forget T)
  let E : (pullback fK gK).left ≅ pullback fK.left gK.left :=
    (Over.forget XK.left).mapIso hN.isoOverPullback
  have hEf : E.hom ≫ pullback.fst fK.left gK.left = (pullback.fst fK gK).left :=
    hN.isoOverPullback.hom.w
  have hEg : E.hom ≫ pullback.snd fK.left gK.left = (pullback.snd fK gK).left :=
    hN.isoOverPullback_hom_left_comp_snd
  have hEb : E.hom ≫ (pullback.fst fK.left gK.left ≫ XK.hom) =
      (pullback fK gK).hom := by
    rw [← Category.assoc, hEf]
    exact (pullback.fst fK gK).w
  let q₀ := pullback.map fK.left gK.left f.left g.left qX qY qF hf hg
  have H := paired_model_scalar_pullback κ XK.hom YK.hom FK.hom
    X.hom Y.hom F.hom fK.left gK.left f.left g.left
    fK.w gK.w f.w g.w qX qY qF hX hY hF hf hg
  let q := E.hom ≫ q₀
  have hqf : q ≫ pullback.fst f.left g.left = (pullback.fst fK gK).left ≫ qX := by
    exact composite_projection E.hom q₀ _ _ _ H.2.1
      (by rw [← Category.assoc, hEf])
  have hqg : q ≫ pullback.snd f.left g.left = (pullback.snd fK gK).left ≫ qY := by
    exact composite_projection E.hom q₀ _ _ _ H.2.2
      (by rw [← Category.assoc, hEg])
  refine ⟨q, source_square κ (pullback fK gK).hom _ q₀ _ H.1 E hEb, hqf, hqg, ?_⟩
  change q ≫ (pullback.fst f.left g.left ≫ f.left) = _
  rw [← Category.assoc, hqf, Category.assoc, ← hf, ← Category.assoc]

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K) (a b : List G.rootBase.support)

omit [IsAlgClosed K] [CharZero K] in
/-- The incidence of proper endpoint models is proper and finitely presented,
with compact, quasi-separated and locally noetherian source. -/
theorem pairedIncidenceModel_properties
    (S : Subalgebra ℤ K) (hS : S.FG) (X Y F : Over (Spec (.of S)))
    [IsProper X.hom] [LocallyOfFinitePresentation X.hom]
    [IsProper Y.hom] [LocallyOfFinitePresentation Y.hom]
    [IsSeparated F.hom] (f : X ⟶ F) (g : Y ⟶ F) :
    IsProper (pairedIncidenceModel f g).hom ∧
      LocallyOfFinitePresentation (pairedIncidenceModel f g).hom ∧
      CompactSpace (pairedIncidenceModel f g).left ∧
      QuasiSeparatedSpace (pairedIncidenceModel f g).left ∧
      IsLocallyNoetherian (pairedIncidenceModel f g).left := by
  have h := paired_model_geometry S hS X Y F f g
  exact ⟨h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2⟩


private theorem chosen_scalar_comp {B T : Scheme.{u}} (κ : T ⟶ B)
    {C D F : Over B} (e : C ⟶ D) (i : D ⟶ F) :
    chosenScalarArrow κ (e ≫ i) = chosenScalarArrow κ e ≫ chosenScalarArrow κ i := by
  apply (Over.forget T).map_injective
  change (chosenScalarArrow κ (e ≫ i)).left =
    (chosenScalarArrow κ e).left ≫ (chosenScalarArrow κ i).left
  apply pullback.hom_ext
  · simp only [chosenScalarArrow, Over.homMk_left, Category.assoc, pullback.lift_fst]
  · simp only [chosenScalarArrow, Over.homMk_left, Over.comp_left,
      Category.assoc, pullback.lift_snd_assoc, pullback.lift_snd]

private theorem target_transport {C : Type*} [Category C]
    {X P D F : C} (E : X ≅ P) (e : X ⟶ D) (i : D ⟶ F) (p : P ⟶ F)
    (h : E.hom ≫ p = e ≫ i) :
    E.hom ≫ (E.inv ≫ e) = e ∧ (E.inv ≫ e) ≫ i = p := by
  constructor
  · simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  · calc
      (E.inv ≫ e) ≫ i = E.inv ≫ (e ≫ i) := Category.assoc _ _ _
      _ = E.inv ≫ (E.hom ≫ p) := congrArg (fun t => E.inv ≫ t) h.symm
      _ = p := by simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

omit [IsAlgClosed K] [CharZero K] in
private theorem raw_pair_retention
    (S : Subalgebra ℤ K) (hS : S.FG)
    (C X Y F : Over (Spec (.of S)))
    [CompactSpace C.left] [QuasiSeparatedSpace C.left]
    [LocallyOfFinitePresentation C.hom]
    [IsProper X.hom] [LocallyOfFinitePresentation X.hom]
    [IsProper Y.hom] [LocallyOfFinitePresentation Y.hom]
    [IsSeparated F.hom] [LocallyOfFinitePresentation F.hom]
    (XK YK FK : Over (Spec (.of K)))
    (f : X ⟶ F) (g : Y ⟶ F) (fK : XK ⟶ FK) (gK : YK ⟶ FK)
    (qX : XK.left ⟶ X.left) (qY : YK.left ⟶ Y.left) (qF : FK.left ⟶ F.left)
    (hX : IsPullback qX XK.hom X.hom (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hY : IsPullback qY YK.hom Y.hom (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hF : IsPullback qF FK.hom F.hom (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hf : fK.left ≫ qF = qX ≫ f.left) (hg : gK.left ≫ qF = qY ≫ g.left)
    (qC : (pullback fK gK).left ⟶ C.left)
    (hC : IsPullback qC (pullback fK gK).hom C.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (D : Over (Spec (.of S))) (eC : C ⟶ D) (iD : D ⟶ F)
    (heC : qC ≫ eC.left ≫ iD.left = (pullback.fst fK gK).left ≫ fK.left ≫ qF)
    (start : CoefficientStage S) :
    ∃ (q : (pullback fK gK).left ⟶ (pairedIncidenceModel f g).left)
      (hP : IsPullback q (pullback fK gK).hom (pairedIncidenceModel f g).hom
        (Spec.map (CommRingCat.ofHom (algebraMap S K)))),
      (q ≫ pullback.fst f.left g.left = (pullback.fst fK gK).left ≫ qX) ∧
      (q ≫ pullback.snd f.left g.left = (pullback.snd fK gK).left ≫ qY) ∧
      let E := chosenPairIso (Spec.map (CommRingCat.ofHom (algebraMap S K)))
        C (pairedIncidenceModel f g) (pullback fK gK).hom qC q hC hP
      ∃ (j : CoefficientStage S) (_ : start ≤ j)
        (E₀ : stageScalarModel S C.hom j ≅ stageScalarModel S (pairedIncidenceModel f g).hom j),
        ((modelScalarCone S C.hom).π.app (op j) ≫ E₀.hom.left =
          E.hom.left ≫ (modelScalarCone S (pairedIncidenceModel f g).hom).π.app (op j)) ∧
        ((modelScalarCone S (pairedIncidenceModel f g).hom).π.app (op j) ≫ E₀.inv.left =
          E.inv.left ≫ (modelScalarCone S C.hom).π.app (op j)) ∧
        E₀.hom ≫ chosenScalarArrow
            (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion j.property.2).toRingHom))
              (pairedIncidenceEndpoint f g) =
          chosenScalarArrow
            (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion j.property.2).toRingHom)) (eC ≫ iD) ∧
        ∃ eP : stageScalarModel S (pairedIncidenceModel f g).hom j ⟶ stageScalarModel S D.hom j,
          E₀.hom ≫ eP = chosenScalarArrow
            (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion j.property.2).toRingHom)) eC ∧
          eP ≫ chosenScalarArrow
            (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion j.property.2).toRingHom)) iD =
              chosenScalarArrow
                (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion j.property.2).toRingHom))
                  (pairedIncidenceEndpoint f g) := by
  obtain ⟨q, hP, hqf, hqg, hqe⟩ := raw_pair_comparison
    (Spec.map (CommRingCat.ofHom (algebraMap S K))) X Y F XK YK FK
    f g fK gK qX qY qF hX hY hF hf hg
  have H := pairedIncidenceModel_properties S hS X Y F f g
  let : LocallyOfFinitePresentation (pairedIncidenceModel f g).hom := H.2.1
  let : CompactSpace (pairedIncidenceModel f g).left := H.2.2.1
  let : QuasiSeparatedSpace (pairedIncidenceModel f g).left := H.2.2.2.1
  obtain ⟨j, hj, E₀, hhom, hinv, hflag⟩ :=
    exists_chosen_paired_retention S hS C (pairedIncidenceModel f g) F
      (pullback fK gK).hom qC q hC hP (eC ≫ iD) (pairedIncidenceEndpoint f g)
      ((pullback.fst fK gK).left ≫ fK.left) qF
      (by simpa only [Over.comp_left, Category.assoc] using heC)
      (by simpa only [Category.assoc] using hqe) start
  let κ := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion j.property.2).toRingHom)
  have ht := target_transport E₀ (chosenScalarArrow κ eC) (chosenScalarArrow κ iD)
    (chosenScalarArrow κ (pairedIncidenceEndpoint f g))
    (hflag.trans (chosen_scalar_comp κ eC iD))
  exact ⟨q, hP, hqf, hqg, j, hj, E₀, hhom, hinv, hflag,
    E₀.inv ≫ chosenScalarArrow κ eC, ht.1, ht.2⟩

/-- A common coefficient extension identifies the prescribed paired source
with the incidence of the two retained endpoints, preserving both scalar
projections and the prescribed flag endpoint. -/
theorem exists_chosen_paired_incidence
    (S : Subalgebra ℤ K) (hS : S.FG) (C X Y F : Over (Spec (.of S)))
    [CompactSpace C.left] [QuasiSeparatedSpace C.left]
    [LocallyOfFinitePresentation C.hom]
    [IsProper X.hom] [LocallyOfFinitePresentation X.hom]
    [IsProper Y.hom] [LocallyOfFinitePresentation Y.hom]
    [IsSeparated F.hom] [LocallyOfFinitePresentation F.hom]
    (f : X ⟶ F) (g : Y ⟶ F)
    (qX : (bsdhVariety G a).scheme ⟶ X.left)
    (qY : (bsdhVariety G b).scheme ⟶ Y.left)
    (qF : (flagVariety G).scheme ⟶ F.left)
    (hX : IsPullback qX (bsdhVariety G a).toSpec X.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hY : IsPullback qY (bsdhVariety G b).toSpec Y.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hF : IsPullback qF (flagVariety G).toSpec F.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hf : bsdhMap G a ≫ qF = qX ≫ f.left)
    (hg : (bsdhOppositeEndpoint G b).left ≫ qF = qY ≫ g.left)
    (qC : (pairedBSDHSource G a b).left ⟶ C.left)
    (hC : IsPullback qC (pairedBSDHSource G a b).hom C.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (D : Over (Spec (.of S))) (eC : C ⟶ D) (iD : D ⟶ F)
    (heC : qC ≫ eC.left ≫ iD.left =
      (pullback.fst (Over.homMk (bsdhMap G a) rfl :
          (bsdhVariety G a).toOver ⟶ (flagVariety G).toOver) (bsdhOppositeEndpoint G b)).left ≫
        bsdhMap G a ≫ qF)
    (start : CoefficientStage S) :
    ∃ (q : (pairedBSDHSource G a b).left ⟶ (pairedIncidenceModel f g).left)
      (hP : IsPullback q (pairedBSDHSource G a b).hom (pairedIncidenceModel f g).hom
        (Spec.map (CommRingCat.ofHom (algebraMap S K)))),
      (q ≫ pullback.fst f.left g.left =
        (pullback.fst (Over.homMk (bsdhMap G a) rfl :
          (bsdhVariety G a).toOver ⟶ (flagVariety G).toOver) (bsdhOppositeEndpoint G b)).left ≫ qX)
            ∧
      (q ≫ pullback.snd f.left g.left =
        (pullback.snd (Over.homMk (bsdhMap G a) rfl :
          (bsdhVariety G a).toOver ⟶ (flagVariety G).toOver) (bsdhOppositeEndpoint G b)).left ≫ qY)
            ∧
      let E := chosenPairIso (Spec.map (CommRingCat.ofHom (algebraMap S K)))
        C (pairedIncidenceModel f g) (pairedBSDHSource G a b).hom qC q hC hP
      ∃ (j : CoefficientStage S) (_ : start ≤ j)
        (E₀ : stageScalarModel S C.hom j ≅ stageScalarModel S (pairedIncidenceModel f g).hom j),
        ((modelScalarCone S C.hom).π.app (op j) ≫ E₀.hom.left =
          E.hom.left ≫ (modelScalarCone S (pairedIncidenceModel f g).hom).π.app (op j)) ∧
        ((modelScalarCone S (pairedIncidenceModel f g).hom).π.app (op j) ≫ E₀.inv.left =
          E.inv.left ≫ (modelScalarCone S C.hom).π.app (op j)) ∧
        E₀.hom ≫ chosenScalarArrow
            (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion j.property.2).toRingHom))
              (pairedIncidenceEndpoint f g) =
          chosenScalarArrow
            (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion j.property.2).toRingHom)) (eC ≫ iD) ∧
        ∃ eP : stageScalarModel S (pairedIncidenceModel f g).hom j ⟶ stageScalarModel S D.hom j,
          E₀.hom ≫ eP = chosenScalarArrow
            (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion j.property.2).toRingHom)) eC ∧
          eP ≫ chosenScalarArrow
            (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion j.property.2).toRingHom)) iD =
              chosenScalarArrow
                (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion j.property.2).toRingHom))
                  (pairedIncidenceEndpoint f g) :=
  raw_pair_retention S hS C X Y F
    (bsdhVariety G a).toOver (bsdhVariety G b).toOver (flagVariety G).toOver
    f g (Over.homMk (bsdhMap G a) rfl :
          (bsdhVariety G a).toOver ⟶ (flagVariety G).toOver) (bsdhOppositeEndpoint G b)
    qX qY qF hX hY hF hf hg qC hC D eC iD heC start

end SchubertGeometry
