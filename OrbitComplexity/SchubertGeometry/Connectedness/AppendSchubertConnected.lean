import Batteries.Tactic.Lint
import OrbitComplexity.SchubertGeometry.Connectedness.AppendCellConnected
import OrbitComplexity.SchubertGeometry.Connectedness.SchubertCoverModels
import OrbitComplexity.SchubertGeometry.Normality.Curves.SchubertWeylSections

set_option autoImplicit false

/-! # Appended endpoints over the retained Schubert cover

Weyl sections and polynomial lower-cell maps are constructed on one
coefficient extension of the specified endpoint model. The cell products
then prove geometric connectedness of that endpoint above the extension.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReductiveGroups
open FrobeniusSplitting Opposite

namespace SchubertGeometry

universe u v

private theorem bind_exists {A : Sort*} {P : A → Prop} {Q : Prop}
    (h : ∃ a, P a) (f : ∀ a, P a → Q) : Q := by
  obtain ⟨a, ha⟩ := h
  exact f a ha

private theorem bound_stages {I : Type*} [Preorder I] [IsDirectedOrder I]
    (r s : I) {Q : Prop} (h : ∀ t, r ≤ t → s ≤ t → Q) : Q := by
  obtain ⟨t, hrt, hst⟩ := exists_ge_ge r s
  exact h t hrt hst

private def scalar_model {B T : Scheme.{u}} (κ : T ⟶ B) (X : Over B) : Over T :=
  Over.mk (pullback.fst κ X.hom)

private theorem scalar_arrow_cartesian {B T : Scheme.{u}} (κ : T ⟶ B)
    {X Y : Over B} (f : X ⟶ Y) :
    IsPullback (chosenScalarArrow κ f).left (pullback.snd κ X.hom)
      (pullback.snd κ Y.hom) f.left := by
  have hf : (chosenScalarArrow κ f).left ≫ pullback.fst κ Y.hom =
      pullback.fst κ X.hom := by
    have h := (chosenScalarArrow κ f).w
    change (chosenScalarArrow κ f).left ≫ pullback.fst κ Y.hom =
      pullback.fst κ X.hom at h
    exact h
  have h : IsPullback ((chosenScalarArrow κ f).left ≫ pullback.fst κ Y.hom)
      (pullback.snd κ X.hom) κ (f.left ≫ Y.hom) := by
    rw [hf, f.w]
    exact IsPullback.of_hasPullback κ X.hom
  exact h.of_right (chosenScalarArrow_snd κ f) (IsPullback.of_hasPullback κ Y.hom)

private theorem scalar_composition {B T : Scheme.{u}} (κ : T ⟶ B)
    {X Y Z : Over B} (f : X ⟶ Y) (g : Y ⟶ Z) :
    chosenScalarArrow κ (f ≫ g) = chosenScalarArrow κ f ≫ chosenScalarArrow κ g := by
  apply (Over.forget T).map_injective
  change (chosenScalarArrow κ (f ≫ g)).left =
    (chosenScalarArrow κ f ≫ chosenScalarArrow κ g).left
  apply pullback.hom_ext
  · exact (chosenScalarArrow κ (f ≫ g)).w.trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun h => (chosenScalarArrow κ f).left ≫ h)
          (chosenScalarArrow κ g).w).trans (chosenScalarArrow κ f).w)).symm
  · calc
      (chosenScalarArrow κ (f ≫ g)).left ≫ pullback.snd κ Z.hom =
          pullback.snd κ X.hom ≫ (f ≫ g).left := chosenScalarArrow_snd κ (f ≫ g)
      _ = (pullback.snd κ X.hom ≫ f.left) ≫ g.left := (Category.assoc _ _ _).symm
      _ = ((chosenScalarArrow κ f).left ≫ pullback.snd κ Y.hom) ≫ g.left :=
        congrArg (fun h => h ≫ g.left) (chosenScalarArrow_snd κ f).symm
      _ = (chosenScalarArrow κ f).left ≫ (pullback.snd κ Y.hom ≫ g.left) :=
        Category.assoc _ _ _
      _ = (chosenScalarArrow κ f).left ≫
          ((chosenScalarArrow κ g).left ≫ pullback.snd κ Z.hom) :=
        congrArg (fun h => (chosenScalarArrow κ f).left ≫ h)
          (chosenScalarArrow_snd κ g).symm
      _ = ((chosenScalarArrow κ f).left ≫ (chosenScalarArrow κ g).left) ≫
          pullback.snd κ Z.hom := (Category.assoc _ _ _).symm

private theorem scalar_property (P : MorphismProperty Scheme.{u})
    [MorphismProperty.IsStableUnderBaseChange P] {B T : Scheme.{u}} (κ : T ⟶ B)
    {X Y : Over B} (f : X ⟶ Y) (hf : P f.left) : P (chosenScalarArrow κ f).left :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (scalar_arrow_cartesian κ f).flip hf

private theorem scalar_fp {B T : Scheme.{u}} (κ : T ⟶ B)
    (X : Over B) [LocallyOfFinitePresentation X.hom] :
    LocallyOfFinitePresentation (scalar_model κ X).hom := by
  change LocallyOfFinitePresentation (pullback.fst κ X.hom)
  infer_instance

private theorem scalar_qc {B T : Scheme.{u}} (κ : T ⟶ B)
    (X : Over B) [QuasiCompact X.hom] : QuasiCompact (scalar_model κ X).hom := by
  change QuasiCompact (pullback.fst κ X.hom)
  infer_instance

private def stage_map {K : Type u} [CommRing K] (S : Subalgebra ℤ K)
    (X : Over (Spec (.of S))) (U : Over (Spec (.of K))) (q : U.left ⟶ X.left)
    (h : IsPullback q U.hom X.hom (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (k : CoefficientStage S) : U.left ⟶ (stageScalarModel S X.hom k).left :=
  h.flip.isoOverPullback.hom.left ≫ (modelScalarCone S X.hom).π.app (op k)

private theorem stage_map_cartesian {K : Type u} [CommRing K] (S : Subalgebra ℤ K)
    (X : Over (Spec (.of S))) (U : Over (Spec (.of K))) (q : U.left ⟶ X.left)
    (h : IsPullback q U.hom X.hom (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (k : CoefficientStage S) :
    IsPullback (stage_map S X U q h k) U.hom (stageScalarModel S X.hom k).hom
      (Spec.map (CommRingCat.ofHom (algebraMap k.val K))) :=
  overIso_modelStage_cartesian S X.hom k U h.flip.isoOverPullback

private theorem stage_map_original {K : Type u} [CommRing K] (S : Subalgebra ℤ K)
    (X : Over (Spec (.of S))) (U : Over (Spec (.of K))) (q : U.left ⟶ X.left)
    (h : IsPullback q U.hom X.hom (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (k : CoefficientStage S) :
    stage_map S X U q h k ≫ pullback.snd
      (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom)) X.hom = q := by
  have ht : (modelScalarCone S X.hom).π.app (op k) ≫ pullback.snd
      (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom)) X.hom =
      pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap S K))) X.hom := by
    change pullback.lift _ _ _ ≫ pullback.snd _ _ = _
    exact pullback.lift_snd _ _ _
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun t => h.flip.isoOverPullback.hom.left ≫ t) ht).trans
      h.flip.isoOverPullback_hom_left_comp_snd)

private theorem scalar_comparison {B BK T : Scheme.{u}} (κ : T ⟶ B) (ρ : BK ⟶ T)
    {X Y : Over B} {U V : Over BK} (f : X ⟶ Y) (g : U ⟶ V)
    (qX : U.left ⟶ X.left) (qY : V.left ⟶ Y.left)
    (qXT : U.left ⟶ (scalar_model κ X).left)
    (qYT : V.left ⟶ (scalar_model κ Y).left)
    (hXT : IsPullback qXT U.hom (scalar_model κ X).hom ρ)
    (hYT : IsPullback qYT V.hom (scalar_model κ Y).hom ρ)
    (hXo : qXT ≫ pullback.snd κ X.hom = qX)
    (hYo : qYT ≫ pullback.snd κ Y.hom = qY)
    (h : qX ≫ f.left = g.left ≫ qY) :
    qXT ≫ (chosenScalarArrow κ f).left = g.left ≫ qYT := by
  apply pullback.hom_ext
  · calc
      (qXT ≫ (chosenScalarArrow κ f).left) ≫ pullback.fst κ Y.hom =
          qXT ≫ (scalar_model κ X).hom :=
        (Category.assoc _ _ _).trans
          (congrArg (fun t => qXT ≫ t) (chosenScalarArrow κ f).w)
      _ = U.hom ≫ ρ := hXT.w
      _ = (g.left ≫ qYT) ≫ pullback.fst κ Y.hom := by
        exact ((Category.assoc g.left qYT (scalar_model κ Y).hom).trans
          ((congrArg (fun t => g.left ≫ t) hYT.w).trans
            ((Category.assoc g.left V.hom ρ).symm.trans
              (congrArg (fun t => t ≫ ρ) g.w)))).symm
  · calc
      (qXT ≫ (chosenScalarArrow κ f).left) ≫ pullback.snd κ Y.hom =
          qXT ≫ (pullback.snd κ X.hom ≫ f.left) :=
        (Category.assoc _ _ _).trans
          (congrArg (fun t => qXT ≫ t) (chosenScalarArrow_snd κ f))
      _ = qX ≫ f.left := (Category.assoc _ _ _).symm.trans
        (congrArg (fun t => t ≫ f.left) hXo)
      _ = g.left ≫ qY := h
      _ = (g.left ≫ qYT) ≫ pullback.snd κ Y.hom :=
        (congrArg (fun t => g.left ≫ t) hYo.symm).trans (Category.assoc _ _ _).symm

private theorem scalar_composite_comparison {B BK T : Scheme.{u}}
    (κ : T ⟶ B) {X Y Z : Over B} {U V : Over BK}
    (f : X ⟶ Y) (g : Y ⟶ Z) (n : U.left ⟶ V.left)
    (qU : U.left ⟶ (scalar_model κ X).left)
    (qV : V.left ⟶ (scalar_model κ Z).left)
    (h : qU ≫ (chosenScalarArrow κ (f ≫ g)).left = n ≫ qV) :
    qU ≫ (chosenScalarArrow κ f ≫ chosenScalarArrow κ g).left = n ≫ qV := by
  exact (congrArg (fun t => qU ≫ t.left) (scalar_composition κ f g)).symm.trans h

private theorem scalar_square {B BK T : Scheme.{u}} (κ : T ⟶ B)
    {X Y : Over B} {U V : Over BK} (f : X ⟶ Y) (g : U ⟶ V)
    (qU : U.left ⟶ X.left) (qV : V.left ⟶ Y.left)
    (h : IsPullback g.left qU qV f.left)
    (qUT : U.left ⟶ (scalar_model κ X).left)
    (qVT : V.left ⟶ (scalar_model κ Y).left)
    (hU : qUT ≫ pullback.snd κ X.hom = qU)
    (hV : qVT ≫ pullback.snd κ Y.hom = qV)
    (hcomm : qUT ≫ (chosenScalarArrow κ f).left = g.left ≫ qVT) :
    IsPullback g.left qUT qVT (chosenScalarArrow κ f).left := by
  have ho : IsPullback g.left (qUT ≫ pullback.snd κ X.hom)
      (qVT ≫ pullback.snd κ Y.hom) f.left := by
    rw [hU, hV]
    exact h
  exact ho.of_bot hcomm.symm (scalar_arrow_cartesian κ f)

private theorem lifted_condition {B T U : Scheme.{u}} (κ : T ⟶ B)
    (ρ : T ⟶ U) (ζ : U ⟶ B) (X : Over B)
    (s : U ⟶ X.left) (hs : s ≫ X.hom = ζ) (hρ : ρ ≫ ζ = κ) :
    (𝟙 T) ≫ κ = (ρ ≫ s) ≫ X.hom :=
  (Category.id_comp κ).trans (hρ.symm.trans
    ((congrArg (fun t => ρ ≫ t) hs.symm).trans (Category.assoc ρ s X.hom).symm))

private def lifted_section {B T U : Scheme.{u}} (κ : T ⟶ B)
    (ρ : T ⟶ U) (ζ : U ⟶ B) (X : Over B)
    (s : U ⟶ X.left) (hs : s ≫ X.hom = ζ) (hρ : ρ ≫ ζ = κ) :
    Over.mk (𝟙 T) ⟶ scalar_model κ X :=
  Over.homMk (pullback.lift (𝟙 T) (ρ ≫ s) (lifted_condition κ ρ ζ X s hs hρ))
    (pullback.lift_fst _ _ _)

private theorem lifted_section_original {B T U : Scheme.{u}} (κ : T ⟶ B)
    (ρ : T ⟶ U) (ζ : U ⟶ B) (X : Over B)
    (s : U ⟶ X.left) (hs : s ≫ X.hom = ζ) (hρ : ρ ≫ ζ = κ) :
    (lifted_section κ ρ ζ X s hs hρ).left ≫ pullback.snd κ X.hom = ρ ≫ s :=
  pullback.lift_snd _ _ _

private theorem lifted_section_comparison {B T U BK : Scheme.{u}}
    (κ : T ⟶ B) (ρ : T ⟶ U) (ζ : U ⟶ B) (τ : BK ⟶ T) (τ₀ : BK ⟶ U)
    (X : Over B) (V : Over BK) (q : V.left ⟶ X.left)
    (qT : V.left ⟶ (scalar_model κ X).left)
    (hT : IsPullback qT V.hom (scalar_model κ X).hom τ)
    (hTo : qT ≫ pullback.snd κ X.hom = q)
    (s : U ⟶ X.left) (hs : s ≫ X.hom = ζ) (hρ : ρ ≫ ζ = κ)
    (p : BK ⟶ V.left) (hp : p ≫ V.hom = 𝟙 BK)
    (hps : p ≫ q = τ₀ ≫ s) (hτ : τ ≫ ρ = τ₀) :
    p ≫ qT = τ ≫ (lifted_section κ ρ ζ X s hs hρ).left := by
  apply pullback.hom_ext
  · calc
      (p ≫ qT) ≫ pullback.fst κ X.hom = (p ≫ V.hom) ≫ τ :=
        (Category.assoc _ _ _).trans
          ((congrArg (fun t => p ≫ t) hT.w).trans (Category.assoc _ _ _).symm)
      _ = τ := (congrArg (fun t => t ≫ τ) hp).trans (Category.id_comp _)
      _ = (τ ≫ (lifted_section κ ρ ζ X s hs hρ).left) ≫ pullback.fst κ X.hom :=
        ((Category.assoc _ _ _).trans
          ((congrArg (fun t => τ ≫ t) (lifted_section κ ρ ζ X s hs hρ).w).trans
            (Category.comp_id _))).symm
  · calc
      (p ≫ qT) ≫ pullback.snd κ X.hom = p ≫ q :=
        (Category.assoc _ _ _).trans (congrArg (fun t => p ≫ t) hTo)
      _ = τ₀ ≫ s := hps
      _ = (τ ≫ ρ) ≫ s := congrArg (fun t => t ≫ s) hτ.symm
      _ = (τ ≫ (lifted_section κ ρ ζ X s hs hρ).left) ≫ pullback.snd κ X.hom :=
        (Category.assoc _ _ _).trans
          ((congrArg (fun t => τ ≫ t)
            (lifted_section_original κ ρ ζ X s hs hρ).symm).trans
              (Category.assoc _ _ _).symm)

private theorem point_image {T : Type*} [Category T] {BK A B C D : T}
    (p : BK ⟶ A) (i : A ⟶ B) (w : BK ⟶ B) (qA : A ⟶ C)
    (qB : B ⟶ D) (j : C ⟶ D) (τ : BK ⟶ C) (hp : p ≫ i = w)
    (hj : qA ≫ j = i ≫ qB) (hs : p ≫ qA = τ) : w ≫ qB = τ ≫ j := by
  calc
    w ≫ qB = p ≫ (i ≫ qB) :=
      (congrArg (fun t => t ≫ qB) hp.symm).trans (Category.assoc _ _ _)
    _ = p ≫ (qA ≫ j) := congrArg (fun t => p ≫ t) hj.symm
    _ = τ ≫ j := (Category.assoc _ _ _).symm.trans (congrArg (fun t => t ≫ j) hs)

private theorem cell_image {T : Type*} [Category T] {A B C D E F : T}
    (c : A ⟶ B) (i : B ⟶ C) (a : A ⟶ C)
    (qA : A ⟶ D) (qB : B ⟶ E) (qC : C ⟶ F)
    (d : D ⟶ E) (j : E ⟶ F)
    (ha : c ≫ i = a) (hc : qA ≫ d = c ≫ qB) (hj : qB ≫ j = i ≫ qC) :
    a ≫ qC = qA ≫ (d ≫ j) := by
  calc
    a ≫ qC = c ≫ (i ≫ qC) :=
      (congrArg (fun t => t ≫ qC) ha.symm).trans (Category.assoc _ _ _)
    _ = c ≫ (qB ≫ j) := congrArg (fun t => c ≫ t) hj.symm
    _ = qA ≫ (d ≫ j) :=
      (Category.assoc _ _ _).symm.trans
        ((congrArg (fun t => t ≫ j) hc.symm).trans (Category.assoc _ _ _))

private def scalar_tower_iso {B T U : Scheme.{u}} (ζ : U ⟶ T) (κ : T ⟶ B)
    (X : Over B) : scalar_model ζ (scalar_model κ X) ≅ scalar_model (ζ ≫ κ) X :=
  ((IsPullback.of_hasPullback ζ (pullback.fst κ X.hom)).flip.paste_horiz
    (IsPullback.of_hasPullback κ X.hom).flip).flip.isoOverPullback

private theorem scalar_tower_original {B T U : Scheme.{u}}
    (ζ : U ⟶ T) (κ : T ⟶ B) (X : Over B) :
    (scalar_tower_iso ζ κ X).hom.left ≫ pullback.snd (ζ ≫ κ) X.hom =
      pullback.snd ζ (scalar_model κ X).hom ≫ pullback.snd κ X.hom :=
  IsPullback.isoOverPullback_hom_left_comp_snd _

private theorem compose_projection {C : Type*} [Category C]
    {A B X Y P Q : C} (s : A ⟶ B) (u : B ⟶ Y) (r : A ⟶ X)
    (a : X ⟶ Y) (x : X ⟶ P) (y : Y ⟶ Q) (f : P ⟶ Q)
    (hs : s ≫ u = r ≫ a) (ha : a ≫ y = x ≫ f) :
    s ≫ (u ≫ y) = (r ≫ x) ≫ f := by
  calc
    s ≫ (u ≫ y) = (s ≫ u) ≫ y := (Category.assoc s u y).symm
    _ = (r ≫ a) ≫ y := congrArg (fun t => t ≫ y) hs
    _ = r ≫ (a ≫ y) := Category.assoc r a y
    _ = r ≫ (x ≫ f) := congrArg (fun t => r ≫ t) ha
    _ = (r ≫ x) ≫ f := (Category.assoc r x f).symm

private theorem compare_projection {C : Type*} [Category C]
    {A A' B B' X Y : C} (e : A ⟶ A') (e' : B ⟶ B')
    (d : A' ⟶ B') (s : A ⟶ B) (x : A' ⟶ X) (y : B' ⟶ Y)
    (z : A ⟶ X) (w : B ⟶ Y) (f : X ⟶ Y)
    (hx : e ≫ x = z) (hy : e' ≫ y = w)
    (hd : d ≫ y = x ≫ f) (hs : s ≫ w = z ≫ f) :
    (e ≫ d) ≫ y = (s ≫ e') ≫ y := by
  calc
    (e ≫ d) ≫ y = e ≫ (d ≫ y) := Category.assoc e d y
    _ = e ≫ (x ≫ f) := congrArg (fun t => e ≫ t) hd
    _ = (e ≫ x) ≫ f := (Category.assoc e x f).symm
    _ = z ≫ f := congrArg (fun t => t ≫ f) hx
    _ = s ≫ w := hs.symm
    _ = s ≫ (e' ≫ y) := congrArg (fun t => s ≫ t) hy.symm
    _ = (s ≫ e') ≫ y := (Category.assoc s e' y).symm

private theorem scalar_tower_natural {B T U : Scheme.{u}}
    (ζ : U ⟶ T) (κ : T ⟶ B) {X Y : Over B} (f : X ⟶ Y) :
    (scalar_tower_iso ζ κ X).hom ≫ chosenScalarArrow (ζ ≫ κ) f =
      chosenScalarArrow ζ (chosenScalarArrow κ f) ≫ (scalar_tower_iso ζ κ Y).hom := by
  apply (Over.forget U).map_injective
  change ((scalar_tower_iso ζ κ X).hom ≫ chosenScalarArrow (ζ ≫ κ) f).left =
    (chosenScalarArrow ζ (chosenScalarArrow κ f) ≫ (scalar_tower_iso ζ κ Y).hom).left
  apply pullback.hom_ext
  · exact ((scalar_tower_iso ζ κ X).hom ≫ chosenScalarArrow (ζ ≫ κ) f).w.trans
      (chosenScalarArrow ζ (chosenScalarArrow κ f) ≫ (scalar_tower_iso ζ κ Y).hom).w.symm
  · exact compare_projection
      (scalar_tower_iso ζ κ X).hom.left (scalar_tower_iso ζ κ Y).hom.left
      (chosenScalarArrow (ζ ≫ κ) f).left (chosenScalarArrow ζ (chosenScalarArrow κ f)).left
      (pullback.snd (ζ ≫ κ) X.hom) (pullback.snd (ζ ≫ κ) Y.hom)
      (pullback.snd ζ (scalar_model κ X).hom ≫ pullback.snd κ X.hom)
      (pullback.snd ζ (scalar_model κ Y).hom ≫ pullback.snd κ Y.hom) f.left
      (scalar_tower_original ζ κ X) (scalar_tower_original ζ κ Y)
      (chosenScalarArrow_snd (ζ ≫ κ) f)
      (compose_projection (chosenScalarArrow ζ (chosenScalarArrow κ f)).left
        (pullback.snd ζ (scalar_model κ Y).hom) (pullback.snd ζ (scalar_model κ X).hom)
        (chosenScalarArrow κ f).left (pullback.snd κ X.hom) (pullback.snd κ Y.hom) f.left
        (chosenScalarArrow_snd ζ (chosenScalarArrow κ f)) (chosenScalarArrow_snd κ f))
private theorem scalar_tower_gc {B T U : Scheme.{u}}
    (ζ : U ⟶ T) (κ : T ⟶ B) {X Y : Over B} (f : X ⟶ Y)
    (h : GeometricallyConnected
      (chosenScalarArrow ζ (chosenScalarArrow κ f)).left) :
    GeometricallyConnected (chosenScalarArrow (ζ ≫ κ) f).left := by
  have hpost : GeometricallyConnected
      ((chosenScalarArrow ζ (chosenScalarArrow κ f)).left ≫
        (scalar_tower_iso ζ κ Y).hom.left) :=
    (MorphismProperty.cancel_right_of_respectsIso (@GeometricallyConnected)
      _ (scalar_tower_iso ζ κ Y).hom.left).mpr h
  have hpre : GeometricallyConnected
      ((scalar_tower_iso ζ κ X).hom.left ≫ (chosenScalarArrow (ζ ≫ κ) f).left) :=
    (congrArg (fun t => GeometricallyConnected t.left) (scalar_tower_natural ζ κ f)).mpr hpost
  exact (MorphismProperty.cancel_left_of_respectsIso (@GeometricallyConnected)
    (scalar_tower_iso ζ κ X).hom.left _).mp hpre

private theorem change_scalar_gc {B T : Scheme.{u}} {κ ζ : T ⟶ B} (h : κ = ζ)
    {X Y : Over B} (f : X ⟶ Y) (hf : GeometricallyConnected (chosenScalarArrow κ f).left) :
    GeometricallyConnected (chosenScalarArrow ζ f).left := by
  subst ζ
  exact hf

private theorem spec_triangle {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    (f : R →+* A) (g : A →+* B) (h : R →+* B) (hgf : g.comp f = h) :
    Spec.map (CommRingCat.ofHom g) ≫ Spec.map (CommRingCat.ofHom f) =
      Spec.map (CommRingCat.ofHom h) := by
  rw [← Spec.map_comp]
  exact congrArg (fun k : R →+* B => Spec.map (CommRingCat.ofHom k)) hgf

private theorem field_connected {X Y : Scheme.{u}} (f : X ⟶ Y)
    [GeometricallyConnected f] (L : Type u) [Field L] (y : Spec (.of L) ⟶ Y) :
    ConnectedSpace (pullback f y : Scheme.{u}) := by
  let : GeometricallyConnected (pullback.snd f y) := inferInstance
  exact GeometricallyConnected.connectedSpace_of_subsingleton (pullback.snd f y)

private def endpoint_result {K : Type u} [CommRing K] (S : Subalgebra ℤ K)
    {N Z : Over (Spec (.of S))} (m : N ⟶ Z) (start : CoefficientStage S) : Prop :=
  ∃ (k : CoefficientStage S) (_ : start ≤ k),
    let κ := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom)
    let mk := chosenScalarArrow κ m
    (mk.left ≫ (stageScalarModel S Z.hom k).hom = (stageScalarModel S N.hom k).hom) ∧
    (mk.left ≫ pullback.snd κ Z.hom = pullback.snd κ N.hom ≫ m.left) ∧
    GeometricallyConnected mk.left ∧
    ∀ (L : Type u) [Field L] (y : Spec (.of L) ⟶ (stageScalarModel S Z.hom k).left),
      ConnectedSpace (pullback mk.left y : Scheme.{u})

private theorem finish_original {K : Type u} [CommRing K] (S : Subalgebra ℤ K)
    {N Z : Over (Spec (.of S))} (m : N ⟶ Z)
    (start R : CoefficientStage S) (hstart : start ≤ R)
    (t : CoefficientStage R.val)
    (ht : GeometricallyConnected (chosenScalarArrow
      (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion t.property.2).toRingHom))
      (chosenScalarArrow
        (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion R.property.2).toRingHom)) m)).left) :
    endpoint_result S m start := by
  let k : CoefficientStage S := ⟨t.val, t.property.1, R.property.2.trans t.property.2⟩
  let κ := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion R.property.2).toRingHom)
  let ζ := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion t.property.2).toRingHom)
  let μ := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom)
  have hζκ : ζ ≫ κ = μ := spec_triangle _ _ _ (by ext x; rfl)
  have hgc : GeometricallyConnected (chosenScalarArrow μ m).left :=
    change_scalar_gc hζκ m (scalar_tower_gc ζ κ m ht)
  let : GeometricallyConnected (chosenScalarArrow μ m).left := hgc
  exact ⟨k, hstart.trans t.property.2, (chosenScalarArrow μ m).w,
    chosenScalarArrow_snd μ m, hgc, fun L _ y =>
      @field_connected _ _ (chosenScalarArrow μ m).left hgc L inferInstance y⟩

private theorem finish_result {K : Type u} [CommRing K] (S : Subalgebra ℤ K)
    {N Z : Over (Spec (.of S))} (m : N ⟶ Z)
    (start R : CoefficientStage S) (hstart : start ≤ R)
    (h : endpoint_result R.val (chosenScalarArrow
      (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion R.property.2).toRingHom)) m)
      ⟨R.val, R.property.1, le_rfl⟩) : endpoint_result S m start := by
  obtain ⟨t, _, _, _, hgc, _⟩ := h
  exact finish_original S m start R hstart t hgc

private theorem apply_schubert_stage
    {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (S : Subalgebra ℤ K) (G : ReductiveGroupData K)
    (word : List G.rootBase.support) (v : G.weylGroup) (i : G.rootBase.support)
    {J : Type v} [Fintype J] (x : J → G.weylGroup)
    (hv : (weylCoxeterSystem G.rootBase).length v <
      (weylCoxeterSystem G.rootBase).length
        (v * RootPairing.weylGroup.ofIdx G.rootSystem i.val))
    (hx : ∀ r, WeylBruhatLE G.rootBase (x r)
      (v * RootPairing.weylGroup.ofIdx G.rootSystem i.val))
    {N A Y Z F Q : Over (Spec (.of S))}
    [LocallyOfFinitePresentation N.hom] [QuasiCompact N.hom]
    [LocallyOfFinitePresentation A.hom] [QuasiCompact A.hom]
    [LocallyOfFinitePresentation F.hom] [QuasiCompact F.hom]
    [LocallyOfFinitePresentation Q.hom]
    (f : A ⟶ Y) [IsProper f.left] [GeometricallyConnected f.left]
    (j : Y ⟶ F) [IsClosedImmersion j.left]
    (m : N ⟶ Z) (z : Z ⟶ F) [IsClosedImmersion z.left] (π : F ⟶ Q)
    [LocallyOfFinitePresentation π.left] [QuasiCompact π.left] [IsSeparated π.left]
    (qN : bsdhScheme G (word ++ [i]) ⟶ N.left)
    (qA : bsdhScheme G word ⟶ A.left)
    (qY : (schubertVariety G v).scheme ⟶ Y.left)
    (qZ : (schubertVariety G (v * RootPairing.weylGroup.ofIdx G.rootSystem i.val)).scheme ⟶ Z.left)
    (qF : (flagVariety G).scheme ⟶ F.left)
    (qQ : (partialFlagVariety G {i}).scheme ⟶ Q.left)
    (hN : IsPullback qN (bsdhToSpec G (word ++ [i])) N.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hA : IsPullback qA (bsdhToSpec G word) A.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hY : IsPullback qY (schubertVariety G v).toSpec Y.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hF : IsPullback qF (flagVariety G).toSpec F.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hQ : IsPullback qQ (partialFlagVariety G {i}).toSpec Q.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hn : qN ≫ (m ≫ z).left = bsdhMap G (word ++ [i]) ≫ qF)
    (ha : bsdhMap G word ≫ qF = qA ≫ (f ≫ j).left)
    (hj : (schubertInclusion G v).left ≫ qF = qY ≫ j.left)
    (hz : qZ ≫ z.left =
      (schubertInclusion G (v * RootPairing.weylGroup.ofIdx G.rootSystem i.val)).left ≫ qF)
    (hπ : IsPullback (partialFlagMorphism G {i}).left qF qQ π.left)
    (start r R : CoefficientStage S) (hstart : start ≤ R) (hrR : r ≤ R)
    (p : ∀ _t : J, (schubertVariety G
      (v * RootPairing.weylGroup.ofIdx G.rootSystem i.val)).points)
    (b₀ : ∀ _t : J, Spec (.of r.val) ⟶ Z.left)
    (hp : ∀ t, (p t).val ≫ (schubertInclusion G
      (v * RootPairing.weylGroup.ofIdx G.rootSystem i.val)).left = (weylFlagPoint G (x t)).val)
    (hb₀ : ∀ t, b₀ t ≫ Z.hom = Spec.map
      (CommRingCat.ofHom (Subalgebra.inclusion r.property.2).toRingHom))
    (he₀ : ∀ t, (p t).val ≫ qZ =
      Spec.map (CommRingCat.ofHom (algebraMap r.val K)) ≫ b₀ t)
    (C : J → Over (Spec (.of R.val))) [∀ t, CompactSpace (C t).left]
    [∀ t, LocallyOfFinitePresentation (C t).hom]
    (c : ∀ t, C t ⟶ stageScalarModel S Z.hom R)
    (qC : ∀ t, (schubertCell G (x t)).scheme ⟶ (C t).left)
    (hC : ∀ t, IsPullback (qC t) (schubertCell G (x t)).toSpec (C t).hom
      (Spec.map (CommRingCat.ofHom (algebraMap R.val K))))
    (qZR : (schubertVariety G (v * RootPairing.weylGroup.ofIdx G.rootSystem i.val)).scheme ⟶
      (stageScalarModel S Z.hom R).left)
    (hZR : IsPullback qZR
      (schubertVariety G (v * RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toSpec
      (stageScalarModel S Z.hom R).hom
      (Spec.map (CommRingCat.ofHom (algebraMap R.val K))))
    (hZo : qZR ≫ pullback.snd
      (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion R.property.2).toRingHom)) Z.hom = qZ)
    (hc : ∀ t, qC t ≫ (c t).left =
      (schubertCellOfLE G (x t)
        (v * RootPairing.weylGroup.ofIdx G.rootSystem i.val) (hx t)).left ≫ qZR)
    (hcover : ∀ k : CoefficientStage R.val,
      ∀ y : (stageScalarModel R.val (stageScalarModel S Z.hom R).hom k).left,
        ∃ t, y ∈ Set.range (chosenScalarArrow
          (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom))
            (c t)).left) : endpoint_result S m start := by
  let κ : Spec (.of R.val) ⟶ Spec (.of S) :=
    Spec.map (CommRingCat.ofHom (Subalgebra.inclusion R.property.2).toRingHom)
  let ρ : Spec (.of K) ⟶ Spec (.of R.val) :=
    Spec.map (CommRingCat.ofHom (algebraMap R.val K))
  let β : Spec (.of R.val) ⟶ Spec (.of r.val) :=
    Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hrR).toRingHom)
  let κr : Spec (.of r.val) ⟶ Spec (.of S) :=
    Spec.map (CommRingCat.ofHom (Subalgebra.inclusion r.property.2).toRingHom)
  have hβ : β ≫ κr = κ := spec_triangle _ _ _ (by ext t; rfl)
  have hρβ : ρ ≫ β = Spec.map (CommRingCat.ofHom (algebraMap r.val K)) :=
    spec_triangle _ _ _ (by ext t; rfl)
  let NR : Over (Spec (.of R.val)) := stageScalarModel S N.hom R
  let AR : Over (Spec (.of R.val)) := stageScalarModel S A.hom R
  let YR : Over (Spec (.of R.val)) := stageScalarModel S Y.hom R
  let ZR : Over (Spec (.of R.val)) := stageScalarModel S Z.hom R
  let FR : Over (Spec (.of R.val)) := stageScalarModel S F.hom R
  let QR : Over (Spec (.of R.val)) := stageScalarModel S Q.hom R
  let fR : AR ⟶ YR := chosenScalarArrow κ f
  let jR : YR ⟶ FR := chosenScalarArrow κ j
  let mR : NR ⟶ ZR := chosenScalarArrow κ m
  let zR : ZR ⟶ FR := chosenScalarArrow κ z
  let πR : FR ⟶ QR := chosenScalarArrow κ π
  let bZR (t : J) : Over.mk (𝟙 (Spec (.of R.val))) ⟶ ZR :=
    lifted_section κ β κr Z (b₀ t) (hb₀ t) hβ
  let bR (t : J) : Over.mk (𝟙 (Spec (.of R.val))) ⟶ FR := bZR t ≫ zR
  let qNR := stage_map S N (Over.mk (bsdhToSpec G (word ++ [i]))) qN hN R
  let qAR := stage_map S A (Over.mk (bsdhToSpec G word)) qA hA R
  let qYR := stage_map S Y (schubertVariety G v).toOver qY hY R
  let qFR := stage_map S F (flagVariety G).toOver qF hF R
  let qQR := stage_map S Q (partialFlagVariety G {i}).toOver qQ hQ R
  have hNR := stage_map_cartesian S N (Over.mk (bsdhToSpec G (word ++ [i]))) qN hN R
  have hAR := stage_map_cartesian S A (Over.mk (bsdhToSpec G word)) qA hA R
  have hYR := stage_map_cartesian S Y (schubertVariety G v).toOver qY hY R
  have hFR := stage_map_cartesian S F (flagVariety G).toOver qF hF R
  have hQR := stage_map_cartesian S Q (partialFlagVariety G {i}).toOver qQ hQ R
  have hNo := stage_map_original S N (Over.mk (bsdhToSpec G (word ++ [i]))) qN hN R
  have hAo := stage_map_original S A (Over.mk (bsdhToSpec G word)) qA hA R
  have hYo := stage_map_original S Y (schubertVariety G v).toOver qY hY R
  have hFo := stage_map_original S F (flagVariety G).toOver qF hF R
  have hQo := stage_map_original S Q (partialFlagVariety G {i}).toOver qQ hQ R
  have hnR : qNR ≫ (mR ≫ zR).left = bsdhMap G (word ++ [i]) ≫ qFR :=
    scalar_composite_comparison κ m z _ qNR qFR
      (scalar_comparison (U := Over.mk (bsdhToSpec G (word ++ [i])))
        (V := (flagVariety G).toOver) κ ρ (m ≫ z) (Over.homMk (bsdhMap G (word ++ [i])) rfl)
        qN qF qNR qFR hNR hFR hNo hFo hn)
  have haR : bsdhMap G word ≫ qFR = qAR ≫ (fR ≫ jR).left :=
    (scalar_composite_comparison κ f j _ qAR qFR
      (scalar_comparison (U := Over.mk (bsdhToSpec G word))
        (V := (flagVariety G).toOver) κ ρ (f ≫ j) (Over.homMk (bsdhMap G word) rfl)
        qA qF qAR qFR hAR hFR hAo hFo ha.symm)).symm
  have hjR : (schubertInclusion G v).left ≫ qFR = qYR ≫ jR.left :=
    (scalar_comparison (U := (schubertVariety G v).toOver)
        (V := (flagVariety G).toOver) κ ρ j (schubertInclusion G v)
      qY qF qYR qFR hYR hFR hYo hFo hj.symm).symm
  have hzR : qZR ≫ zR.left = (schubertInclusion G
      (v * RootPairing.weylGroup.ofIdx G.rootSystem i.val)).left ≫ qFR :=
    scalar_comparison
      (U := (schubertVariety G (v * RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver)
      (V := (flagVariety G).toOver) κ ρ z
      (schubertInclusion G (v * RootPairing.weylGroup.ofIdx G.rootSystem i.val))
      qZ qF qZR qFR hZR hFR hZo hFo hz
  have hπR : IsPullback (partialFlagMorphism G {i}).left qFR qQR πR.left :=
    scalar_square κ π (partialFlagMorphism G {i}) qF qQ hπ qFR qQR hFo hQo
      (scalar_comparison (U := (flagVariety G).toOver)
        (V := (partialFlagVariety G {i}).toOver) κ ρ π (partialFlagMorphism G {i})
        qF qQ qFR qQR hFR hQR hFo hQo hπ.w.symm)
  have hbR (t : J) : (weylFlagPoint G (x t)).val ≫ qFR = ρ ≫ (bR t).left :=
    (point_image (p t).val _ (weylFlagPoint G (x t)).val qZR qFR zR.left
      (ρ ≫ (bZR t).left) (hp t) hzR
      (lifted_section_comparison κ β κr ρ
        (Spec.map (CommRingCat.ofHom (algebraMap r.val K))) Z
        (schubertVariety G (v * RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver
        qZ qZR hZR hZo
        (b₀ t) (hb₀ t) hβ (p t).val (p t).property (he₀ t) hρβ)).trans
      (Category.assoc _ _ _)
  have hcR (t : J) : (schubertCellInclusion G (x t)).left ≫ qFR =
      qC t ≫ (c t ≫ zR).left :=
    cell_image _ _ _ (qC t) qZR qFR (c t).left zR.left
      (congrArg Over.Hom.left (schubertCellOfLE_comp G (x t)
        (v * RootPairing.weylGroup.ofIdx G.rootSystem i.val) (hx t))) (hc t) hzR
  let : LocallyOfFinitePresentation NR.hom := scalar_fp κ N
  let : QuasiCompact NR.hom := scalar_qc κ N
  let : LocallyOfFinitePresentation AR.hom := scalar_fp κ A
  let : QuasiCompact AR.hom := scalar_qc κ A
  let : LocallyOfFinitePresentation FR.hom := scalar_fp κ F
  let : QuasiCompact FR.hom := scalar_qc κ F
  let : LocallyOfFinitePresentation QR.hom := scalar_fp κ Q
  let : IsProper fR.left := scalar_property (@IsProper) κ f inferInstance
  let : GeometricallyConnected fR.left :=
    scalar_property (@GeometricallyConnected) κ f inferInstance
  let : IsClosedImmersion jR.left := scalar_property (@IsClosedImmersion) κ j inferInstance
  let : IsClosedImmersion zR.left := scalar_property (@IsClosedImmersion) κ z inferInstance
  let : LocallyOfFinitePresentation πR.left :=
    scalar_property (@LocallyOfFinitePresentation) κ π inferInstance
  let : QuasiCompact πR.left := scalar_property (@QuasiCompact) κ π inferInstance
  let : IsSeparated πR.left := scalar_property (@IsSeparated) κ π inferInstance
  exact finish_result S m start R hstart
    (exists_append_cell_connected R.val R.property.1 G word v i x hv hx fR jR mR zR πR
      bR C c qNR qAR qYR qFR qQR qC hNR hAR hYR hFR hQR hC
      hnR haR hjR hπR hbR hcR hcover ⟨R.val, R.property.1, le_rfl⟩)

/-- The appended endpoint on specified arithmetic models acquires connected
geometric fibres above a coefficient extension. The lower-cell cover and Weyl
sections are constructed from its Schubert comparison; the shorter endpoint
provides the proper connected-fibre induction hypothesis. -/
theorem exists_append_schubert_connected
    {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (S : Subalgebra ℤ K) (hS : S.FG) (G : ReductiveGroupData K)
    (word : List G.rootBase.support) (v : G.weylGroup) (i : G.rootBase.support)
    (hv : (weylCoxeterSystem G.rootBase).length v <
      (weylCoxeterSystem G.rootBase).length
        (v * RootPairing.weylGroup.ofIdx G.rootSystem i.val))
    {N A Y Z F Q : Over (Spec (.of S))}
    [LocallyOfFinitePresentation N.hom] [QuasiCompact N.hom]
    [LocallyOfFinitePresentation A.hom] [QuasiCompact A.hom]
    [LocallyOfFinitePresentation Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    [LocallyOfFinitePresentation F.hom] [QuasiCompact F.hom]
    [LocallyOfFinitePresentation Q.hom]
    (f : A ⟶ Y) [IsProper f.left] [GeometricallyConnected f.left]
    (j : Y ⟶ F) [IsClosedImmersion j.left]
    (m : N ⟶ Z) (z : Z ⟶ F) [IsClosedImmersion z.left] (π : F ⟶ Q)
    [LocallyOfFinitePresentation π.left] [QuasiCompact π.left] [IsSeparated π.left]
    (qN : bsdhScheme G (word ++ [i]) ⟶ N.left)
    (qA : bsdhScheme G word ⟶ A.left)
    (qY : (schubertVariety G v).scheme ⟶ Y.left)
    (qZ : (schubertVariety G (v * RootPairing.weylGroup.ofIdx G.rootSystem i.val)).scheme ⟶ Z.left)
    (qF : (flagVariety G).scheme ⟶ F.left)
    (qQ : (partialFlagVariety G {i}).scheme ⟶ Q.left)
    (hN : IsPullback qN (bsdhToSpec G (word ++ [i])) N.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hA : IsPullback qA (bsdhToSpec G word) A.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hY : IsPullback qY (schubertVariety G v).toSpec Y.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hZ : IsPullback qZ
      (schubertVariety G (v * RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toSpec Z.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hF : IsPullback qF (flagVariety G).toSpec F.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hQ : IsPullback qQ (partialFlagVariety G {i}).toSpec Q.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hn : qN ≫ (m ≫ z).left = bsdhMap G (word ++ [i]) ≫ qF)
    (ha : bsdhMap G word ≫ qF = qA ≫ (f ≫ j).left)
    (hj : (schubertInclusion G v).left ≫ qF = qY ≫ j.left)
    (hz : qZ ≫ z.left =
      (schubertInclusion G (v * RootPairing.weylGroup.ofIdx G.rootSystem i.val)).left ≫ qF)
    (hπ : IsPullback (partialFlagMorphism G {i}).left qF qQ π.left)
    (start : CoefficientStage S) :
    ∃ (k : CoefficientStage S) (_ : start ≤ k),
      let κ := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom)
      let mk := chosenScalarArrow κ m
      (mk.left ≫ (stageScalarModel S Z.hom k).hom = (stageScalarModel S N.hom k).hom) ∧
      (mk.left ≫ pullback.snd κ Z.hom = pullback.snd κ N.hom ≫ m.left) ∧
      GeometricallyConnected mk.left ∧
      ∀ (L : Type u) [Field L] (y : Spec (.of L) ⟶ (stageScalarModel S Z.hom k).left),
        ConnectedSpace (pullback mk.left y : Scheme.{u}) := by
  let u₁ := v * RootPairing.weylGroup.ofIdx G.rootSystem i.val
  let J := {w : G.weylGroup // WeylBruhatLE G.rootBase w u₁}
  let : Finite G.weylGroup := ReductiveGroups.weylGroup_finite G.rootBase
  let : Fintype J := Fintype.ofFinite J
  let x (t : J) : G.weylGroup := t.val
  let E : (schubertVariety G u₁).toOver ≅ genericScalarModel S Z.hom :=
    Over.isoMk hZ.flip.isoPullback hZ.flip.isoPullback_hom_fst
  exact bind_exists
    (exists_schubert_weyl_sections S hS G x (fun _ => u₁) (fun t => t.property)
      (fun _ => Z) (fun _ => qZ) (fun _ => hZ.w)) (fun r hr =>
    bind_exists hr (fun p hp => bind_exists hp (fun b hb =>
      bound_stages r start (fun s hrs hstarts =>
        bind_exists (exists_schubert_cover_models S hS G u₁ Z qZ hZ s) (fun R hR =>
          bind_exists hR.2 (fun c hc =>
            let _ : ∀ t : J, CompactSpace
                (stageScalarModel S
                  (cellPolynomialModel S ((weylCoxeterSystem G.rootBase).length t.val)).hom R).left
                    :=
              hc.1
            let _ : ∀ t : J, LocallyOfFinitePresentation
                (stageScalarModel S
                  (cellPolynomialModel S ((weylCoxeterSystem G.rootBase).length t.val)).hom R).hom
                    :=
              hc.2.1
            apply_schubert_stage S G word v i x hv (fun t => t.property) f j m z π
              qN qA qY qZ qF qQ hN hA hY hF hQ hn ha hj hz hπ start r R
              (hstarts.trans hR.1) (hrs.trans hR.1) p b hb.1 hb.2.1 hb.2.2
              (fun t => stageScalarModel S
                (cellPolynomialModel S ((weylCoxeterSystem G.rootBase).length t.val)).hom R)
              c (fun t => (cellModelIso S G t.val).hom.left ≫
                (modelScalarCone S
                  (cellPolynomialModel S ((weylCoxeterSystem G.rootBase).length t.val)).hom).π.app
                    (op R)) hc.2.2.1
              (E.hom.left ≫ (modelScalarCone S Z.hom).π.app (op R)) hc.2.2.2.1
              hc.2.2.2.2.1 hc.2.2.2.2.2.1 hc.2.2.2.2.2.2))))))

-- GAP: C6-STAGE. Iterate this coefficient-retaining step on the chosen word
-- models, with their base endpoint and proper structural maps.

end SchubertGeometry
