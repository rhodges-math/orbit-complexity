import OrbitComplexity.FrobeniusSplitting.Normality.Limits.ModelIsoDescent
import OrbitComplexity.FrobeniusSplitting.Normality.Connectedness.SectionRetention
import OrbitComplexity.FrobeniusSplitting.Normality.Connectedness.ModelStageCartesian
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Pointed affine isomorphisms at coefficient stages

An affine isomorphism in the generic fibre, together with an endpoint equation
and a rational section, descends with all three properties at one coefficient
stage. The original source and target projections are retained.
-/

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace FrobeniusSplitting

universe u

open private model_scalar_original from
  OrbitComplexity.FrobeniusSplitting.Normality.Connectedness.ModelStageCartesian

private theorem inverse_over_maps {B T : Scheme.{u}} (κ : T ⟶ B)
    {X Y : Over B} {XT YT : Over T}
    (qX : XT.left ⟶ X.left) (qY : YT.left ⟶ Y.left)
    (hX : IsPullback qX XT.hom X.hom κ)
    (f : X ⟶ Y) (g : Y ⟶ X) (hfg : f ≫ g = 𝟙 X)
    (fT : XT ⟶ YT) (gT : YT ⟶ XT)
    (hf : fT.left ≫ qY = qX ≫ f.left)
    (hg : gT.left ≫ qX = qY ≫ g.left) : fT ≫ gT = 𝟙 XT := by
  apply CostructuredArrow.hom_ext
  apply hX.hom_ext
  · change (fT.left ≫ gT.left) ≫ qX = qX
    calc
      (fT.left ≫ gT.left) ≫ qX = fT.left ≫ (gT.left ≫ qX) := Category.assoc _ _ _
      _ = fT.left ≫ (qY ≫ g.left) := congrArg (fun k => fT.left ≫ k) hg
      _ = (fT.left ≫ qY) ≫ g.left := (Category.assoc _ _ _).symm
      _ = (qX ≫ f.left) ≫ g.left := congrArg (fun k => k ≫ g.left) hf
      _ = qX ≫ (f ≫ g).left := Category.assoc _ _ _
      _ = qX ≫ (𝟙 X.left) := congrArg (fun k : X ⟶ X => qX ≫ k.left) hfg
      _ = qX := Category.comp_id _
  · simp

private def extendStageIso {K : Type u} [CommRing K]
    (S : Subalgebra ℤ K) {X Y : Scheme.{u}}
    (a : X ⟶ Spec (.of S)) (b : Y ⟶ Spec (.of S))
    {i j : CoefficientStage S} (hij : i ≤ j)
    (E : stageScalarModel S a i ≅ stageScalarModel S b i) :
    stageScalarModel S a j ≅ stageScalarModel S b j where
  hom := extendModelMorphism S a b hij E.hom
  inv := extendModelMorphism S b a hij E.inv
  hom_inv_id := inverse_over_maps _ _ _ (stageScalarCartesian S a hij)
    E.hom E.inv E.hom_inv_id _ _
    (extendModelMorphism_transition S a b hij E.hom)
    (extendModelMorphism_transition S b a hij E.inv)
  inv_hom_id := inverse_over_maps _ _ _ (stageScalarCartesian S b hij)
    E.inv E.hom E.inv_hom_id _ _
    (extendModelMorphism_transition S b a hij E.inv)
    (extendModelMorphism_transition S a b hij E.hom)

private theorem iso_old_base {B T : Scheme.{u}} (κ : T ⟶ B)
    {X Y : Scheme.{u}} (x : X ⟶ B) (y : Y ⟶ B) {XT YT : Over T} (E : XT ≅ YT)
    (qX : XT.left ⟶ X) (qY : YT.left ⟶ Y)
    (hX : qX ≫ x = XT.hom ≫ κ) (hY : qY ≫ y = YT.hom ≫ κ) :
    E.hom.left ≫ qY ≫ y = qX ≫ x := by
  calc
    E.hom.left ≫ qY ≫ y = E.hom.left ≫ (YT.hom ≫ κ) :=
      congrArg (fun k => E.hom.left ≫ k) hY
    _ = (E.hom.left ≫ YT.hom) ≫ κ := (Category.assoc _ _ _).symm
    _ = XT.hom ≫ κ := congrArg (fun k => k ≫ κ) E.hom.w
    _ = qX ≫ x := hX.symm

private theorem retain_iso_triangle {A B A' B' Z : Scheme.{u}}
    (E : A ≅ B) (E' : A' ≅ B') (u : A' ⟶ A) (v : B' ⟶ B)
    (qA : A ⟶ Z) (qB : B ⟶ Z) (qA' : A' ⟶ Z) (qB' : B' ⟶ Z)
    (hE : E'.hom ≫ v = u ≫ E.hom)
    (hA : u ≫ qA = qA') (hB : v ≫ qB = qB')
    (h : u ≫ E.hom ≫ qB = u ≫ qA) : E'.hom ≫ qB' = qA' := by
  calc
    E'.hom ≫ qB' = E'.hom ≫ (v ≫ qB) := congrArg (fun k => E'.hom ≫ k) hB.symm
    _ = (E'.hom ≫ v) ≫ qB := (Category.assoc _ _ _).symm
    _ = (u ≫ E.hom) ≫ qB := congrArg (fun k => k ≫ qB) hE
    _ = u ≫ qA := (Category.assoc _ _ _).trans h
    _ = qA' := hA

private theorem generic_endpoint_triangle
    {A B A' B' X Y Z : Scheme.{u}}
    (πA : A' ⟶ A) (πB : B' ⟶ B) (E : A' ⟶ B') (E0 : A ⟶ B)
    (qA : A ⟶ X) (qB : B ⟶ Y) (rA : A' ⟶ X) (rB : B' ⟶ Y)
    (u : X ⟶ Z) (v : Y ⟶ Z)
    (hE : πA ≫ E0 = E ≫ πB) (hA : πA ≫ qA = rA) (hB : πB ≫ qB = rB)
    (h : E ≫ rB ≫ v = rA ≫ u) : πA ≫ E0 ≫ qB ≫ v = πA ≫ qA ≫ u := by
  calc
    πA ≫ E0 ≫ qB ≫ v = (πA ≫ E0) ≫ qB ≫ v := (Category.assoc _ _ _).symm
    _ = (E ≫ πB) ≫ qB ≫ v := congrArg (fun k => k ≫ qB ≫ v) hE
    _ = E ≫ (πB ≫ qB) ≫ v := by simp only [Category.assoc]
    _ = E ≫ rB ≫ v := congrArg (fun k => E ≫ k ≫ v) hB
    _ = rA ≫ u := h
    _ = (πA ≫ qA) ≫ u := congrArg (fun k => k ≫ u) hA.symm
    _ = πA ≫ qA ≫ u := Category.assoc _ _ _

private theorem section_extension {B T X Y : Scheme.{u}}
    (κ : T ⟶ B) (q : Y ⟶ X) (x : X ⟶ B) (y : Y ⟶ T)
    (h : IsPullback q y x κ) (s : B ⟶ X) (hs : s ≫ x = 𝟙 B) :
    ∃ t : T ⟶ Y, t ≫ y = 𝟙 T := by
  let t := h.lift (κ ≫ s) (𝟙 T) (by simp [Category.assoc, hs])
  exact ⟨t, h.lift_snd _ _ _⟩

/-- A pointed generic isomorphism between two affine model opens descends with
its section and its endpoint equation at one coefficient stage. -/
theorem exists_pointed_iso_stage {K : Type u} [CommRing K]
    (S : Subalgebra ℤ K) (hS : S.FG) (C F : Over (Spec (.of S)))
    [LocallyOfFinitePresentation C.hom] [LocallyOfFinitePresentation F.hom]
    (e : C ⟶ F) (U : C.left.Opens) (hU : IsAffineOpen U)
    (V : F.left.Opens) (hV : IsAffineOpen V)
    (E : genericScalarModel S (U.ι ≫ C.hom) ≅ genericScalarModel S (V.ι ≫ F.hom))
    (hE : E.hom.left ≫ pullback.snd
        (Spec.map (CommRingCat.ofHom (algebraMap S K))) (V.ι ≫ F.hom) ≫ V.ι =
      pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap S K)))
        (U.ι ≫ C.hom) ≫ U.ι ≫ e.left)
    (s : Spec (.of K) ⟶ (genericScalarModel S (V.ι ≫ F.hom)).left)
    (hs : s ≫ (genericScalarModel S (V.ι ≫ F.hom)).hom = 𝟙 _)
    (start : CoefficientStage S) :
    ∃ (t : CoefficientStage S) (_ : start ≤ t)
      (Et : stageScalarModel S (U.ι ≫ C.hom) t ≅ stageScalarModel S (V.ι ≫ F.hom) t)
      (st : Spec (.of t.val) ⟶ (stageScalarModel S (V.ι ≫ F.hom) t).left),
      st ≫ (stageScalarModel S (V.ι ≫ F.hom) t).hom = 𝟙 _ ∧
      Et.hom.left ≫ pullback.snd
          (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion t.property.2).toRingHom))
          (V.ι ≫ F.hom) ≫ V.ι =
        pullback.snd
          (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion t.property.2).toRingHom))
          (U.ι ≫ C.hom) ≫ U.ι ≫ e.left := by
  let : IsAffine U.toScheme := hU
  let : IsAffine V.toScheme := hV
  obtain ⟨i, Ei, hi, _⟩ := exists_model_iso S hS (U.ι ≫ C.hom) (V.ι ≫ F.hom) E
  obtain ⟨j, hij, hstart⟩ := exists_ge_ge i start
  let P : Unit → Scheme.{u} := fun _ => V.toScheme
  let a : ∀ r : Unit, P r ⟶ Spec (.of S) := fun _ => V.ι ≫ F.hom
  let sp : ∀ r : Unit, Spec (.of K) ⟶ (genericScalarModel S (a r)).left := fun _ => s
  have hsp (r : Unit) : sp r ≫ (genericScalarModel S (a r)).hom = 𝟙 _ := hs
  obtain ⟨k, hjk, sk, hsk⟩ := exists_retained_sections S hS P a sp hsp j
  let Ek := extendStageIso S (U.ι ≫ C.hom) (V.ι ≫ F.hom) (hij.trans hjk) Ei
  let sk0 := stageOriginSection S (𝟙 (Spec (.of S))) (𝟙 _) (Category.id_comp _) k ≫
    (sk ()).left
  have hsk0 : sk0 ≫ (stageScalarModel S (V.ι ≫ F.hom) k).hom = 𝟙 _ := (hsk ()).2.1
  let β := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom)
  let qA : (stageScalarModel S (U.ι ≫ C.hom) k).left ⟶ U.toScheme :=
    pullback.snd β (U.ι ≫ C.hom)
  let qB : (stageScalarModel S (V.ι ≫ F.hom) k).left ⟶ V.toScheme :=
    pullback.snd β (V.ι ≫ F.hom)
  let f : (stageScalarModel S (U.ι ≫ C.hom) k).left ⟶ F.left := Ek.hom.left ≫ qB ≫ V.ι
  let g : (stageScalarModel S (U.ι ≫ C.hom) k).left ⟶ F.left := qA ≫ U.ι ≫ e.left
  have hbase : (modelScalarBase S (U.ι ≫ C.hom)).app (op k) = qA ≫ (U.ι ≫ C.hom) := rfl
  have hf : f ≫ F.hom = (modelScalarBase S (U.ι ≫ C.hom)).app (op k) := by
    simpa only [f, Category.assoc] using
      (iso_old_base β (U.ι ≫ C.hom) (V.ι ≫ F.hom) Ek qA qB
        (pullback.condition.symm) (pullback.condition.symm)).trans hbase.symm
  have hg : g ≫ F.hom = (modelScalarBase S (U.ι ≫ C.hom)).app (op k) := by
    exact (Category.assoc qA (U.ι ≫ e.left) F.hom).trans
      (congrArg (fun z => qA ≫ z)
        ((Category.assoc U.ι e.left F.hom).trans (congrArg (fun z => U.ι ≫ z) e.w)))
  have hEk : (modelScalarCone S (U.ι ≫ C.hom)).π.app (op k) ≫ Ek.hom.left =
      E.hom.left ≫ (modelScalarCone S (V.ι ≫ F.hom)).π.app (op k) :=
    (congrArg (fun z : stageScalarModel S (U.ι ≫ C.hom) k ⟶
        stageScalarModel S (V.ι ≫ F.hom) k =>
        (modelScalarCone S (U.ι ≫ C.hom)).π.app (op k) ≫ z.left)
      (show Ek.hom = extendModelMorphism S (U.ι ≫ C.hom) (V.ι ≫ F.hom)
        (hij.trans hjk) Ei.hom from rfl)).trans
      (extendModelMorphism_baseChange S (U.ι ≫ C.hom) (V.ι ≫ F.hom)
        (hij.trans hjk) Ei.hom E.hom hi)
  have hfg : (modelScalarCone S (U.ι ≫ C.hom)).π.app (op k) ≫ f =
      (modelScalarCone S (U.ι ≫ C.hom)).π.app (op k) ≫ g :=
    generic_endpoint_triangle
      ((modelScalarCone S (U.ι ≫ C.hom)).π.app (op k))
      ((modelScalarCone S (V.ι ≫ F.hom)).π.app (op k)) E.hom.left Ek.hom.left
      qA qB _ _ (U.ι ≫ e.left) V.ι hEk
      (model_scalar_original S (U.ι ≫ C.hom) k)
      (model_scalar_original S (V.ι ≫ F.hom) k) hE
  obtain ⟨t, hkt, ht⟩ := exists_scalar_equality S hS (U.ι ≫ C.hom) F.hom k f g hf hg hfg
  let Et := extendStageIso S (U.ι ≫ C.hom) (V.ι ≫ F.hom) hkt Ek
  obtain ⟨st, hst⟩ := section_extension
    (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hkt).toRingHom))
    (stageScalarTransition S (V.ι ≫ F.hom) hkt)
    (stageScalarModel S (V.ι ≫ F.hom) k).hom
    (stageScalarModel S (V.ι ≫ F.hom) t).hom
    (stageScalarCartesian S (V.ι ≫ F.hom) hkt) sk0 hsk0
  let qAt : (stageScalarModel S (U.ι ≫ C.hom) t).left ⟶ U.toScheme :=
    pullback.snd _ (U.ι ≫ C.hom)
  let qBt : (stageScalarModel S (V.ι ≫ F.hom) t).left ⟶ V.toScheme :=
    pullback.snd _ (V.ι ≫ F.hom)
  have hEt : Et.hom.left ≫ stageScalarTransition S (V.ι ≫ F.hom) hkt =
      stageScalarTransition S (U.ι ≫ C.hom) hkt ≫ Ek.hom.left :=
    (congrArg (fun z : stageScalarModel S (U.ι ≫ C.hom) t ⟶
        stageScalarModel S (V.ι ≫ F.hom) t =>
        z.left ≫ stageScalarTransition S (V.ι ≫ F.hom) hkt)
      (show Et.hom = extendModelMorphism S (U.ι ≫ C.hom) (V.ι ≫ F.hom) hkt Ek.hom from rfl)).trans
      (extendModelMorphism_transition S (U.ι ≫ C.hom) (V.ι ≫ F.hom) hkt Ek.hom)
  have hA : stageScalarTransition S (U.ι ≫ C.hom) hkt ≫ g = qAt ≫ U.ι ≫ e.left :=
    (Category.assoc _ _ _).symm.trans
      (congrArg (fun z => z ≫ U.ι ≫ e.left) (stageScalarTransition_snd S (U.ι ≫ C.hom) hkt))
  have hB : stageScalarTransition S (V.ι ≫ F.hom) hkt ≫ qB ≫ V.ι = qBt ≫ V.ι :=
    (Category.assoc _ _ _).symm.trans
      (congrArg (fun z => z ≫ V.ι) (stageScalarTransition_snd S (V.ι ≫ F.hom) hkt))
  refine ⟨t, hstart.trans (hjk.trans hkt), Et, st, hst, ?_⟩
  exact retain_iso_triangle
    ((Over.forget _).mapIso Ek) ((Over.forget _).mapIso Et)
    (stageScalarTransition S (U.ι ≫ C.hom) hkt)
    (stageScalarTransition S (V.ι ≫ F.hom) hkt)
    g (qB ≫ V.ι) (qAt ≫ U.ι ≫ e.left) (qBt ≫ V.ι) hEt hA hB ht

end FrobeniusSplitting
