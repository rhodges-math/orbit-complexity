import OrbitComplexity.SchubertGeometry.Connectedness.WordEndpointConnected
import OrbitComplexity.SchubertGeometry.Connectedness.PairedIncidenceModels
import OrbitComplexity.SchubertGeometry.BSDH.RichardsonMap
import OrbitComplexity.FrobeniusSplitting.Normality.Connectedness.RetainedIsomorphisms
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Opposite endpoint and incidence comparisons

The opposite endpoint uses the same arithmetic arrow with translated
Schubert and flag comparisons. Incidence endpoints are Cartesian
restrictions of the map between the two intersection models.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open ReductiveGroups FrobeniusSplitting

noncomputable section
universe u v

namespace SchubertGeometry

open private properConnected properConnected_baseChange properConnected_compStable properGC_comp
  from OrbitComplexity.SchubertGeometry.BSDH.RichardsonMap
open private RetainedComparisons retained_comparisons
  from OrbitComplexity.SchubertGeometry.Connectedness.WordEndpointConnected
open private chosenScalarLeg_snd
  from OrbitComplexity.SchubertGeometry.Connectedness.ChosenPairedRetention

private theorem translated_square {B BK : Scheme.{u}}
    {X X' : Over BK} (E : X' ≅ X) {Y : Over B}
    (ρ : BK ⟶ B) (q : X.left ⟶ Y.left) (h : IsPullback q X.hom Y.hom ρ) :
    IsPullback (E.hom.left ≫ q) X'.hom Y.hom ρ := by
  exact h.of_iso' ((Over.forget BK).mapIso E) (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp) (by simp) (by simp) (by simp)

private theorem translated_triangles {C : Type v} [Category C]
    {A B X Y Y' F F' P : C}
    (qA : A ⟶ X) (e : X ⟶ B) (qY : Y ⟶ B) (qF : F ⟶ P) (j : B ⟶ P)
    (f : A ⟶ Y) (f' : A ⟶ Y') (t : Y' ⟶ Y)
    (i : Y ⟶ F) (i' : Y' ⟶ F') (s : F' ⟶ F)
    (he : qA ≫ e = f ≫ qY) (hj : qY ≫ j = i ≫ qF)
    (hf : f = f' ≫ t) (hi : t ≫ i = i' ≫ s) :
    qA ≫ e = f' ≫ (t ≫ qY) ∧
      (t ≫ qY) ≫ j = i' ≫ (s ≫ qF) := by
  constructor
  · exact he.trans ((congrArg (fun a => a ≫ qY) hf).trans (Category.assoc _ _ _))
  · rw [Category.assoc, hj, ← Category.assoc, hi, Category.assoc]

private def incidenceFactor {B : Scheme.{u}} {X Y U V F : Over B}
    (f : X ⟶ U) (g : Y ⟶ V) (i : U ⟶ F) (j : V ⟶ F) :
    pairedIncidenceModel (f ≫ i) (g ≫ j) ⟶ pairedIncidenceModel i j :=
  Over.homMk
    (pullback.map (f ≫ i).left (g ≫ j).left i.left j.left f.left g.left (𝟙 F.left)
      (by simp) (by simp))
    (by
      change _ ≫ (pullback.fst i.left j.left ≫ U.hom) =
        pullback.fst (f ≫ i).left (g ≫ j).left ≫ X.hom
      rw [← Category.assoc, pullback.lift_fst, Category.assoc, f.w])

private theorem incidenceFactor_properties {B : Scheme.{u}} {X Y U V F : Over B}
    (f : X ⟶ U) (g : Y ⟶ V) (i : U ⟶ F) (j : V ⟶ F)
    [IsProper f.left] [GeometricallyConnected f.left]
    [IsProper g.left] [GeometricallyConnected g.left] :
    IsProper (incidenceFactor f g i j).left ∧
      GeometricallyConnected (incidenceFactor f g i j).left := by
  let : MorphismProperty.IsStableUnderBaseChange properConnected := properConnected_baseChange
  let : MorphismProperty.IsStableUnderComposition properConnected := properConnected_compStable
  exact MorphismProperty.pullbackMap (P := properConnected)
    (f := (f ≫ i).left) (g := (g ≫ j).left) (f' := i.left) (g' := j.left)
    (i₁ := f.left) (i₂ := g.left) ⟨inferInstance, inferInstance⟩
    ⟨inferInstance, inferInstance⟩ rfl rfl

private theorem incidenceFactor_endpoint {B : Scheme.{u}} {X Y U V F : Over B}
    (f : X ⟶ U) (g : Y ⟶ V) (i : U ⟶ F) (j : V ⟶ F) :
    incidenceFactor f g i j ≫ pairedIncidenceEndpoint i j =
      pairedIncidenceEndpoint (f ≫ i) (g ≫ j) := by
  apply CostructuredArrow.hom_ext
  dsimp only [incidenceFactor, pairedIncidenceEndpoint, pairedIncidenceModel, Over.homMk]
  exact pullback.lift_fst_assoc _ _ _ i.left

private theorem mono_restriction {X Y R : Scheme.{u}}
    (m : X ⟶ Y) (h : X ⟶ R) (i : Y ⟶ R) [Mono i]
    (hm : m ≫ i = h) : IsPullback (𝟙 X) m h i :=
  IsPullback.of_horiz_isIso_mono ⟨by simpa using hm.symm⟩

private theorem pairedEndpoint_of_factors {B : Scheme.{u}}
    {C D X Y U V F : Over B}
    (f : X ⟶ U) (g : Y ⟶ V) (i : U ⟶ F) (j : V ⟶ F)
    [IsProper f.left] [GeometricallyConnected f.left]
    [IsProper g.left] [GeometricallyConnected g.left]
    [Mono i.left] [Mono j.left]
    (r : D ⟶ F) [Mono r.left] (rx : D ⟶ U) (ry : D ⟶ V)
    (hrx : rx ≫ i = r) (hry : ry ≫ j = r)
    (m : pairedIncidenceModel (f ≫ i) (g ≫ j) ⟶ D)
    (hm : m ≫ r = pairedIncidenceEndpoint (f ≫ i) (g ≫ j))
    (E : C ≅ pairedIncidenceModel (f ≫ i) (g ≫ j))
    (e : C ⟶ D) (he : E.hom ≫ m = e) :
    IsProper e.left ∧ GeometricallyConnected e.left := by
  let L : D.left ⟶ (pairedIncidenceModel i j).left :=
    pullback.lift rx.left ry.left
      ((congrArg Over.Hom.left hrx).trans (congrArg Over.Hom.left hry).symm)
  have hL : L ≫ (pairedIncidenceEndpoint i j).left = r.left := by
    exact (pullback.lift_fst_assoc _ _ _ i.left).trans (congrArg Over.Hom.left hrx)
  let : Mono L := mono_of_mono_fac hL
  let : Mono (pairedIncidenceEndpoint i j).left := by
    change Mono (pullback.fst i.left j.left ≫ i.left)
    infer_instance
  have hfac : m.left ≫ L = (incidenceFactor f g i j).left := by
    apply (cancel_mono (pairedIncidenceEndpoint i j).left).mp
    calc
      (m.left ≫ L) ≫ (pairedIncidenceEndpoint i j).left = m.left ≫ r.left := by
        rw [Category.assoc, hL]
      _ = (pairedIncidenceEndpoint (f ≫ i) (g ≫ j)).left := congrArg Over.Hom.left hm
      _ = (incidenceFactor f g i j).left ≫ (pairedIncidenceEndpoint i j).left :=
        (congrArg Over.Hom.left (incidenceFactor_endpoint f g i j)).symm
  have hcart := mono_restriction m.left (incidenceFactor f g i j).left L hfac
  have hp := incidenceFactor_properties f g i j
  let : IsProper m.left := MorphismProperty.of_isPullback (P := @IsProper) hcart hp.1
  let : GeometricallyConnected m.left :=
    MorphismProperty.of_isPullback (P := @GeometricallyConnected) hcart hp.2
  have hcomp : E.hom.left ≫ m.left = e.left := congrArg Over.Hom.left he
  refine ⟨?_, ?_⟩
  · exact hcomp ▸ inferInstanceAs (IsProper (E.hom.left ≫ m.left))
  · exact hcomp ▸ (MorphismProperty.cancel_left_of_respectsIso
      (@GeometricallyConnected) E.hom.left m.left).mpr inferInstance

private theorem old_projection_base {B T : Scheme.{u}} (κ : T ⟶ B)
    (D F : Over B) (r : D ⟶ F) :
    (pullback.snd κ D.hom ≫ r.left) ≫ F.hom = pullback.fst κ D.hom ≫ κ := by
  rw [Category.assoc, r.w]
  exact (pullback.condition (f := κ) (g := D.hom)).symm

private theorem projected_arrow_base {B T : Scheme.{u}} (κ : T ⟶ B)
    (D U F : Over B) (i : U ⟶ F)
    (p : Over.mk (pullback.fst κ D.hom) ⟶ Over.mk (pullback.fst κ U.hom)) :
    (p.left ≫ pullback.snd κ U.hom ≫ i.left) ≫ F.hom =
      pullback.fst κ D.hom ≫ κ := by
  calc
    (p.left ≫ pullback.snd κ U.hom ≫ i.left) ≫ F.hom =
        p.left ≫ ((pullback.snd κ U.hom ≫ i.left) ≫ F.hom) := Category.assoc _ _ _
    _ = p.left ≫ (pullback.fst κ U.hom ≫ κ) :=
      congrArg (fun a => p.left ≫ a) (old_projection_base κ U F i)
    _ = (p.left ≫ pullback.fst κ U.hom) ≫ κ := (Category.assoc _ _ _).symm
    _ = pullback.fst κ D.hom ≫ κ := congrArg (fun a => a ≫ κ) p.w

private theorem cone_triangle {C : Type v} [Category C]
    {A B D X Y Z W : C}
    (cD : A ⟶ X) (p : X ⟶ Y) (g : A ⟶ B) (cU : B ⟶ Y)
    (sD : X ⟶ D) (sU : Y ⟶ Z) (d : A ⟶ D) (u : B ⟶ Z)
    (iD : D ⟶ W) (iU : Z ⟶ W)
    (hp : cD ≫ p = g ≫ cU) (hD : cD ≫ sD = d) (hU : cU ≫ sU = u)
    (hg : g ≫ u ≫ iU = d ≫ iD) :
    cD ≫ (p ≫ sU ≫ iU) = cD ≫ (sD ≫ iD) := by
  calc
    cD ≫ (p ≫ sU ≫ iU) = g ≫ (cU ≫ sU) ≫ iU := by
      rw [← Category.assoc, hp]
      simp only [Category.assoc]
    _ = g ≫ u ≫ iU := congrArg (fun a => g ≫ a ≫ iU) hU
    _ = d ≫ iD := hg
    _ = cD ≫ (sD ≫ iD) :=
      (congrArg (fun a => a ≫ iD) hD).symm.trans (Category.assoc _ _ _)

private theorem extended_projection {K : Type u} [CommRing K]
    (S : Subalgebra ℤ K) (D U : Over (Spec (.of S)))
    {i j : CoefficientStage S} (hij : i ≤ j)
    (p : stageScalarModel S D.hom i ⟶ stageScalarModel S U.hom i) :
    (extendModelMorphism S D.hom U.hom hij p).left ≫ pullback.snd _ U.hom =
      stageScalarTransition S D.hom hij ≫ p.left ≫ pullback.snd _ U.hom := by
  calc
    (extendModelMorphism S D.hom U.hom hij p).left ≫ pullback.snd _ U.hom =
        (extendModelMorphism S D.hom U.hom hij p).left ≫
          (stageScalarTransition S U.hom hij ≫ pullback.snd _ U.hom) :=
      congrArg (fun a => (extendModelMorphism S D.hom U.hom hij p).left ≫ a)
        (stageScalarTransition_snd S U.hom hij).symm
    _ = ((extendModelMorphism S D.hom U.hom hij p).left ≫
        stageScalarTransition S U.hom hij) ≫ pullback.snd _ U.hom :=
      (Category.assoc _ _ _).symm
    _ = (stageScalarTransition S D.hom hij ≫ p.left) ≫ pullback.snd _ U.hom :=
      congrArg (fun a => a ≫ pullback.snd _ U.hom)
        (extendModelMorphism_transition S D.hom U.hom hij p)
    _ = stageScalarTransition S D.hom hij ≫ p.left ≫ pullback.snd _ U.hom :=
      Category.assoc _ _ _

private theorem projection_after_extension {C : Type v} [Category C]
    {X X₀ U U₀ U₁ D F : C}
    (p : X ⟶ U) (s : U ⟶ U₀) (t : X ⟶ X₀)
    (q : X₀ ⟶ U₁) (s₀ : U₁ ⟶ U₀) (i : U₀ ⟶ F)
    (d : X₀ ⟶ D) (r : D ⟶ F) (sD : X ⟶ D)
    (hp : p ≫ s = t ≫ q ≫ s₀)
    (h : t ≫ (q ≫ s₀ ≫ i) = t ≫ (d ≫ r))
    (hd : t ≫ d = sD) :
    p ≫ (s ≫ i) = sD ≫ r := by
  calc
    p ≫ (s ≫ i) = (p ≫ s) ≫ i := (Category.assoc _ _ _).symm
    _ = (t ≫ q ≫ s₀) ≫ i := congrArg (fun a => a ≫ i) hp
    _ = t ≫ (q ≫ s₀ ≫ i) := by simp only [Category.assoc]
    _ = t ≫ (d ≫ r) := h
    _ = (t ≫ d) ≫ r := (Category.assoc _ _ _).symm
    _ = sD ≫ r := congrArg (fun a => a ≫ r) hd

private theorem model_triangle_later {K : Type u} [CommRing K]
    (S : Subalgebra ℤ K) (D U F : Over (Spec (.of S))) (r : D ⟶ F) (iU : U ⟶ F)
    {i j : CoefficientStage S} (hij : i ≤ j)
    (p : stageScalarModel S D.hom i ⟶ stageScalarModel S U.hom i)
    (h : stageScalarTransition S D.hom hij ≫ (p.left ≫ pullback.snd _ U.hom ≫ iU.left) =
      stageScalarTransition S D.hom hij ≫ (pullback.snd _ D.hom ≫ r.left)) :
    extendModelMorphism S D.hom U.hom hij p ≫ chosenScalarArrow
        (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion j.property.2).toRingHom)) iU =
      chosenScalarArrow
        (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion j.property.2).toRingHom)) r := by
  let κ := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion j.property.2).toRingHom)
  let κ₀ := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion i.property.2).toRingHom)
  let p' := extendModelMorphism S D.hom U.hom hij p
  have htrans : stageScalarTransition S D.hom hij ≫ pullback.snd κ₀ D.hom =
      pullback.snd κ D.hom := stageScalarTransition_snd S D.hom hij
  apply CostructuredArrow.hom_ext
  apply pullback.hom_ext
  · exact (p' ≫ chosenScalarArrow κ iU).w.trans (chosenScalarArrow κ r).w.symm
  · have hleft :
        (p' ≫ chosenScalarArrow κ iU).left ≫ pullback.snd κ F.hom =
          p'.left ≫ (pullback.snd κ U.hom ≫ iU.left) :=
      (Category.assoc _ _ _).trans
        (congrArg (fun a => p'.left ≫ a) (chosenScalarArrow_snd κ iU))
    have hmiddle := projection_after_extension p'.left (pullback.snd κ U.hom)
      (stageScalarTransition S D.hom hij) p.left (pullback.snd κ₀ U.hom)
      iU.left (pullback.snd κ₀ D.hom) r.left (pullback.snd κ D.hom)
      (extended_projection S D U hij p) h htrans
    exact hleft.trans (hmiddle.trans (chosenScalarArrow_snd κ r).symm)

private theorem retain_target_triangles {K : Type u} [CommRing K]
    (S : Subalgebra ℤ K) (hS : S.FG) {I : Type v} [Fintype I]
    (D F : Over (Spec (.of S))) (U : I → Over (Spec (.of S)))
    [CompactSpace D.left] [QuasiSeparatedSpace D.left]
    [LocallyOfFiniteType F.hom] [∀ r, LocallyOfFinitePresentation (U r).hom]
    (r : D ⟶ F) (iU : ∀ a, U a ⟶ F)
    (g : ∀ a, genericScalarModel S D.hom ⟶ genericScalarModel S (U a).hom)
    (hg : ∀ a, (g a).left ≫
      pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap S K))) (U a).hom ≫ (iU a).left =
      pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap S K))) D.hom ≫ r.left)
    (start : CoefficientStage S) :
    ∃ (j : CoefficientStage S) (_ : start ≤ j)
      (p : ∀ a, stageScalarModel S D.hom j ⟶ stageScalarModel S (U a).hom j),
      (∀ a, p a ≫ chosenScalarArrow
          (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion j.property.2).toRingHom)) (iU a) =
        chosenScalarArrow
          (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion j.property.2).toRingHom)) r) ∧
      ∀ a, (modelScalarCone S D.hom).π.app (op j) ≫ (p a).left =
        (g a).left ≫ (modelScalarCone S (U a).hom).π.app (op j) := by
  let : ∀ _a : I, CompactSpace D.left := fun _ => inferInstance
  let : ∀ _a : I, QuasiSeparatedSpace D.left := fun _ => inferInstance
  let : ∀ _a : I, LocallyOfFiniteType F.hom := fun _ => inferInstance
  obtain ⟨i, hi, p, hp⟩ := exists_retained_maps S hS (fun _ : I => D.left)
    (fun a => (U a).left) (fun _ => D.hom) (fun a => (U a).hom) g start
  let κ := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion i.property.2).toRingHom)
  let a : ∀ t : I, (stageScalarModel S D.hom i).left ⟶ F.left :=
    fun t => (p t).left ≫ pullback.snd κ (U t).hom ≫ (iU t).left
  let b : ∀ _t : I, (stageScalarModel S D.hom i).left ⟶ F.left :=
    fun _ => pullback.snd κ D.hom ≫ r.left
  have ha : ∀ t, a t ≫ F.hom = (modelScalarBase S D.hom).app (op i) :=
    fun t => (projected_arrow_base κ D (U t) F (iU t) (p t)).trans
      (pullback.condition (f := κ) (g := D.hom))
  have hb : ∀ t, b t ≫ F.hom = (modelScalarBase S D.hom).app (op i) :=
    fun _ => (old_projection_base κ D F r).trans
      (pullback.condition (f := κ) (g := D.hom))
  have heq : ∀ t, (modelScalarCone S D.hom).π.app (op i) ≫ a t =
      (modelScalarCone S D.hom).π.app (op i) ≫ b t := fun t =>
    cone_triangle ((modelScalarCone S D.hom).π.app (op i)) (p t).left (g t).left
      ((modelScalarCone S (U t).hom).π.app (op i))
      (pullback.snd κ D.hom) (pullback.snd κ (U t).hom)
      (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap S K))) D.hom)
      (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap S K))) (U t).hom)
      r.left (iU t).left (hp t) (chosenScalarLeg_snd S D.hom i)
      (chosenScalarLeg_snd S (U t).hom i) (hg t)
  obtain ⟨j, hij, h⟩ := exists_retained_equations (S := S) hS
    (fun _ : I => D.left) (fun _ : I => F.left) (fun _ => D.hom) (fun _ => F.hom)
    i a b ha hb heq
  exact ⟨j, hi.trans hij, (fun t => extendModelMorphism S D.hom (U t).hom hij (p t)),
    (fun t => model_triangle_later S D (U t) F r (iU t) hij (p t) (h t)),
    (fun t => extendModelMorphism_baseChange S D.hom (U t).hom hij (p t) (g t) (hp t))⟩

private theorem projection_triangle {C : Type v} [Category C]
    {X Y F D U P : C} (p : X ⟶ Y) (j : Y ⟶ F) (r : X ⟶ F)
    (qD : X ⟶ D) (qU : Y ⟶ U) (qF : F ⟶ P) (iD : D ⟶ P) (iU : U ⟶ P)
    (hp : p ≫ j = r) (hU : qU ≫ iU = j ≫ qF) (hD : qD ≫ iD = r ≫ qF) :
    p ≫ qU ≫ iU = qD ≫ iD := by
  rw [hU, ← Category.assoc, hp]
  exact hD.symm

private theorem conjugate_old_triangle {C : Type v} [Category C]
    {X Y X₀ Y₀ D U F : C} (E : X ≅ X₀) (T : Y ≅ Y₀)
    (p : X ⟶ Y) (sD : X₀ ⟶ D) (sU : Y₀ ⟶ U)
    (qD : X ⟶ D) (qU : Y ⟶ U) (iD : D ⟶ F) (iU : U ⟶ F)
    (hD : E.hom ≫ sD = qD) (hU : T.hom ≫ sU = qU)
    (h : p ≫ qU ≫ iU = qD ≫ iD) :
    (E.inv ≫ p ≫ T.hom) ≫ sU ≫ iU = sD ≫ iD := by
  calc
    (E.inv ≫ p ≫ T.hom) ≫ sU ≫ iU = E.inv ≫ (p ≫ (T.hom ≫ sU) ≫ iU) := by
      simp only [Category.assoc]
    _ = E.inv ≫ (p ≫ qU ≫ iU) := congrArg (fun a => E.inv ≫ (p ≫ a ≫ iU)) hU
    _ = E.inv ≫ (qD ≫ iD) := congrArg (fun a => E.inv ≫ a) h
    _ = E.inv ≫ ((E.hom ≫ sD) ≫ iD) :=
      congrArg (fun a => E.inv ≫ (a ≫ iD)) hD.symm
    _ = sD ≫ iD := by simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-- The Richardson projections to its two Schubert targets have models over
a common coefficient extension. Both triangles with the flag inclusion and
both generic scalar comparisons are retained. -/
theorem exists_richardson_projections {K : Type u}
    [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K) (u v : G.weylGroup)
    (S : Subalgebra ℤ K) (hS : S.FG)
    (D U V F : Over (Spec (.of S)))
    [CompactSpace D.left] [QuasiSeparatedSpace D.left]
    [LocallyOfFinitePresentation U.hom] [LocallyOfFinitePresentation V.hom]
    [LocallyOfFiniteType F.hom]
    (iD : D ⟶ F) (iU : U ⟶ F) (iV : V ⟶ F)
    (qD : (richardsonVariety G u v).scheme ⟶ D.left)
    (qU : (schubertVariety G v).scheme ⟶ U.left)
    (qV : (oppositeSchubertVariety G u).scheme ⟶ V.left)
    (qF : (flagVariety G).scheme ⟶ F.left)
    (hD : IsPullback qD (richardsonVariety G u v).toSpec D.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hU : IsPullback qU (schubertVariety G v).toSpec U.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hV : IsPullback qV (oppositeSchubertVariety G u).toSpec V.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hiD : qD ≫ iD.left = (richardsonInclusion G u v).left ≫ qF)
    (hiU : qU ≫ iU.left = (schubertInclusion G v).left ≫ qF)
    (hiV : qV ≫ iV.left = (oppositeSchubertInclusion G u).left ≫ qF)
    (start : CoefficientStage S) :
    let ED : (richardsonVariety G u v).toOver ≅ genericScalarModel S D.hom :=
      hD.flip.isoOverPullback
    let EU : (schubertVariety G v).toOver ≅ genericScalarModel S U.hom :=
      hU.flip.isoOverPullback
    let EV : (oppositeSchubertVariety G u).toOver ≅ genericScalarModel S V.hom :=
      hV.flip.isoOverPullback
    ∃ (k : CoefficientStage S) (_ : start ≤ k)
      (p : stageScalarModel S D.hom k ⟶ stageScalarModel S U.hom k)
      (q : stageScalarModel S D.hom k ⟶ stageScalarModel S V.hom k),
      let κ := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom)
      p ≫ chosenScalarArrow κ iU = chosenScalarArrow κ iD ∧
      q ≫ chosenScalarArrow κ iV = chosenScalarArrow κ iD ∧
      (modelScalarCone S D.hom).π.app (op k) ≫ p.left =
        (ED.inv ≫ richardsonToSchubert G u v ≫ EU.hom).left ≫
          (modelScalarCone S U.hom).π.app (op k) ∧
      (modelScalarCone S D.hom).π.app (op k) ≫ q.left =
        (ED.inv ≫ richardsonToOpposite G u v ≫ EV.hom).left ≫
          (modelScalarCone S V.hom).π.app (op k) := by
  classical
  let targets : Bool → Over (Spec (.of S))
    | false => U
    | true => V
  let targetsK : Bool → Over (Spec (.of K))
    | false => (schubertVariety G v).toOver
    | true => (oppositeSchubertVariety G u).toOver
  let inclusion : ∀ b, targets b ⟶ F
    | false => iU
    | true => iV
  let inclusionK : ∀ b, targetsK b ⟶ (flagVariety G).toOver
    | false => schubertInclusion G v
    | true => oppositeSchubertInclusion G u
  let qTarget : ∀ b, (targetsK b).left ⟶ (targets b).left
    | false => qU
    | true => qV
  have hTarget : ∀ b, IsPullback (qTarget b) (targetsK b).hom (targets b).hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))) := by
    intro b
    cases b
    · exact hU
    · exact hV
  have hInclusion : ∀ b, qTarget b ≫ (inclusion b).left = (inclusionK b).left ≫ qF := by
    intro b
    cases b
    · exact hiU
    · exact hiV
  let projectionK : ∀ b, (richardsonVariety G u v).toOver ⟶ targetsK b
    | false => richardsonToSchubert G u v
    | true => richardsonToOpposite G u v
  have hProjectionK : ∀ b, projectionK b ≫ inclusionK b = richardsonInclusion G u v := by
    intro b
    cases b
    · exact richardsonToSchubert_comp G u v
    · exact richardsonToOpposite_comp G u v
  let ED : (richardsonVariety G u v).toOver ≅ genericScalarModel S D.hom :=
    hD.flip.isoOverPullback
  let E : ∀ b, targetsK b ≅ genericScalarModel S (targets b).hom :=
    fun b => (hTarget b).flip.isoOverPullback
  let g : ∀ b, genericScalarModel S D.hom ⟶ genericScalarModel S (targets b).hom :=
    fun b => ED.inv ≫ projectionK b ≫ (E b).hom
  have hg : ∀ b, (g b).left ≫
      pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap S K))) (targets b).hom ≫
        (inclusion b).left =
      pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap S K))) D.hom ≫ iD.left := by
    intro b
    exact conjugate_old_triangle ((Over.forget (Spec (.of K))).mapIso ED)
      ((Over.forget (Spec (.of K))).mapIso (E b)) (projectionK b).left
      (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap S K))) D.hom)
      (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap S K))) (targets b).hom)
      qD (qTarget b) iD.left (inclusion b).left
      hD.flip.isoOverPullback_hom_left_comp_snd
      (hTarget b).flip.isoOverPullback_hom_left_comp_snd
      (projection_triangle (projectionK b).left (inclusionK b).left
        (richardsonInclusion G u v).left qD (qTarget b) qF iD.left (inclusion b).left
        (congrArg Over.Hom.left (hProjectionK b)) (hInclusion b) hiD)
  let : ∀ b, LocallyOfFinitePresentation (targets b).hom := fun b => by
    cases b <;> infer_instance
  obtain ⟨k, hk, p, hp, hcomp⟩ := retain_target_triangles S hS D F targets iD inclusion g hg start
  exact ⟨k, hk, p false, p true, hp false, hp true, hcomp false, hcomp true⟩

/-- The opposite Schubert endpoint becomes geometrically connected on a
coefficient extension of the given model. Translation changes the two
comparison maps and preserves the arithmetic source, target, and endpoint. -/
theorem exists_opposite_endpoint_connected {K : Type u}
    [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K) (word : List G.rootBase.support)
    (hred : (weylCoxeterSystem G.rootBase).IsReduced word)
    (S : Subalgebra ℤ K) (hS : S.FG) (P : Over (Spec (.of S)))
    [LocallyOfFinitePresentation P.hom] [QuasiCompact P.hom] [IsSeparated P.hom]
    (qP : (flagVariety G).scheme ⟶ P.left)
    (hP : IsPullback qP (flagVariety G).toSpec P.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (C D : Over (Spec (.of S))) (e : C ⟶ D) (j : D ⟶ P)
    [IsProper e.left] [IsClosedImmersion j.left]
    (qC : bsdhScheme G word ⟶ C.left)
    (qD : (oppositeSchubertVariety G
      (G.longestElement * simpleWeylWord G.rootBase word)).scheme ⟶ D.left)
    (hC : IsPullback qC (bsdhToSpec G word) C.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hD : IsPullback qD (oppositeSchubertVariety G
      (G.longestElement * simpleWeylWord G.rootBase word)).toSpec D.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (he : qC ≫ e.left = (bsdhOppositeSchubertMap G word hred).left ≫ qD)
    (hj : qD ≫ j.left = (oppositeSchubertInclusion G
      (G.longestElement * simpleWeylWord G.rootBase word)).left ≫ qP)
    (start : CoefficientStage S) :
    ∃ (k : CoefficientStage S) (_ : start ≤ k),
      let κ := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom)
      let ek := chosenScalarArrow κ e
      GeometricallyConnected ek.left ∧ IsProper ek.left ∧
      (ek.left ≫ (stageScalarModel S D.hom k).hom = (stageScalarModel S C.hom k).hom) ∧
      (ek.left ≫ pullback.snd κ D.hom = pullback.snd κ C.hom ≫ e.left) ∧
      (∀ (L : Type u) [Field L] (y : Spec (.of L) ⟶ (stageScalarModel S D.hom k).left),
        ConnectedSpace (pullback ek.left y : Scheme.{u})) ∧
      RetainedComparisons S C D P e j (bsdhVariety G word).toOver
        (oppositeSchubertVariety G
          (G.longestElement * simpleWeylWord G.rootBase word)).toOver (flagVariety G).toOver
        (bsdhOppositeSchubertMap G word hred)
        (oppositeSchubertInclusion G (G.longestElement * simpleWeylWord G.rootBase word))
        qC qD qP k := by
  let E := oppositeSchubertIso G (simpleWeylWord G.rootBase word)
  let T := longestFlagIso G
  let qD' := E.hom.left ≫ qD
  let qP' := T.hom.left ≫ qP
  have hD' := translated_square E
    (Spec.map (CommRingCat.ofHom (algebraMap S K))) qD hD
  have hP' := translated_square T
    (Spec.map (CommRingCat.ofHom (algebraMap S K))) qP hP
  have heMap : (bsdhOppositeSchubertMap G word hred).left =
      (bsdhSchubertMap G word hred).left ≫ E.hom.left := rfl
  have hiMap : E.hom.left ≫ (oppositeSchubertInclusion G
      (G.longestElement * simpleWeylWord G.rootBase word)).left =
      (schubertInclusion G (simpleWeylWord G.rootBase word)).left ≫ T.hom.left :=
    congrArg Over.Hom.left (oppositeSchubertIso_comp G (simpleWeylWord G.rootBase word))
  have htrans := translated_triangles qC e.left qD qP j.left
    (bsdhOppositeSchubertMap G word hred).left (bsdhSchubertMap G word hred).left E.hom.left
    (oppositeSchubertInclusion G (G.longestElement * simpleWeylWord G.rootBase word)).left
    (schubertInclusion G (simpleWeylWord G.rootBase word)).left T.hom.left
    he hj heMap hiMap
  obtain ⟨k, hk, hgc, hp, hbase, hold, hfields, _hretained⟩ :=
    exists_word_endpoint_connected G word hred S hS P qP' hP' C D e j qC qD' hC hD'
      htrans.1 htrans.2 start
  have hretained := retained_comparisons S C D P e j (bsdhVariety G word).toOver
    (oppositeSchubertVariety G
      (G.longestElement * simpleWeylWord G.rootBase word)).toOver (flagVariety G).toOver
    (bsdhOppositeSchubertMap G word hred)
    (oppositeSchubertInclusion G (G.longestElement * simpleWeylWord G.rootBase word))
    qC qD qP hC hD hP he hj k
  exact ⟨k, hk, hgc, hp, hbase, hold, hfields, hretained⟩

end SchubertGeometry
