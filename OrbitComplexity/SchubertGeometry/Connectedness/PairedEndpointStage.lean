import OrbitComplexity.SchubertGeometry.Connectedness.PairedEndpointConnected
import OrbitComplexity.FrobeniusSplitting.Normality.Products.PairedScalarComparison
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # A common coefficient stage for the paired endpoint

The two word endpoints, the Richardson projections, and the prescribed
incidence source comparison are extended to one coefficient stage. The
resulting paired map is the scalar extension of the given endpoint.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open ReductiveGroups FrobeniusSplitting

noncomputable section
universe u v

namespace SchubertGeometry

open private scalar_property scalar_composition
  from OrbitComplexity.SchubertGeometry.Connectedness.AppendSchubertConnected
open private field_connected
  from OrbitComplexity.SchubertGeometry.Connectedness.AppendSchubertConnected
open private scalar_endpoint_gc endpoint_factor RetainedComparisons retained_comparisons
  from OrbitComplexity.SchubertGeometry.Connectedness.WordEndpointConnected
open private pairedEndpoint_of_factors extended_projection
  from OrbitComplexity.SchubertGeometry.Connectedness.PairedEndpointConnected

private theorem projection_composition {C : Type v} [Category C]
    {A A₀ B B₀ X Y : C}
    (p : A ⟶ B) (s : B ⟶ Y) (t : A ⟶ A₀)
    (q : A₀ ⟶ B₀) (s₀ : B₀ ⟶ Y)
    (a : A₀ ⟶ X) (b : A ⟶ X) (f : X ⟶ Y)
    (hp : p ≫ s = t ≫ q ≫ s₀)
    (hq : q ≫ s₀ = a ≫ f) (ht : t ≫ a = b) :
    p ≫ s = b ≫ f := by
  exact hp.trans ((congrArg (fun z => t ≫ z) hq).trans
    ((Category.assoc _ _ _).symm.trans (congrArg (fun z => z ≫ f) ht)))

private theorem incidence_projection_triangle {C : Type v} [Category C]
    {P P' X X' F F' : C}
    (q : P' ⟶ P) (a : P ⟶ X) (f : X ⟶ F)
    (a' : P' ⟶ X') (f' : X' ⟶ F')
    (sX : X' ⟶ X) (sF : F' ⟶ F)
    (hq : q ≫ a = a' ≫ sX) (hf : f' ≫ sF = sX ≫ f) :
    q ≫ (a ≫ f) = (a' ≫ f') ≫ sF := by
  calc
    q ≫ (a ≫ f) = (q ≫ a) ≫ f := (Category.assoc _ _ _).symm
    _ = (a' ≫ sX) ≫ f := congrArg (fun z => z ≫ f) hq
    _ = a' ≫ (sX ≫ f) := Category.assoc _ _ _
    _ = a' ≫ (f' ≫ sF) := congrArg (fun z => a' ≫ z) hf.symm
    _ = (a' ≫ f') ≫ sF := (Category.assoc _ _ _).symm

private theorem endpoint_projection_triangle {C : Type v} [Category C]
    {A P' F' P F : C}
    (a : A ⟶ P') (e : P' ⟶ F') (sF : F' ⟶ F)
    (sP : P' ⟶ P) (p : P ⟶ F) (q : A ⟶ P) (m : A ⟶ F')
    (he : e ≫ sF = sP ≫ p) (hq : a ≫ sP = q)
    (hm : q ≫ p = m ≫ sF) :
    (a ≫ e) ≫ sF = m ≫ sF := by
  calc
    (a ≫ e) ≫ sF = a ≫ (e ≫ sF) := Category.assoc _ _ _
    _ = a ≫ (sP ≫ p) := congrArg (fun z => a ≫ z) he
    _ = (a ≫ sP) ≫ p := (Category.assoc _ _ _).symm
    _ = q ≫ p := congrArg (fun z => z ≫ p) hq
    _ = m ≫ sF := hm

private theorem iso_factor_cancel {C : Type v} [Category C]
    {X P Q D : C} (E : X ≅ P) (A : Q ≅ P)
    (m : P ⟶ D) (e : X ⟶ D) (h : E.hom ≫ m = e) :
    (E.hom ≫ A.inv) ≫ (A.hom ≫ m) = e := by
  simpa only [Category.assoc, Iso.inv_hom_id_assoc] using h

private theorem extended_chosen {K : Type u} [CommRing K]
    (S : Subalgebra ℤ K) {X Y : Over (Spec (.of S))} (f : X ⟶ Y)
    {i j : CoefficientStage S} (hij : i ≤ j) :
    extendModelMorphism S X.hom Y.hom hij
      (chosenScalarArrow
        (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion i.property.2).toRingHom)) f) =
    chosenScalarArrow
      (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion j.property.2).toRingHom)) f := by
  let κ := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion i.property.2).toRingHom)
  let τ := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion j.property.2).toRingHom)
  let p := extendModelMorphism S X.hom Y.hom hij (chosenScalarArrow κ f)
  apply CostructuredArrow.hom_ext
  apply pullback.hom_ext
  · exact p.w.trans (chosenScalarArrow τ f).w.symm
  · exact (projection_composition p.left (pullback.snd τ Y.hom)
      (stageScalarTransition S X.hom hij) (chosenScalarArrow κ f).left
      (pullback.snd κ Y.hom) (pullback.snd κ X.hom) (pullback.snd τ X.hom)
      f.left (extended_projection S X Y hij (chosenScalarArrow κ f))
      (chosenScalarArrow_snd κ f) (stageScalarTransition_snd S X.hom hij)).trans
        (chosenScalarArrow_snd τ f).symm

private theorem extend_triangle {K : Type u} [CommRing K]
    (S : Subalgebra ℤ K) {X Y Z : Over (Spec (.of S))}
    (f : X ⟶ Z) (g : Y ⟶ Z) {i j : CoefficientStage S} (hij : i ≤ j)
    (p : stageScalarModel S X.hom i ⟶ stageScalarModel S Y.hom i)
    (h : p ≫ chosenScalarArrow
        (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion i.property.2).toRingHom)) g =
      chosenScalarArrow
        (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion i.property.2).toRingHom)) f) :
    extendModelMorphism S X.hom Y.hom hij p ≫ chosenScalarArrow
        (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion j.property.2).toRingHom)) g =
      chosenScalarArrow
        (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion j.property.2).toRingHom)) f := by
  let κ := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion i.property.2).toRingHom)
  exact (congrArg (fun a => extendModelMorphism S X.hom Y.hom hij p ≫ a)
    (extended_chosen S g hij).symm).trans
      ((retainedMap_comp S X.hom Y.hom Z.hom hij p (chosenScalarArrow κ g)).trans
        ((congrArg (extendModelMorphism S X.hom Z.hom hij) h).trans
          (extended_chosen S f hij)))

private theorem extend_iso_square {K : Type u} [CommRing K]
    (S : Subalgebra ℤ K) {C P D : Over (Spec (.of S))} (e : C ⟶ D)
    {i j : CoefficientStage S} (hij : i ≤ j)
    (E : stageScalarModel S C.hom i ≅ stageScalarModel S P.hom i)
    (m : stageScalarModel S P.hom i ⟶ stageScalarModel S D.hom i)
    (h : E.hom ≫ m = chosenScalarArrow
      (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion i.property.2).toRingHom)) e) :
    (retainedIsoExtend S C.hom P.hom hij E).hom ≫
        extendModelMorphism S P.hom D.hom hij m =
      chosenScalarArrow
        (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion j.property.2).toRingHom)) e :=
  (retainedMap_comp S C.hom P.hom D.hom hij E.hom m).trans
    ((congrArg (extendModelMorphism S C.hom D.hom hij) h).trans
      (extended_chosen S e hij))

private theorem stage_gc_mono {K : Type u} [CommRing K]
    (S : Subalgebra ℤ K) {X Y : Over (Spec (.of S))} (f : X ⟶ Y)
    {i j : CoefficientStage S} (hij : i ≤ j)
    (h : GeometricallyConnected
      (chosenScalarArrow
        (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion i.property.2).toRingHom)) f).left) :
    GeometricallyConnected
      (chosenScalarArrow
        (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion j.property.2).toRingHom)) f).left := by
  let l : CoefficientStage i.val := ⟨j.val, j.property.1, hij⟩
  have hNested := scalar_property (@GeometricallyConnected)
    (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hij).toRingHom))
    (chosenScalarArrow
      (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion i.property.2).toRingHom)) f) h
  exact scalar_endpoint_gc S f i l hNested

private theorem scalar_composite_snd {B T : Scheme.{u}} (κ : T ⟶ B)
    {X U F : Over B} (f : X ⟶ U) (i : U ⟶ F) :
    (chosenScalarArrow κ f ≫ chosenScalarArrow κ i).left ≫ pullback.snd κ F.hom =
      pullback.snd κ X.hom ≫ (f ≫ i).left :=
  (congrArg (fun a => a.left ≫ pullback.snd κ F.hom)
    (scalar_composition κ f i).symm).trans (chosenScalarArrow_snd κ (f ≫ i))

private theorem scalar_incidence_iso {B T : Scheme.{u}} (κ : T ⟶ B)
    {X Y U V F : Over B} (f : X ⟶ U) (g : Y ⟶ V) (i : U ⟶ F) (j : V ⟶ F) :
    let fT := chosenScalarArrow κ f ≫ chosenScalarArrow κ i
    let gT := chosenScalarArrow κ g ≫ chosenScalarArrow κ j
    ∃ E : pairedIncidenceModel fT gT ≅
        Over.mk (pullback.fst κ (pairedIncidenceModel (f ≫ i) (g ≫ j)).hom),
      E.hom ≫ chosenScalarArrow κ (pairedIncidenceEndpoint (f ≫ i) (g ≫ j)) =
        pairedIncidenceEndpoint fT gT ∧
      (E.hom.left ≫ pullback.snd κ (pairedIncidenceModel (f ≫ i) (g ≫ j)).hom) ≫
          pullback.fst (f ≫ i).left (g ≫ j).left =
        pullback.fst fT.left gT.left ≫ pullback.snd κ X.hom ∧
      (E.hom.left ≫ pullback.snd κ (pairedIncidenceModel (f ≫ i) (g ≫ j)).hom) ≫
          pullback.snd (f ≫ i).left (g ≫ j).left =
        pullback.snd fT.left gT.left ≫ pullback.snd κ Y.hom := by
  let fT := chosenScalarArrow κ f ≫ chosenScalarArrow κ i
  let gT := chosenScalarArrow κ g ≫ chosenScalarArrow κ j
  let XT : Over T := Over.mk (pullback.fst κ X.hom)
  let YT : Over T := Over.mk (pullback.fst κ Y.hom)
  let FT : Over T := Over.mk (pullback.fst κ F.hom)
  let P := pairedIncidenceModel (f ≫ i) (g ≫ j)
  let PT := pairedIncidenceModel fT gT
  have hcomp := paired_model_scalar_pullback κ XT.hom YT.hom FT.hom
    X.hom Y.hom F.hom fT.left gT.left (f ≫ i).left (g ≫ j).left
    fT.w gT.w (f ≫ i).w (g ≫ j).w
    (pullback.snd κ X.hom) (pullback.snd κ Y.hom) (pullback.snd κ F.hom)
    (IsPullback.of_hasPullback κ X.hom).flip
    (IsPullback.of_hasPullback κ Y.hom).flip
    (IsPullback.of_hasPullback κ F.hom).flip
    (scalar_composite_snd κ f i) (scalar_composite_snd κ g j)
  let q : PT.left ⟶ P.left :=
    pullback.map fT.left gT.left (f ≫ i).left (g ≫ j).left
      (pullback.snd κ X.hom) (pullback.snd κ Y.hom) (pullback.snd κ F.hom)
      (scalar_composite_snd κ f i) (scalar_composite_snd κ g j)
  let E : PT ≅ Over.mk (pullback.fst κ P.hom) := hcomp.1.flip.isoOverPullback
  have hOld : E.hom.left ≫ pullback.snd κ P.hom = q :=
    hcomp.1.flip.isoOverPullback_hom_left_comp_snd
  have hqEnd : q ≫ (pairedIncidenceEndpoint (f ≫ i) (g ≫ j)).left =
      (pairedIncidenceEndpoint fT gT).left ≫ pullback.snd κ F.hom :=
    incidence_projection_triangle q
      (pullback.fst (f ≫ i).left (g ≫ j).left) (f ≫ i).left
      (pullback.fst fT.left gT.left) fT.left
      (pullback.snd κ X.hom) (pullback.snd κ F.hom)
      hcomp.2.1 (scalar_composite_snd κ f i)
  have hEnd : E.hom ≫ chosenScalarArrow κ (pairedIncidenceEndpoint (f ≫ i) (g ≫ j)) =
      pairedIncidenceEndpoint fT gT := by
    apply CostructuredArrow.hom_ext
    apply pullback.hom_ext
    · exact (E.hom ≫ chosenScalarArrow κ (pairedIncidenceEndpoint (f ≫ i) (g ≫ j))).w.trans
        (pairedIncidenceEndpoint fT gT).w.symm
    · exact endpoint_projection_triangle E.hom.left
        (chosenScalarArrow κ (pairedIncidenceEndpoint (f ≫ i) (g ≫ j))).left
        (pullback.snd κ F.hom) (pullback.snd κ P.hom)
        (pairedIncidenceEndpoint (f ≫ i) (g ≫ j)).left q
        (pairedIncidenceEndpoint fT gT).left
        (chosenScalarArrow_snd κ (pairedIncidenceEndpoint (f ≫ i) (g ≫ j))) hOld hqEnd
  exact ⟨E, hEnd,
    (congrArg (fun a => a ≫ pullback.fst (f ≫ i).left (g ≫ j).left) hOld).trans hcomp.2.1,
    (congrArg (fun a => a ≫ pullback.snd (f ≫ i).left (g ≫ j).left) hOld).trans hcomp.2.2⟩

private def PairedConnectedResult {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K) (a b : List G.rootBase.support)
    (ha : (weylCoxeterSystem G.rootBase).IsReduced a)
    (hb : (weylCoxeterSystem G.rootBase).IsReduced b)
    (S : Subalgebra ℤ K) (C D X Y U V F : Over (Spec (.of S)))
    (e : C ⟶ D) (r : D ⟶ F) (f : X ⟶ U) (g : Y ⟶ V) (i : U ⟶ F) (j : V ⟶ F)
    (qX : bsdhScheme G a ⟶ X.left) (qY : bsdhScheme G b ⟶ Y.left)
    (qF : (flagVariety G).scheme ⟶ F.left)
    (qC : (pairedBSDHSource G a b).left ⟶ C.left)
    (qD : (richardsonVariety G (G.longestElement * simpleWeylWord G.rootBase b)
      (simpleWeylWord G.rootBase a)).scheme ⟶ D.left)
    (hC : IsPullback qC (pairedBSDHSource G a b).hom C.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (start : CoefficientStage S) : Prop :=
  let P := pairedIncidenceModel (f ≫ i) (g ≫ j)
  ∃ (qP : (pairedBSDHSource G a b).left ⟶ P.left)
    (hP : IsPullback qP (pairedBSDHSource G a b).hom P.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K)))),
    qP ≫ pullback.fst (f ≫ i).left (g ≫ j).left =
      (pullback.fst (Over.homMk (bsdhMap G a) rfl :
        (bsdhVariety G a).toOver ⟶ (flagVariety G).toOver) (bsdhOppositeEndpoint G b)).left ≫ qX ∧
    qP ≫ pullback.snd (f ≫ i).left (g ≫ j).left =
      (pullback.snd (Over.homMk (bsdhMap G a) rfl :
        (bsdhVariety G a).toOver ⟶ (flagVariety G).toOver) (bsdhOppositeEndpoint G b)).left ≫ qY ∧
    let E := chosenPairIso (Spec.map (CommRingCat.ofHom (algebraMap S K)))
      C P (pairedBSDHSource G a b).hom qC qP hC hP
    ∃ (k : CoefficientStage S) (_ : start ≤ k)
      (E₀ : stageScalarModel S C.hom k ≅ stageScalarModel S P.hom k),
      ((modelScalarCone S C.hom).π.app (op k) ≫ E₀.hom.left =
        E.hom.left ≫ (modelScalarCone S P.hom).π.app (op k)) ∧
      ((modelScalarCone S P.hom).π.app (op k) ≫ E₀.inv.left =
        E.inv.left ≫ (modelScalarCone S C.hom).π.app (op k)) ∧
      let κ := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom)
      let fT := chosenScalarArrow κ f ≫ chosenScalarArrow κ i
      let gT := chosenScalarArrow κ g ≫ chosenScalarArrow κ j
      ∃ A : pairedIncidenceModel fT gT ≅ stageScalarModel S P.hom k,
      A.hom ≫ chosenScalarArrow κ (pairedIncidenceEndpoint (f ≫ i) (g ≫ j)) =
        pairedIncidenceEndpoint fT gT ∧
      (A.hom.left ≫ pullback.snd κ P.hom) ≫ pullback.fst (f ≫ i).left (g ≫ j).left =
        pullback.fst fT.left gT.left ≫ pullback.snd κ X.hom ∧
      (A.hom.left ≫ pullback.snd κ P.hom) ≫ pullback.snd (f ≫ i).left (g ≫ j).left =
        pullback.snd fT.left gT.left ≫ pullback.snd κ Y.hom ∧
      let ek := chosenScalarArrow κ e
      GeometricallyConnected ek.left ∧ IsProper ek.left ∧
      (ek.left ≫ (stageScalarModel S D.hom k).hom = (stageScalarModel S C.hom k).hom) ∧
      (ek.left ≫ pullback.snd κ D.hom = pullback.snd κ C.hom ≫ e.left) ∧
      (∀ (L : Type u) [Field L] (y : Spec (.of L) ⟶ (stageScalarModel S D.hom k).left),
        ConnectedSpace (pullback ek.left y : Scheme.{u})) ∧
      RetainedComparisons S C D F e r (pairedBSDHSource G a b)
        (richardsonVariety G (G.longestElement * simpleWeylWord G.rootBase b)
          (simpleWeylWord G.rootBase a)).toOver (flagVariety G).toOver
        (pairedRichardsonMap G a b ha hb)
        (richardsonInclusion G (G.longestElement * simpleWeylWord G.rootBase b)
          (simpleWeylWord G.rootBase a)) qC qD qF k

/-- The prescribed paired endpoint becomes geometrically connected after a
common coefficient extension. The component connectedness proofs, Richardson
projections, and incidence comparison are constructed at compatible stages;
the paired source, target, endpoint and both original projections are retained. -/
theorem exists_paired_endpoint_connected {K : Type u}
    [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K) (a b : List G.rootBase.support)
    (ha : (weylCoxeterSystem G.rootBase).IsReduced a)
    (hb : (weylCoxeterSystem G.rootBase).IsReduced b)
    (S : Subalgebra ℤ K) (hS : S.FG)
    (C D X Y U V F : Over (Spec (.of S)))
    [CompactSpace C.left] [QuasiSeparatedSpace C.left]
    [LocallyOfFinitePresentation C.hom]
    [CompactSpace D.left] [QuasiSeparatedSpace D.left]

    [IsProper X.hom] [LocallyOfFinitePresentation X.hom]
    [IsProper Y.hom] [LocallyOfFinitePresentation Y.hom]
    [LocallyOfFinitePresentation U.hom] [LocallyOfFinitePresentation V.hom]
    [LocallyOfFinitePresentation F.hom] [QuasiCompact F.hom] [IsSeparated F.hom]
    (e : C ⟶ D) (r : D ⟶ F) [IsClosedImmersion r.left]
    (f : X ⟶ U) (g : Y ⟶ V) [IsProper f.left] [IsProper g.left]
    (i : U ⟶ F) (j : V ⟶ F) [IsClosedImmersion i.left] [IsClosedImmersion j.left]
    (qX : bsdhScheme G a ⟶ X.left) (qY : bsdhScheme G b ⟶ Y.left)
    (qU : (schubertVariety G (simpleWeylWord G.rootBase a)).scheme ⟶ U.left)
    (qV : (oppositeSchubertVariety G
      (G.longestElement * simpleWeylWord G.rootBase b)).scheme ⟶ V.left)
    (qF : (flagVariety G).scheme ⟶ F.left)
    (qC : (pairedBSDHSource G a b).left ⟶ C.left)
    (qD : (richardsonVariety G (G.longestElement * simpleWeylWord G.rootBase b)
      (simpleWeylWord G.rootBase a)).scheme ⟶ D.left)
    (hX : IsPullback qX (bsdhToSpec G a) X.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hY : IsPullback qY (bsdhToSpec G b) Y.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hU : IsPullback qU (schubertVariety G (simpleWeylWord G.rootBase a)).toSpec U.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hV : IsPullback qV (oppositeSchubertVariety G
      (G.longestElement * simpleWeylWord G.rootBase b)).toSpec V.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hF : IsPullback qF (flagVariety G).toSpec F.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hC : IsPullback qC (pairedBSDHSource G a b).hom C.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hD : IsPullback qD (richardsonVariety G
      (G.longestElement * simpleWeylWord G.rootBase b) (simpleWeylWord G.rootBase a)).toSpec
      D.hom (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hf : qX ≫ f.left = (bsdhSchubertMap G a ha).left ≫ qU)
    (hg : qY ≫ g.left = (bsdhOppositeSchubertMap G b hb).left ≫ qV)
    (hi : qU ≫ i.left = (schubertInclusion G (simpleWeylWord G.rootBase a)).left ≫ qF)
    (hj : qV ≫ j.left = (oppositeSchubertInclusion G
      (G.longestElement * simpleWeylWord G.rootBase b)).left ≫ qF)
    (he : qC ≫ e.left = (pairedRichardsonMap G a b ha hb).left ≫ qD)
    (hr : qD ≫ r.left = (richardsonInclusion G
      (G.longestElement * simpleWeylWord G.rootBase b) (simpleWeylWord G.rootBase a)).left ≫ qF)
    (start : CoefficientStage S) :
    PairedConnectedResult G a b ha hb S C D X Y U V F e r f g i j qX qY qF qC qD hC start := by
  classical
  obtain ⟨kA, hAstart, hAGC, _hAproper, _hAbase, _hAold, _hAfields, _hAcomp⟩ :=
    exists_word_endpoint_connected G a ha S hS F qF hF X U f i qX qU hX hU hf hi start
  obtain ⟨kB, _hBstart, hBGC, _hBproper, _hBbase, _hBold, _hBfields, _hBcomp⟩ :=
    exists_opposite_endpoint_connected G b hb S hS F qF hF Y V g j qY qV hY hV hg hj start
  obtain ⟨kR, _hRstart, rx, ry, hRx, hRy, _hRxComp, _hRyComp⟩ :=
    exists_richardson_projections G (G.longestElement * simpleWeylWord G.rootBase b)
      (simpleWeylWord G.rootBase a) S hS D U V F r i j qD qU qV qF
      hD hU hV hr hi hj start
  have hfRaw : bsdhMap G a ≫ qF = qX ≫ (f ≫ i).left := by
    exact ((endpoint_factor qX qU qF f.left i.left (bsdhSchubertMap G a ha).left
      (schubertInclusion G (simpleWeylWord G.rootBase a)).left hf hi).trans
      (congrArg (fun t => t ≫ qF) (bsdhSchubertMap_comp G a ha))).symm
  have hgRaw : (bsdhOppositeEndpoint G b).left ≫ qF = qY ≫ (g ≫ j).left := by
    exact ((endpoint_factor qY qV qF g.left j.left (bsdhOppositeSchubertMap G b hb).left
      (oppositeSchubertInclusion G (G.longestElement * simpleWeylWord G.rootBase b)).left
      hg hj).trans (congrArg (fun t => t ≫ qF)
        (congrArg Over.Hom.left (bsdhOppositeSchubertMap_comp G b hb)))).symm
  have heRaw : qC ≫ e.left ≫ r.left =
      (pullback.fst (Over.homMk (bsdhMap G a) rfl :
        (bsdhVariety G a).toOver ⟶ (flagVariety G).toOver) (bsdhOppositeEndpoint G b)).left ≫
        bsdhMap G a ≫ qF := by
    exact (endpoint_factor qC qD qF e.left r.left (pairedRichardsonMap G a b ha hb).left
      (richardsonInclusion G (G.longestElement * simpleWeylWord G.rootBase b)
        (simpleWeylWord G.rootBase a)).left he hr).trans
      ((congrArg (fun t => t ≫ qF)
        (congrArg Over.Hom.left (pairedRichardsonMap_comp G a b ha hb))).trans
          (Category.assoc _ _ _))
  obtain ⟨qP, hP, hProjX, hProjY, kI, _hIstart, E₀, hE₀hom, hE₀inv, _hE₀flag,
    eP, hChosen, hIncidence⟩ := exists_chosen_paired_incidence G a b S hS C X Y F
      (f ≫ i) (g ≫ j) qX qY qF hX hY hF hfRaw hgRaw qC hC D e r heRaw start
  obtain ⟨kAB, hAAB, hBAB⟩ := exists_ge_ge kA kB
  obtain ⟨kRI, hRRI, hIRI⟩ := exists_ge_ge kR kI
  obtain ⟨t, hABt, hRIt⟩ := exists_ge_ge kAB kRI
  have hAt : kA ≤ t := hAAB.trans hABt
  have hBt : kB ≤ t := hBAB.trans hABt
  have hRt : kR ≤ t := hRRI.trans hRIt
  have hIt : kI ≤ t := hIRI.trans hRIt
  let κ := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion t.property.2).toRingHom)
  let P := pairedIncidenceModel (f ≫ i) (g ≫ j)
  let Ct := stageScalarModel S C.hom t
  let Dt := stageScalarModel S D.hom t
  let ft := chosenScalarArrow κ f
  let gt := chosenScalarArrow κ g
  let it := chosenScalarArrow κ i
  let jt := chosenScalarArrow κ j
  let rt := chosenScalarArrow κ r
  let et := chosenScalarArrow κ e
  let rxt := extendModelMorphism S D.hom U.hom hRt rx
  let ryt := extendModelMorphism S D.hom V.hom hRt ry
  have hRxt : rxt ≫ it = rt := extend_triangle S r i hRt rx hRx
  have hRyt : ryt ≫ jt = rt := extend_triangle S r j hRt ry hRy
  let E := retainedIsoExtend S C.hom P.hom hIt E₀
  let mt := extendModelMorphism S P.hom D.hom hIt eP
  have hChosenT : E.hom ≫ mt = et := extend_iso_square S e hIt E₀ eP hChosen
  have hIncidenceT : mt ≫ rt = chosenScalarArrow κ (pairedIncidenceEndpoint (f ≫ i) (g ≫ j)) :=
    extend_triangle S (pairedIncidenceEndpoint (f ≫ i) (g ≫ j)) r hIt eP hIncidence
  obtain ⟨A, hAEnd, hAProjX, hAProjY⟩ := scalar_incidence_iso κ f g i j
  let EPair : Ct ≅ pairedIncidenceModel (ft ≫ it) (gt ≫ jt) := E ≪≫ A.symm
  let mPair : pairedIncidenceModel (ft ≫ it) (gt ≫ jt) ⟶ Dt := A.hom ≫ mt
  have hPair : EPair.hom ≫ mPair = et :=
    iso_factor_cancel E A mt et hChosenT
  have hPairEnd : mPair ≫ rt = pairedIncidenceEndpoint (ft ≫ it) (gt ≫ jt) :=
    (Category.assoc _ _ _).trans ((congrArg (fun p => A.hom ≫ p) hIncidenceT).trans hAEnd)
  let : IsProper ft.left := scalar_property (@IsProper) κ f inferInstance
  let : IsProper gt.left := scalar_property (@IsProper) κ g inferInstance
  let : GeometricallyConnected ft.left := stage_gc_mono S f hAt hAGC
  let : GeometricallyConnected gt.left := stage_gc_mono S g hBt hBGC
  let : IsClosedImmersion it.left := scalar_property (@IsClosedImmersion) κ i inferInstance
  let : IsClosedImmersion jt.left := scalar_property (@IsClosedImmersion) κ j inferInstance
  let : IsClosedImmersion rt.left := scalar_property (@IsClosedImmersion) κ r inferInstance
  have hPairProperties := pairedEndpoint_of_factors ft gt it jt rt rxt ryt hRxt hRyt
    mPair hPairEnd EPair et hPair
  let : GeometricallyConnected et.left := hPairProperties.2
  let EGeneric := chosenPairIso (Spec.map (CommRingCat.ofHom (algebraMap S K)))
    C P (pairedBSDHSource G a b).hom qC qP hC hP
  have hEhom : (modelScalarCone S C.hom).π.app (op t) ≫ E.hom.left =
      EGeneric.hom.left ≫ (modelScalarCone S P.hom).π.app (op t) :=
    extendModelMorphism_baseChange S C.hom P.hom hIt E₀.hom EGeneric.hom hE₀hom
  have hEinv : (modelScalarCone S P.hom).π.app (op t) ≫ E.inv.left =
      EGeneric.inv.left ≫ (modelScalarCone S C.hom).π.app (op t) :=
    extendModelMorphism_baseChange S P.hom C.hom hIt E₀.inv EGeneric.inv hE₀inv
  have hretained := retained_comparisons S C D F e r (pairedBSDHSource G a b)
    (richardsonVariety G (G.longestElement * simpleWeylWord G.rootBase b)
      (simpleWeylWord G.rootBase a)).toOver (flagVariety G).toOver
    (pairedRichardsonMap G a b ha hb)
    (richardsonInclusion G (G.longestElement * simpleWeylWord G.rootBase b)
      (simpleWeylWord G.rootBase a)) qC qD qF hC hD hF he hr t
  exact ⟨qP, hP, hProjX, hProjY, t, hAstart.trans hAt, E, hEhom, hEinv,
    A, hAEnd, hAProjX, hAProjY,
    hPairProperties.2, hPairProperties.1, et.w, chosenScalarArrow_snd κ e,
    (fun L hL y => @field_connected _ _ et.left hPairProperties.2 L hL y), hretained⟩

end SchubertGeometry
