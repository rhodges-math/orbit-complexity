import Batteries.Tactic.Lint
import OrbitComplexity.SchubertGeometry.Connectedness.AppendScalarModels
import OrbitComplexity.SchubertGeometry.Connectedness.AppendCellModels

/-! # Connected append stages from primitive curve intersections -/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReductiveGroups
open FrobeniusSplitting GroupActions Opposite

namespace SchubertGeometry

universe u v

/-- A stage at which the specified append fibres are geometrically connected. -/
def appendStageResult {K : Type u} [CommRing K] (S : Subalgebra ℤ K)
    {J : Type v} {N F : Over (Spec (.of S))} (n : N ⟶ F)
    (b : ∀ _j : J, Over.mk (𝟙 (Spec (.of S))) ⟶ F)
    (start : CoefficientStage S) : Prop :=
  ∃ (m : CoefficientStage S) (_ : start ≤ m), ∀ j,
    GeometricallyConnected (stageScalarModel S (fibreModel n (b j)).hom m).hom ∧
    ∀ (L : Type u) [Field L] (ρ : m.val →+* L),
      ConnectedSpace (pullback (Spec.map (CommRingCat.ofHom ρ))
        (stageScalarModel S (fibreModel n (b j)).hom m).hom : Scheme.{u})

private theorem finish_append_stage
    {K : Type u} [CommRing K] (S : Subalgebra ℤ K)
    {J : Type v} {N A Y F Q : Over (Spec (.of S))}
    (f : A ⟶ Y) (j : Y ⟶ F) [IsProper f.left] [GeometricallyConnected f.left]
    (n : N ⟶ F) (π : F ⟶ Q)
    (b : ∀ _r : J, Over.mk (𝟙 (Spec (.of S))) ⟶ F)
    (C : J → Over (Spec (.of S))) (c : ∀ r, C r ⟶ F)
    (hc : ∀ r, IsPullback (c r).left (C r).hom π.left (b r ≫ π).left)
    {t m : CoefficientStage S} (htm : t ≤ m)
    (hI : ∀ r, GeometricallyConnected
      (stageScalarModel S (intersectionModel (c r) j).hom t).hom)
    (d : stageScalarModel S N.hom m ⟶ stageScalarModel S A.hom m)
    (hg : IsPullback d.left
      (chosenScalarArrow
        (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion m.property.2).toRingHom)) n).left
      ((chosenScalarArrow
          (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion m.property.2).toRingHom))
            (f ≫ j)).left ≫
        (chosenScalarArrow
          (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion m.property.2).toRingHom)) π).left)
      (chosenScalarArrow
        (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion m.property.2).toRingHom)) π).left) :
    ∀ r, GeometricallyConnected (stageScalarModel S (fibreModel n (b r)).hom m).hom := by
  let κ := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion m.property.2).toRingHom)
  let fm := chosenScalarArrow κ f
  let jm := chosenScalarArrow κ j
  let nm := chosenScalarArrow κ n
  let πm := chosenScalarArrow κ π
  let : IsProper fm.left := appendModel_arrow_proper κ f
  let : GeometricallyConnected fm.left := appendModel_arrow_connected κ f
  have hg' : IsPullback d.left nm.left ((fm ≫ jm).left ≫ πm.left) πm.left :=
    appendModel_factor_square hg (congrArg Over.Hom.left (appendModel_composition κ f j))
  intro r
  let cm := chosenScalarArrow κ (c r)
  let bm := scalarPoint κ (b r)
  have hIm : GeometricallyConnected
      (stageScalarModel S (intersectionModel (c r) j).hom m).hom :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (stageScalarCartesian S (intersectionModel (c r) j).hom htm) (hI r)
  let : GeometricallyConnected (intersectionModel cm jm).hom :=
    appendModel_iso_connected (scalarIntersectionIso κ (c r) j) hIm
  have hcm : IsPullback cm.left ((scalarFunctor κ).obj (C r)).hom πm.left
      (bm ≫ πm).left :=
    appendModel_curve_base (appendModel_curve_cartesian κ (c r) π (b r ≫ π) (hc r))
      (appendModel_section_naturality κ π (b r))
  have hpoint := appendModel_point_connected fm jm nm πm d bm cm hg' hcm
  exact appendModel_iso_connected (pointScalarIso κ n (b r)) hpoint

private theorem bind_curve_family {K : Type u} [CommRing K] (S : Subalgebra ℤ K)
    {J : Type v} {I IK : J → Scheme.{u}}
    (a : ∀ r, I r ⟶ Spec (.of S)) (aK : ∀ r, IK r ⟶ Spec (.of K))
    (q : ∀ r, IK r ⟶ I r) (start : CoefficientStage S) {R : Prop}
    (h : ∃ (t : CoefficientStage S) (_ : start ≤ t)
      (qT : ∀ r, IK r ⟶ (stageScalarModel S (a r) t).left), ∀ r,
      IsPullback (qT r) (aK r) (stageScalarModel S (a r) t).hom
        (Spec.map (CommRingCat.ofHom (algebraMap t.val K))) ∧
      qT r ≫ pullback.snd
        (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion t.property.2).toRingHom))
          (a r) = q r ∧
      GeometricallyConnected (stageScalarModel S (a r) t).hom ∧
      ∀ (L : Type u) [Field L] (ρ : t.val →+* L),
        ConnectedSpace (pullback (Spec.map (CommRingCat.ofHom ρ))
          (stageScalarModel S (a r) t).hom : Scheme.{u}))
    (next : ∀ (t : CoefficientStage S) (_ : start ≤ t),
      (∀ r, GeometricallyConnected (stageScalarModel S (a r) t).hom) → R) : R := by
  obtain ⟨t, ht, _, ha⟩ := h
  exact next t ht (fun r => (ha r).2.2.1)

private theorem bind_incidence {P D : Type*} [Preorder D] {HP : P → Prop}
    {E A : D → Type*} {P₁ P₂ : P → Prop}
    {P₃ P₄ : ∀ p, HP p → ∀ m, E m → Prop}
    {P₅ : ∀ m, E m → Prop} {P₆ : ∀ m, E m → A m → Prop}
    {G : ∀ m, A m → Prop} {R : Prop} (start : D)
    (h : ∃ (p : P) (hp : HP p) (m : D) (_ : start ≤ m) (e : E m) (a : A m),
      P₁ p ∧ P₂ p ∧ P₃ p hp m e ∧ P₄ p hp m e ∧ P₅ m e ∧ P₆ m e a ∧ G m a)
    (next : ∀ (m : D) (_ : start ≤ m) (a : A m), G m a → R) : R := by
  obtain ⟨p, hp, m, hm, e, a, ha⟩ := h
  exact next m hm a ha.2.2.2.2.2.2

private theorem package_append_stage
    {K : Type u} [CommRing K] (S : Subalgebra ℤ K)
    {J : Type v} {N F : Over (Spec (.of S))} (n : N ⟶ F)
    (b : ∀ _r : J, Over.mk (𝟙 (Spec (.of S))) ⟶ F)
    (start m : CoefficientStage S) (hm : start ≤ m)
    (h : ∀ r, GeometricallyConnected
      (stageScalarModel S (fibreModel n (b r)).hom m).hom) :
    appendStageResult S n b start := by
  refine ⟨m, hm, fun r => ⟨h r, ?_⟩⟩
  let : GeometricallyConnected (stageScalarModel S (fibreModel n (b r)).hom m).hom := h r
  exact appendModel_field_connected _

/-- Primitive curve intersections give a geometrically connected append stage. -/
theorem append_from_primitive_curves
    {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (S : Subalgebra ℤ K) (hS : S.FG) (G : ReductiveGroupData K)
    (word : List G.rootBase.support) (v : G.weylGroup) (i : G.rootBase.support)
    {J : Type v} [Fintype J] (r : J → G.weylGroup)
    (hr : ∀ t, G.rootBase.IsPos (G.rootSystem.weylGroupToPerm (r t) i.val))
    (hrv : ∀ t, WeylBruhatLE G.rootBase (r t) v)
    {N A Y F Q : Over (Spec (.of S))}
    [CompactSpace N.left] [QuasiSeparatedSpace N.left]
    [CompactSpace A.left] [CompactSpace F.left]
    [LocallyOfFinitePresentation N.hom] [LocallyOfFinitePresentation A.hom]
    [LocallyOfFinitePresentation F.hom] [LocallyOfFinitePresentation Q.hom]
    (f : A ⟶ Y) [IsProper f.left] [GeometricallyConnected f.left]
    (j : Y ⟶ F) [IsClosedImmersion j.left] (n : N ⟶ F) (π : F ⟶ Q)
    (b : ∀ _t : J, Over.mk (𝟙 (Spec (.of S))) ⟶ F)
    (C : J → Over (Spec (.of S)))
    (E : ∀ t, Over.mk (projectiveToSpec S (ULift.{u} (Fin 2))) ≅ C t)
    (c : ∀ t, C t ⟶ F)
    (hc : ∀ t, IsPullback (c t).left (C t).hom π.left (b t ≫ π).left)
    (qN : bsdhScheme G (word ++ [i]) ⟶ N.left)
    (qA : bsdhScheme G word ⟶ A.left)
    (qY : (schubertVariety G v).scheme ⟶ Y.left)
    (qF : (flagVariety G).scheme ⟶ F.left)
    (qQ : (partialFlagVariety G {i}).scheme ⟶ Q.left)
    (qC : ∀ t,
      (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).scheme ⟶
        (C t).left)
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
    (hC : ∀ t, IsPullback (qC t)
      (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toSpec
      (C t).hom (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hn : qN ≫ n.left = bsdhMap G (word ++ [i]) ≫ qF)
    (ha : bsdhMap G word ≫ qF = qA ≫ (f ≫ j).left)
    (hj : (schubertInclusion G v).left ≫ qF = qY ≫ j.left)
    (hπ : (partialFlagMorphism G {i}).left ≫ qQ = qF ≫ π.left)
    (hd : ∀ t, (simpleSchubertCurve G (r t) i).left ≫ qF = qC t ≫ (c t).left)
    (hcoeff : ∀ t, qC t = simpleCurveCoefficientMap S G i ≫ (E t).hom.left)
    (start : CoefficientStage S) : appendStageResult S n b start := by
  let hcurves := @exists_simpleCurves_connected K _ _ _ S hS G J _
    r (fun _ => v) (fun _ => i) hr hrv C (fun _ => F) (fun _ => Y)
    (fun _ => inferInstance) E c (fun _ => j) (fun _ => inferInstance)
    qC (fun _ => qY) (fun _ => qF) hC (fun _ => hY) (fun _ => hF)
    hd (fun _ => hj) hcoeff start
  let aI (t : J) : (intersectionModel (c t) j).left ⟶ Spec (.of S) :=
    (intersectionModel (c t) j).hom
  let aIK (t : J) :
      pullback (simpleSchubertCurve G (r t) i).left (schubertInclusion G v).left ⟶
        Spec (.of K) :=
    pullback.fst (simpleSchubertCurve G (r t) i).left (schubertInclusion G v).left ≫
      (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toSpec
  let qI (t : J) :
      pullback (simpleSchubertCurve G (r t) i).left (schubertInclusion G v).left ⟶
        (intersectionModel (c t) j).left :=
    pullback.map (simpleSchubertCurve G (r t) i).left (schubertInclusion G v).left
      (c t).left j.left (qC t) qY qF (hd t) hj
  apply bind_curve_family S aI aIK qI start hcurves
  intro t ht hI
  apply bind_incidence t
    (exists_append_incidence_stage S hS G word i n (f ≫ j) π
      qN qA qF qQ hN hA hF hQ hn ha hπ t)
  intro m htm d hg
  exact package_append_stage S n b start m (le_trans ht htm)
    (finish_append_stage S f j n π b C c hc htm hI d hg)

end SchubertGeometry
