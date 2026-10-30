import Batteries.Tactic.Lint
import OrbitComplexity.SchubertGeometry.Connectedness.SimpleCurveIncidence
import OrbitComplexity.BruhatIntervals.Order.Basic
import OrbitComplexity.SchubertGeometry.Parabolics.PartialPoints

set_option autoImplicit false

/-! # Finite simple-curve comparisons at append Weyl points

The shorter representative of each simple parabolic Weyl coset determines
its positive-root curve. All specified partial-flag fibres are compared
with their projective models at one coefficient stage.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReductiveGroups
open FrobeniusSplitting GroupActions Opposite

namespace SchubertGeometry

universe u v

attribute [local instance] MvPolynomial.gradedAlgebra
private theorem choose_family {J : Type*} {A : J → Type*}
    (P : ∀ j, A j → Prop) (h : ∀ j, ∃ a, P j a) :
    ∃ a : ∀ j, A j, ∀ j, P j (a j) := by
  classical
  exact ⟨fun j => Classical.choose (h j), fun j => Classical.choose_spec (h j)⟩

private theorem shorter_step {B W : Type*} [Group W] {M : CoxeterMatrix B}
    (cs : CoxeterSystem M W) (v x : W) (i : B)
    (hv : cs.length v < cs.length (v * cs.simple i))
    (hx : cs.BruhatLE x (v * cs.simple i)) :
    ∃ r, ¬ cs.IsRightDescent r i ∧ cs.BruhatLE r v ∧
      (x = r ∨ x = r * cs.simple i) := by
  have htop : cs.IsRightDescent (v * cs.simple i) i := by
    change cs.length (v * cs.simple i * cs.simple i) < cs.length (v * cs.simple i)
    rw [cs.simple_mul_simple_cancel_right]
    exact hv
  by_cases hxi : cs.IsRightDescent x i
  · have hr : ¬ cs.IsRightDescent (x * cs.simple i) i :=
      cs.isRightDescent_iff_not_isRightDescent_mul.mp hxi
    have h := BruhatIntervals.bruhatLE_mul_of_ascent cs
      (hx.mul_simple_of_isRightDescent i htop) i hr
    rw [cs.simple_mul_simple_cancel_right] at h
    exact ⟨x * cs.simple i, hr, h, Or.inr (cs.simple_mul_simple_cancel_right i).symm⟩
  · have h := BruhatIntervals.bruhatLE_mul_of_ascent cs hx i hxi
    rw [cs.simple_mul_simple_cancel_right] at h
    exact ⟨x, hxi, h, Or.inl rfl⟩

private theorem positive_of_ascent
    {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K) (w : G.weylGroup) (i : G.rootBase.support)
    (h : ¬ (weylCoxeterSystem G.rootBase).IsRightDescent w i) :
    G.rootBase.IsPos (G.rootSystem.weylGroupToPerm w i.val) := by
  by_contra hn
  have hneg := (root_height_neg_iff_not_isPos G.rootBase
    (G.rootSystem.weylGroupToPerm w i.val)).mpr hn
  have hcount := rootInversionCount_mul_simple_of_neg G.rootBase w i hneg
  apply h
  change (weylCoxeterSystem G.rootBase).length
      (w * (weylCoxeterSystem G.rootBase).simple i) <
    (weylCoxeterSystem G.rootBase).length w
  simp only [weylCoxeterSystem_simple, weylCoxeterSystem_length]
  omega

private theorem partial_step
    {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K) (r x : G.weylGroup) (i : G.rootBase.support)
    (h : x = r ∨ x = r * RootPairing.weylGroup.ofIdx G.rootSystem i.val) :
    (weylFlagPoint G r).val ≫ (partialFlagMorphism G {i}).left =
      (weylFlagPoint G x).val ≫ (partialFlagMorphism G {i}).left := by
  have hmem : r⁻¹ * x ∈ standardParabolicSubgroup G.rootBase {i} := by
    rcases h with rfl | rfl
    · simp only [inv_mul_cancel]
      exact (standardParabolicSubgroup G.rootBase {i}).one_mem
    · simpa only [inv_mul_cancel_left] using
        simple_mem_standardParabolicSubgroup G.rootBase {i} i (Set.mem_singleton i)
  have hp := (partialWeylFlag_eq_iff G {i} r x).mpr hmem
  have he := congrArg (partialFlagPointsEquiv G {i}) hp
  have hr := partialFlagMorphism_points G {i} (flagProjection G (G.weylPoint r))
  have hx := partialFlagMorphism_points G {i} (flagProjection G (G.weylPoint x))
  exact congrArg (fun p : (partialFlagVariety G {i}).points => p.val)
    (hr.trans (he.trans hx.symm))

private theorem shorter_family
    {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K) (v : G.weylGroup) (i : G.rootBase.support)
    {J : Type v} (x : J → G.weylGroup)
    (hv : (weylCoxeterSystem G.rootBase).length v <
      (weylCoxeterSystem G.rootBase).length
        (v * RootPairing.weylGroup.ofIdx G.rootSystem i.val))
    (hx : ∀ j, WeylBruhatLE G.rootBase (x j)
      (v * RootPairing.weylGroup.ofIdx G.rootSystem i.val)) :
    ∃ r : J → G.weylGroup,
      (∀ j, G.rootBase.IsPos (G.rootSystem.weylGroupToPerm (r j) i.val)) ∧
      (∀ j, WeylBruhatLE G.rootBase (r j) v) ∧
      (∀ j, x j = r j ∨ x j = r j * RootPairing.weylGroup.ofIdx G.rootSystem i.val) ∧
      ∀ j, (weylFlagPoint G (r j)).val ≫ (partialFlagMorphism G {i}).left =
        (weylFlagPoint G (x j)).val ≫ (partialFlagMorphism G {i}).left := by
  classical
  have h (j : J) := shorter_step (weylCoxeterSystem G.rootBase) v (x j) i
    (by simpa only [weylCoxeterSystem_simple] using hv)
    (by simpa only [weylCoxeterSystem_simple] using
      (weyl_bruhat_iff G.rootBase _ _).mp (hx j))
  let r (j : J) := Classical.choose (h j)
  have hr (j : J) :
      ¬ (weylCoxeterSystem G.rootBase).IsRightDescent (r j) i ∧
      (weylCoxeterSystem G.rootBase).BruhatLE (r j) v ∧
      (x j = r j ∨ x j = r j * (weylCoxeterSystem G.rootBase).simple i) :=
    Classical.choose_spec (h j)
  refine ⟨r, fun j => positive_of_ascent G (r j) i (hr j).1,
    fun j => (weyl_bruhat_iff G.rootBase _ _).mpr (hr j).2.1, ?_, ?_⟩
  · intro j
    simpa only [weylCoxeterSystem_simple] using (hr j).2.2
  · intro j
    apply partial_step G (r j) (x j) i
    simpa only [weylCoxeterSystem_simple] using (hr j).2.2

private theorem partial_endpoint_triangle {T : Type*} [Category T]
    {X F P F₀ Q₀ B : T} (r x : X ⟶ F) (πK : F ⟶ P)
    (qF : F ⟶ F₀) (qQ : P ⟶ Q₀) (π : F₀ ⟶ Q₀)
    (κ : X ⟶ B) (b : B ⟶ F₀)
    (hrx : r ≫ πK = x ≫ πK) (hπ : πK ≫ qQ = qF ≫ π)
    (hb : x ≫ qF = κ ≫ b) :
    (r ≫ πK) ≫ qQ = κ ≫ (b ≫ π) := by
  calc
    (r ≫ πK) ≫ qQ = (x ≫ πK) ≫ qQ := congrArg (fun f => f ≫ qQ) hrx
    _ = x ≫ (qF ≫ π) :=
      (Category.assoc _ _ _).trans (congrArg (fun f => x ≫ f) hπ)
    _ = (κ ≫ b) ≫ π := (Category.assoc _ _ _).symm.trans
      (congrArg (fun f => f ≫ π) hb)
    _ = κ ≫ (b ≫ π) := Category.assoc _ _ _

private theorem bind_witness {A : Type*} {P : A → Prop} {Q : Prop}
    (h : ∃ a, P a) (next : ∀ a, P a → Q) : Q := by
  obtain ⟨a, ha⟩ := h
  exact next a ha

private def curve_family_result
    {K : Type u} [CommRing K] (S : Subalgebra ℤ K)
    {J : Type v} {XK FK : Over (Spec (.of K))} {F Q : Over (Spec (.of S))}
    (π : F ⟶ Q) (b : ∀ _j : J, Over.mk (𝟙 (Spec (.of S))) ⟶ Q)
    (fK : J → (XK ⟶ FK)) (qF : FK.left ⟶ F.left)
    (q : ∀ j, XK.left ⟶ (fibreModel π (b j)).left)
    (h : ∀ j, IsPullback (q j) XK.hom (fibreModel π (b j)).hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (qStd : XK.left ⟶ projectiveScheme S (ULift.{u} (Fin 2)))
    (hStd : IsPullback qStd XK.hom (projectiveToSpec S (ULift.{u} (Fin 2)))
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (qR : ∀ k : CoefficientStage S, XK.left ⟶ projectiveScheme k.val (ULift.{u} (Fin 2)))
    (start : CoefficientStage S) : Prop :=
  let P := Over.mk (projectiveToSpec S (ULift.{u} (Fin 2)))
  let W := fun j => fibreModel π (b j)
  let κ := Spec.map (CommRingCat.ofHom (algebraMap S K))
  let EG := fun j => chosenPairIso κ P (W j) XK.hom qStd (q j) hStd (h j)
  ∃ (k : CoefficientStage S) (_ : start ≤ k)
    (E₀ : ∀ j, stageScalarModel S P.hom k ≅ stageScalarModel S (W j).hom k)
    (E : ∀ j, Over.mk (projectiveToSpec k.val (ULift.{u} (Fin 2))) ≅
      stageScalarModel S (W j).hom k)
    (qC : ∀ j, XK.left ⟶ (stageScalarModel S (W j).hom k).left)
    (qF₀ : FK.left ⟶ (stageScalarModel S F.hom k).left),
    (∀ j, E j = projectiveStageIso S (ULift.{u} (Fin 2)) k ≪≫ E₀ j) ∧
    (∀ j, (modelScalarCone S P.hom).π.app (op k) ≫ (E₀ j).hom.left =
      (EG j).hom.left ≫ (modelScalarCone S (W j).hom).π.app (op k)) ∧
    (∀ j, (modelScalarCone S (W j).hom).π.app (op k) ≫ (E₀ j).inv.left =
      (EG j).inv.left ≫ (modelScalarCone S P.hom).π.app (op k)) ∧
    (∀ j, IsPullback (qC j) XK.hom (stageScalarModel S (W j).hom k).hom
      (Spec.map (CommRingCat.ofHom (algebraMap k.val K)))) ∧
    IsPullback qF₀ FK.hom (stageScalarModel S F.hom k).hom
      (Spec.map (CommRingCat.ofHom (algebraMap k.val K))) ∧
    (∀ j, qC j ≫ pullback.snd
      (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom))
        (W j).hom = q j) ∧
    (qF₀ ≫ pullback.snd
      (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom))
        F.hom = qF) ∧
    (∀ j, qC j = qR k ≫ (E j).hom.left) ∧
    (∀ j, (fK j).left ≫ qF₀ = qC j ≫ (chosenScalarArrow
      (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom))
        (fibreProjection π (b j))).left) ∧
    ∀ j, IsPullback (chosenScalarArrow
      (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom))
        (fibreProjection π (b j))).left (stageScalarModel S (W j).hom k).hom
      (chosenScalarArrow
        (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom)) π).left
      (scalarSection
        (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom))
          Q.hom (b j).left (b j).w)

private theorem retain_curve_family
    {K : Type u} [CommRing K] (S : Subalgebra ℤ K) (hS : S.FG)
    {J : Type v} [Fintype J] {XK FK : Over (Spec (.of K))}
    {F Q : Over (Spec (.of S))} (π : F ⟶ Q)
    [LocallyOfFinitePresentation π.left] [QuasiCompact π.left] [IsSeparated π.left]
    (b : ∀ _j : J, Over.mk (𝟙 (Spec (.of S))) ⟶ Q) (fK : J → (XK ⟶ FK))
    (qF : FK.left ⟶ F.left)
    (hF : IsPullback qF FK.hom F.hom (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (q : ∀ j, XK.left ⟶ (fibreModel π (b j)).left)
    (h : ∀ j, IsPullback (q j) XK.hom (fibreModel π (b j)).hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hq : ∀ j, q j ≫ (fibreProjection π (b j)).left = (fK j).left ≫ qF)
    (qStd : XK.left ⟶ projectiveScheme S (ULift.{u} (Fin 2)))
    (hStd : IsPullback qStd XK.hom (projectiveToSpec S (ULift.{u} (Fin 2)))
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (qR : ∀ k : CoefficientStage S, XK.left ⟶ projectiveScheme k.val (ULift.{u} (Fin 2)))
    (hcoeff : ∀ k : CoefficientStage S,
      qR k ≫ (projectiveStageIso S (ULift.{u} (Fin 2)) k).hom.left =
        hStd.flip.isoOverPullback.hom.left ≫
          genericLeg S (projectiveToSpec S (ULift.{u} (Fin 2))) k)
    (start : CoefficientStage S) :
    curve_family_result S π b fK qF q h qStd hStd qR start := by
  let P : Over (Spec (.of S)) := Over.mk (projectiveToSpec S (ULift.{u} (Fin 2)))
  let W := fun j => fibreModel π (b j)
  let : Algebra.FiniteType ℤ S := (Subalgebra.fg_iff_finiteType S).mp hS
  let : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing ℤ S
  let : LocallyOfFinitePresentation P.hom := inferInstanceAs
    (LocallyOfFinitePresentation (projectiveToSpec S (ULift.{u} (Fin 2))))
  let : IsLocallyNoetherian P.left := LocallyOfFiniteType.isLocallyNoetherian P.hom
  have hPC : CompactSpace P.left :=
    QuasiCompact.compactSpace_of_compactSpace (projectiveToSpec S (ULift.{u} (Fin 2)))
  have hPQ : QuasiSeparatedSpace P.left := inferInstance
  have hWL (j : J) : LocallyOfFinitePresentation (W j).hom :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback π.left (b j).left) inferInstance
  have hWC (j : J) : CompactSpace (W j).left := by
    let : QuasiCompact (W j).hom :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (IsPullback.of_hasPullback π.left (b j).left) inferInstance
    exact QuasiCompact.compactSpace_of_compactSpace (W j).hom
  have hWQ (j : J) : QuasiSeparatedSpace (W j).left := by
    let : IsSeparated (W j).hom :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (IsPullback.of_hasPullback π.left (b j).left) inferInstance
    exact quasiSeparatedSpace_of_quasiSeparated (W j).hom
  let κ := Spec.map (CommRingCat.ofHom (algebraMap S K))
  let EG := fun j => chosenPairIso κ P (W j) XK.hom qStd (q j) hStd (h j)
  apply bind_witness (@exists_retained_isos K _ S J _ hS
    (fun _ => P.left) (fun j => (W j).left)
    (fun _ => hPC) (fun _ => hPQ) hWC hWQ
    (fun _ => P.hom) (fun j => (W j).hom)
    (fun _ => inferInstance) hWL EG start)
  intro k hk
  obtain ⟨hstart, E₀, hhom, hinv⟩ := hk
  let E := fun j => projectiveStageIso S (ULift.{u} (Fin 2)) k ≪≫ E₀ j
  let qC := fun j => modelStageMap S (W j).hom XK.hom (q j) (h j) k
  let qF₀ := modelStageMap S F.hom FK.hom qF hF k
  have hn (j : J) : qC j = qR k ≫ (E j).hom.left := by
    have hcommon : hStd.flip.isoOverPullback.hom.left ≫ (EG j).hom.left =
        (h j).flip.isoOverPullback.hom.left :=
      congrArg Over.Hom.left
        (scalarComparison_iso_triangle hStd.flip.isoOverPullback (h j).flip.isoOverPullback)
    exact scalarCurve_comparison_triangle
      hStd.flip.isoOverPullback.hom.left (h j).flip.isoOverPullback.hom.left
      (EG j).hom.left (genericLeg S P.hom k) (genericLeg S (W j).hom k)
      (E₀ j).hom.left (projectiveStageIso S (ULift.{u} (Fin 2)) k).hom.left (qR k)
      (E j).hom.left (qC j) hcommon (hhom j) (hcoeff k) rfl rfl
  exact ⟨k, hstart, E₀, E, qC, qF₀, fun _ => rfl, hhom, hinv,
    fun j => modelStageMap_cartesian S (W j).hom XK.hom (q j) (h j) k,
    modelStageMap_cartesian S F.hom FK.hom qF hF k,
    fun j => modelStageMap_projection S (W j).hom XK.hom (q j) (h j) k,
    modelStageMap_projection S F.hom FK.hom qF hF k, hn,
    fun j => (modelStageMap_naturality S (fK j) (fibreProjection π (b j))
      (q j) qF (h j) hF (hq j) k).symm,
    fun j => scalarFibre_cartesian _ π (b j)⟩

private theorem retain_raw_family
    {K : Type u} [CommRing K] (S : Subalgebra ℤ K) (hS : S.FG)
    {J : Type v} [Fintype J] {XK FK : Over (Spec (.of K))}
    {F Q : Over (Spec (.of S))} (π : F ⟶ Q)
    [LocallyOfFinitePresentation π.left] [QuasiCompact π.left] [IsSeparated π.left]
    (b : ∀ _j : J, Over.mk (𝟙 (Spec (.of S))) ⟶ Q) (fK : J → (XK ⟶ FK))
    (qF : FK.left ⟶ F.left)
    (hF : IsPullback qF FK.hom F.hom (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (raw : ∀ j, ∃ q : XK.left ⟶ (fibreModel π (b j)).left,
      IsPullback q XK.hom (fibreModel π (b j)).hom
        (Spec.map (CommRingCat.ofHom (algebraMap S K))) ∧
      q ≫ (fibreProjection π (b j)).left = (fK j).left ≫ qF ∧
      q ≫ (fibreModel π (b j)).hom =
        XK.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap S K)))
    (qStd : XK.left ⟶ projectiveScheme S (ULift.{u} (Fin 2)))
    (hStd : IsPullback qStd XK.hom (projectiveToSpec S (ULift.{u} (Fin 2)))
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (qR : ∀ k : CoefficientStage S, XK.left ⟶ projectiveScheme k.val (ULift.{u} (Fin 2)))
    (hcoeff : ∀ k : CoefficientStage S,
      qR k ≫ (projectiveStageIso S (ULift.{u} (Fin 2)) k).hom.left =
        hStd.flip.isoOverPullback.hom.left ≫
          genericLeg S (projectiveToSpec S (ULift.{u} (Fin 2))) k)
    (start : CoefficientStage S) :
    ∃ q : ∀ j, XK.left ⟶ (fibreModel π (b j)).left,
      ∃ h : ∀ j, IsPullback (q j) XK.hom (fibreModel π (b j)).hom
        (Spec.map (CommRingCat.ofHom (algebraMap S K))),
      (∀ j, q j ≫ (fibreProjection π (b j)).left = (fK j).left ≫ qF) ∧
      (∀ j, q j ≫ (fibreModel π (b j)).hom =
        XK.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap S K))) ∧
      curve_family_result S π b fK qF q h qStd hStd qR start := by
  apply bind_witness (choose_family _ raw)
  intro q hq
  exact ⟨q, fun j => (hq j).1, fun j => (hq j).2.1, fun j => (hq j).2.2,
    retain_curve_family S hS π b fK qF hF q (fun j => (hq j).1)
      (fun j => (hq j).2.1) qStd hStd qR hcoeff start⟩

private theorem extend_witness {A : Type*} {P Q : A → Prop}
    (h : ∃ a, P a) (next : ∀ a, P a → Q a) : ∃ a, P a ∧ Q a := by
  obtain ⟨a, ha⟩ := h
  exact ⟨a, ha, next a ha⟩

/-- The shorter Weyl representatives and the specified partial-flag fibres
receive projective comparisons and both original projections at one coefficient stage. -/
theorem exists_append_weyl_curves
    {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (S : Subalgebra ℤ K) (hS : S.FG) (G : ReductiveGroupData K)
    (v : G.weylGroup) (i : G.rootBase.support) {J : Type v} [Fintype J]
    (x : J → G.weylGroup)
    (hv : (weylCoxeterSystem G.rootBase).length v <
      (weylCoxeterSystem G.rootBase).length
        (v * RootPairing.weylGroup.ofIdx G.rootSystem i.val))
    (hx : ∀ j, WeylBruhatLE G.rootBase (x j)
      (v * RootPairing.weylGroup.ofIdx G.rootSystem i.val))
    (F Q : Over (Spec (.of S))) (π : F ⟶ Q)
    [LocallyOfFinitePresentation π.left] [QuasiCompact π.left] [IsSeparated π.left]
    (qF : (flagVariety G).scheme ⟶ F.left)
    (qQ : (partialFlagVariety G {i}).scheme ⟶ Q.left)
    (hF : IsPullback qF (flagVariety G).toSpec F.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hπ : IsPullback (partialFlagMorphism G {i}).left qF qQ π.left)
    (b : ∀ _j : J, Over.mk (𝟙 (Spec (.of S))) ⟶ F)
    (hb : ∀ j, (weylFlagPoint G (x j)).val ≫ qF =
      Spec.map (CommRingCat.ofHom (algebraMap S K)) ≫ (b j).left)
    (start : CoefficientStage S) :
    ∃ r : J → G.weylGroup,
      ((∀ j, G.rootBase.IsPos (G.rootSystem.weylGroupToPerm (r j) i.val)) ∧
        (∀ j, WeylBruhatLE G.rootBase (r j) v) ∧
        (∀ j, x j = r j ∨ x j = r j * RootPairing.weylGroup.ofIdx G.rootSystem i.val) ∧
        ∀ j, (weylFlagPoint G (r j)).val ≫ (partialFlagMorphism G {i}).left =
          (weylFlagPoint G (x j)).val ≫ (partialFlagMorphism G {i}).left) ∧
      ∃ q : ∀ j,
          (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).scheme ⟶
            (fibreModel π (b j ≫ π)).left,
        ∃ h : ∀ j, IsPullback (q j)
          (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toSpec
          (fibreModel π (b j ≫ π)).hom
          (Spec.map (CommRingCat.ofHom (algebraMap S K))),
        (∀ j, q j ≫ (fibreProjection π (b j ≫ π)).left =
          (simpleSchubertCurve G (r j) i).left ≫ qF) ∧
        (∀ j, q j ≫ (fibreModel π (b j ≫ π)).hom =
          (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toSpec ≫
            Spec.map (CommRingCat.ofHom (algebraMap S K))) ∧
        curve_family_result S π (fun j => b j ≫ π)
          (fun j => simpleSchubertCurve G (r j) i) qF q h
          (simpleCurveCoefficientMap S G i) (curveModel_projective_square S G i)
          (fun k => simpleCurveCoefficientMap k.val G i) start := by
  apply extend_witness (shorter_family G v i x hv hx)
  intro r hr
  apply retain_raw_family S hS π (fun j => b j ≫ π)
    (fun j => simpleSchubertCurve G (r j) i) qF hF
  · intro j
    exact simpleCurve_raw_comparison S G (r j) i F Q π qF qQ hπ (b j ≫ π)
      (partial_endpoint_triangle (weylFlagPoint G (r j)).val
        (weylFlagPoint G (x j)).val (partialFlagMorphism G {i}).left qF qQ π.left
        (Spec.map (CommRingCat.ofHom (algebraMap S K))) (b j).left
        (hr.2.2.2 j) hπ.w (hb j))
  · exact projectiveStage_coefficient_agreement S G i

-- GAP: C6-STAGE. Apply these finite projective comparisons to the preceding
-- Schubert model, retain the cell-product comparisons on the same coefficient
-- stage, and use the cell cover in the endpoint induction.

end SchubertGeometry
