import OrbitComplexity.SchubertGeometry.Connectedness.RestrictedCurveStage
import OrbitComplexity.SchubertGeometry.Connectedness.AppendScalarModels
import Batteries.Tactic.Lint
import OrbitComplexity.FrobeniusSplitting.Normality.Connectedness.PolynomialGeometric
import OrbitComplexity.FrobeniusSplitting.Normality.Limits.ModelMorphismDescent
import OrbitComplexity.GroupActions.Varieties.ProjectiveConnected
import OrbitComplexity.SchubertGeometry.Connectedness.CellModelMaps

set_option autoImplicit false

/-! # Connected geometric fibres of cell and projective stage models

The polynomial contraction of a cell model gives connected geometric fibres
over its arithmetic base. This property passes to each coefficient stage,
as it does for the projective-line models used by reflection-root curves.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
  ReductiveGroups FrobeniusSplitting GroupActions

namespace SchubertGeometry.CellContraction

universe u

private theorem geomConnected_rewrite {X Y : Scheme.{u}} (f g : X ⟶ Y)
    (h : f = g) (hg : GeometricallyConnected g) : GeometricallyConnected f := by
  rw [h]
  exact hg

private theorem pullback_geomConnected {B T X : Scheme.{u}}
    (κ : T ⟶ B) (a : X ⟶ B) (U : Over T) (q : U.left ⟶ X)
    (sq : IsPullback U.hom q κ a) (f : U.left ⟶ T) (hf : f = U.hom)
    (ha : GeometricallyConnected a) : GeometricallyConnected f :=
  geomConnected_rewrite f U.hom hf
    (MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @GeometricallyConnected) sq.flip ha)

private theorem scalar_geomConnected {K : Type u} [CommRing K]
    (S : Subalgebra ℤ K) {X : Scheme.{u}} (a : X ⟶ Spec (.of S))
    (k : CoefficientStage S) (ha : GeometricallyConnected a) :
    GeometricallyConnected (stageScalarModel S a k).hom := by
  let κ := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom)
  exact pullback_geomConnected κ a (Over.mk (pullback.fst κ a)) (pullback.snd κ a)
    (IsPullback.of_hasPullback κ a) (stageScalarModel S a k).hom rfl ha

/-- The projective-line structural map has connected geometric fibres at each
coefficient stage. -/
theorem projectiveStage_geomConnected {K : Type u} [CommRing K]
    (R : Subalgebra ℤ K) (k : CoefficientStage R) :
    GeometricallyConnected
      (stageScalarModel R (projectiveToSpec R (ULift.{u} (Fin 2))) k).hom :=
  scalar_geomConnected R (projectiveToSpec R (ULift.{u} (Fin 2))) k
    (projectiveToSpec_geometricallyConnected R (ULift.{u} (Fin 2)))

attribute [local instance] coefficientAlgebra

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K) {R : Subalgebra ℤ K}

/-- The structural map of an arithmetic cell model has connected geometric
fibres by its polynomial contraction and scalar origin. -/
theorem cellArithmeticBase_geomConnected (a b w : G.weylGroup)
    (hne : Nonempty (cellIntersection G a b w).left)
    (M : ArithmeticContractionModel (R := R)
      (cellContractionAlg G a b w) (cellOriginAlg G a b w hne)) :
    GeometricallyConnected (cellArithmeticBase G a b w hne M) :=
  geomConnected_rewrite (cellArithmeticBase G a b w hne M)
    (Spec.map (CommRingCat.ofHom (algebraMap R M.model))) rfl
    (geomConnected_of_polynomial M.family M.origin M.one M.zero)

/-- The structural map of the same arithmetic cell model has connected
geometric fibres at each coefficient stage. -/
theorem cellArithmeticStage_geomConnected (a b w : G.weylGroup)
    (hne : Nonempty (cellIntersection G a b w).left)
    (M : ArithmeticContractionModel (R := R)
      (cellContractionAlg G a b w) (cellOriginAlg G a b w hne))
    (k : CoefficientStage R) :
    GeometricallyConnected
      (stageScalarModel R (cellArithmeticBase G a b w hne M) k).hom :=
  scalar_geomConnected R (cellArithmeticBase G a b w hne M) k
    (cellArithmeticBase_geomConnected G a b w hne M)

end SchubertGeometry.CellContraction


namespace SchubertGeometry

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReductiveGroups
open FrobeniusSplitting GroupActions Opposite CellContraction
open CartesianMonoidalCategory MonoidalCategory

universe u v

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] Over.cartesianMonoidalCategory

/-- Use an existential hypothesis to prove a fixed proposition. -/
theorem curveData_elim {A : Type*} {P : A → Prop} {Q : Prop}
    (h : ∃ a, P a) (next : ∀ a, P a → Q) : Q := by
  obtain ⟨a, ha⟩ := h
  exact next a ha

private theorem branch_result {P Q R : Prop} (h : P ∨ Q)
    (hp : P → R) (hq : Q → R) : R := h.elim hp hq

private theorem restricted_branch {C A : Type*}
    {p q r : C → Prop} {n : C → ℕ → Prop} {s : A → Prop} {R : Prop}
    (h : ∃ c, p c ∧ q c ∧ r c ∧ (∃ N : ℕ, 0 < N ∧ n c N) ∧ ∃ a, s a)
    (next : ∀ c, p c → q c → r c → ∀ N : ℕ, 0 < N → n c N → ∀ a, s a → R) : R := by
  obtain ⟨c, hp, hq, hr, hn, hs⟩ := h
  obtain ⟨N, hN, hn⟩ := hn
  obtain ⟨a, ha⟩ := hs
  exact next c hp hq hr N hN hn a ha

private theorem trim_curve_data {J : Type*} {A B C : J → Type*}
    {p : ∀ j, A j → B j → Prop} {q r : ∀ j, B j → Prop}
    {s : ∀ j, A j → B j → Prop} {t n : ∀ j, C j → Prop}
    {z : ∀ j, A j → C j → Prop} {g f : J → Prop}
    (h : ∃ j a b, p j a b ∧ q j b ∧ r j b ∧ s j a b ∧
      ∃ c, t j c ∧ n j c ∧ z j a c ∧ g j ∧ f j) :
    ∃ j b, q j b ∧ r j b ∧ g j ∧ f j := by
  obtain ⟨j, _, b, _, hq, hr, _, _, _, _, _, hg, hf⟩ := h
  exact ⟨j, b, hq, hr, hg, hf⟩

private def scalar_iso {B T : Scheme.{u}} (κ : T ⟶ B)
    {P Q : Over B} (E : P ≅ Q) :
    Over.mk (pullback.fst κ P.hom) ≅ Over.mk (pullback.fst κ Q.hom) where
  hom := chosenScalarArrow κ E.hom
  inv := chosenScalarArrow κ E.inv
  hom_inv_id := by
    apply (Over.forget T).map_injective
    have h : E.hom.left ≫ E.inv.left = 𝟙 P.left :=
      congrArg (fun f : P ⟶ P => f.left) E.hom_inv_id
    apply pullback.hom_ext
    · simp [chosenScalarArrow, Category.assoc]
    · simp [chosenScalarArrow, Category.assoc, h]
  inv_hom_id := by
    apply (Over.forget T).map_injective
    have h : E.inv.left ≫ E.hom.left = 𝟙 Q.left :=
      congrArg (fun f : Q ⟶ Q => f.left) E.inv_hom_id
    apply pullback.hom_ext
    · simp [chosenScalarArrow, Category.assoc]
    · simp [chosenScalarArrow, Category.assoc, h]

private theorem over_iso_gc {B : Scheme.{u}} {P Q : Over B}
    (E : P ≅ Q) [GeometricallyConnected Q.hom] : GeometricallyConnected P.hom := by
  have h := geomConnected_comp_iso ((Over.forget B).mapIso E) Q.hom
  have he : E.hom.left ≫ Q.hom = P.hom := E.hom.w
  exact he ▸ h

private theorem closed_intersection_properties
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {C F Y : Over (Spec (.of R))}
    [LocallyOfFinitePresentation F.hom]
    (E : Over.mk (projectiveToSpec R (ULift.{u} (Fin 2))) ≅ C)
    (d : C ⟶ F) (j : Y ⟶ F) [IsClosedImmersion j.left] :
    LocallyOfFinitePresentation (pullback.fst d.left j.left ≫ C.hom) ∧
      CompactSpace (pullback d.left j.left : Scheme.{u}) ∧
      QuasiSeparatedSpace (pullback d.left j.left : Scheme.{u}) := by
  let : IsLocallyNoetherian F.left := LocallyOfFiniteType.isLocallyNoetherian F.hom
  let : LocallyOfFinitePresentation j.left := inferInstance
  have hC : E.inv.left ≫ projectiveToSpec R (ULift.{u} (Fin 2)) = C.hom := E.inv.w
  let : LocallyOfFinitePresentation C.hom := hC ▸ inferInstanceAs
    (LocallyOfFinitePresentation (E.inv.left ≫ projectiveToSpec R (ULift.{u} (Fin 2))))
  let : IsProper C.hom := hC ▸ inferInstanceAs
    (IsProper (E.inv.left ≫ projectiveToSpec R (ULift.{u} (Fin 2))))
  let : CompactSpace C.left := QuasiCompact.compactSpace_of_compactSpace C.hom
  let : LocallyOfFinitePresentation (pullback.fst d.left j.left ≫ C.hom) := inferInstance
  let : CompactSpace (pullback d.left j.left : Scheme.{u}) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.fst d.left j.left)
  let : IsLocallyNoetherian (pullback d.left j.left : Scheme.{u}) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.fst d.left j.left ≫ C.hom)
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- The comparison isomorphism determined by a Cartesian coefficient square. -/
def curveCoefficientIso {B T X : Scheme.{u}} (κ : T ⟶ B)
    {M : Over B} (b : X ⟶ T) (q : X ⟶ M.left) (h : IsPullback q b M.hom κ) :
    Over.mk b ≅ Over.mk (pullback.fst κ M.hom) :=
  Over.isoMk h.flip.isoPullback h.flip.isoPullback_hom_fst

private theorem field_connected {R : Type u} [CommRing R] {X : Scheme.{u}}
    (b : X ⟶ Spec (.of R)) [GeometricallyConnected b]
    (L : Type u) [Field L] (ρ : R →+* L) :
    ConnectedSpace (pullback (Spec.map (CommRingCat.ofHom ρ)) b : Scheme.{u}) := by
  let : GeometricallyConnected (pullback.fst (Spec.map (CommRingCat.ofHom ρ)) b) :=
    inferInstance
  exact GeometricallyConnected.connectedSpace_of_subsingleton
    (f := pullback.fst (Spec.map (CommRingCat.ofHom ρ)) b)

/-- A connected coefficient-stage fibre of a specified curve intersection. -/
def curveFibreResult
    {K : Type u} [CommRing K] (S : Subalgebra ℤ K)
    {I IK : Scheme.{u}} (b : I ⟶ Spec (.of S)) (bK : IK ⟶ Spec (.of K))
    (qI : IK ⟶ I) : Prop :=
  ∃ (k : CoefficientStage S) (qK : IK ⟶ (stageScalarModel S b k).left),
    IsPullback qK bK (stageScalarModel S b k).hom
      (Spec.map (CommRingCat.ofHom (algebraMap k.val K))) ∧
    qK ≫ pullback.snd
      (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom)) b = qI ∧
    GeometricallyConnected (stageScalarModel S b k).hom ∧
    ∀ (L : Type u) [Field L] (ρ : k.val →+* L),
      ConnectedSpace (pullback (Spec.map (CommRingCat.ofHom ρ))
        (stageScalarModel S b k).hom : Scheme.{u})

private theorem whole_curve_stage
    {K : Type u} [CommRing K] (S : Subalgebra ℤ K) (hS : S.FG)
    {I IK CK : Scheme.{u}} (b : I ⟶ Spec (.of S))
    [CompactSpace I] [QuasiSeparatedSpace I] [LocallyOfFinitePresentation b]
    {C : Over (Spec (.of S))}
    (E : Over.mk (projectiveToSpec S (ULift.{u} (Fin 2))) ≅ C)
    (bK : IK ⟶ Spec (.of K)) (bCK : CK ⟶ Spec (.of K))
    (qI : IK ⟶ I) (qC : CK ⟶ C.left)
    (hI : IsPullback qI bK b (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hC : IsPullback qC bCK C.hom (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (e : Over.mk bK ≅ Over.mk bCK) : curveFibreResult S b bK qI := by
  let κ := Spec.map (CommRingCat.ofHom (algebraMap S K))
  let EI := curveCoefficientIso κ (M := Over.mk b) bK qI hI
  let EC := curveCoefficientIso κ bCK qC hC
  let EGeneric : genericScalarModel S b ≅
      genericScalarModel S (projectiveToSpec S (ULift.{u} (Fin 2))) :=
    EI.symm ≪≫ e ≪≫ EC ≪≫ scalar_iso κ E.symm
  let start : CoefficientStage S := ⟨S, hS, le_rfl⟩
  apply curveData_elim (@exists_retained_isos K _ S PUnit.{u + 1} _ hS
    (fun _ : PUnit.{u + 1} => I)
    (fun _ => projectiveScheme S (ULift.{u} (Fin 2)))
    (fun _ => inferInstanceAs (CompactSpace I))
    (fun _ => inferInstanceAs (QuasiSeparatedSpace I))
    (fun _ => QuasiCompact.compactSpace_of_compactSpace
      (projectiveToSpec S (ULift.{u} (Fin 2))))
    (fun _ => quasiSeparatedSpace_of_quasiSeparated
      (projectiveToSpec S (ULift.{u} (Fin 2))))
    (fun _ => b) (fun _ => projectiveToSpec S (ULift.{u} (Fin 2)))
    (fun _ => inferInstanceAs (LocallyOfFinitePresentation b))
    (fun _ => inferInstanceAs
      (LocallyOfFinitePresentation (projectiveToSpec S (ULift.{u} (Fin 2)))))
    (fun _ => EGeneric) start)
  intro k hk
  obtain ⟨_, E₀, _, _⟩ := hk
  let : GeometricallyConnected
      (stageScalarModel S (projectiveToSpec S (ULift.{u} (Fin 2))) k).hom :=
    projectiveStage_geomConnected S k
  let : GeometricallyConnected (stageScalarModel S b k).hom := over_iso_gc (E₀ PUnit.unit)
  let qK : IK ⟶ (stageScalarModel S b k).left := EI.hom.left ≫ genericLeg S b k
  have hK : IsPullback qK bK (stageScalarModel S b k).hom
      (Spec.map (CommRingCat.ofHom (algebraMap k.val K))) :=
    overIso_modelStage_cartesian S b k (Over.mk bK) EI
  have hqK : qK ≫ pullback.snd
      (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom)) b = qI :=
    curveModel_composite_triangle EI.hom.left (genericLeg S b k) _ _ qI
      (genericLeg_projection S b k) hI.flip.isoPullback_hom_snd
  exact ⟨k, qK, hK, hqK, inferInstance, fun L _ ρ => field_connected _ L ρ⟩

/-- The simple-curve alternatives give connected field fibres of the specified
closed intersection at a coefficient stage, preserving its original comparison. -/
theorem exists_simpleCurve_intersection_gc
    {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (S : Subalgebra ℤ K) (hS : S.FG) (G : ReductiveGroupData K)
    (w v : G.weylGroup) (i : G.rootBase.support)
    (hw : G.rootBase.IsPos (G.rootSystem.weylGroupToPerm w i.val))
    (hwv : WeylBruhatLE G.rootBase w v)
    {C F Y : Over (Spec (.of S))} [LocallyOfFinitePresentation F.hom]
    (E : Over.mk (projectiveToSpec S (ULift.{u} (Fin 2))) ≅ C)
    (d : C ⟶ F) (j : Y ⟶ F) [IsClosedImmersion j.left]
    (qC : (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).scheme ⟶ C.left)
    (qY : (schubertVariety G v).scheme ⟶ Y.left)
    (qF : (flagVariety G).scheme ⟶ F.left)
    (hC : IsPullback qC
      (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toSpec
      C.hom (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hY : IsPullback qY (schubertVariety G v).toSpec Y.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hF : IsPullback qF (flagVariety G).toSpec F.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hd : (simpleSchubertCurve G w i).left ≫ qF = qC ≫ d.left)
    (hj : (schubertInclusion G v).left ≫ qF = qY ≫ j.left)
    (hcoeff : qC = simpleCurveCoefficientMap S G i ≫ E.hom.left) :
    let b := pullback.fst d.left j.left ≫ C.hom
    let bK := pullback.fst (simpleSchubertCurve G w i).left
      (schubertInclusion G v).left ≫
        (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toSpec
    let qI := pullback.map (simpleSchubertCurve G w i).left (schubertInclusion G v).left
      d.left j.left qC qY qF hd hj
    curveFibreResult S b bK qI := by
  let : Algebra.FiniteType ℤ S := (Subalgebra.fg_iff_finiteType S).mp hS
  let : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing ℤ S
  have hprops := closed_intersection_properties E d j
  let : LocallyOfFinitePresentation (pullback.fst d.left j.left ≫ C.hom) := hprops.1
  let : CompactSpace (pullback d.left j.left : Scheme.{u}) := hprops.2.1
  let : QuasiSeparatedSpace (pullback d.left j.left : Scheme.{u}) := hprops.2.2
  have hI := paired_model_scalar_pullback
    (Spec.map (CommRingCat.ofHom (algebraMap S K)))
    (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toSpec
    (schubertVariety G v).toSpec (flagVariety G).toSpec
    C.hom Y.hom F.hom (simpleSchubertCurve G w i).left (schubertInclusion G v).left
    d.left j.left (simpleSchubertCurve G w i).w (schubertInclusion G v).w d.w j.w
    qC qY qF hC hY hF hd hj
  apply branch_result (simpleCurve_finite_cases G w v i hw hwv)
  · intro hwhole
    apply curveData_elim hwhole
    intro e _
    exact whole_curve_stage S hS (pullback.fst d.left j.left ≫ C.hom) E
      _ _ _ qC hI.1 hC e
  · intro hrestricted
    apply restricted_branch hrestricted
    intro c _ _ hc N hN hnil σ hσ
    exact trim_curve_data (exists_simpleCurve_restricted_gc S hS G w v i E d j
      qC qY qF hC hY hF hd hj hcoeff c hc N hN hnil σ hσ)

end SchubertGeometry
