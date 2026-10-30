import OrbitComplexity.SchubertGeometry.Connectedness.TargetStageTransport
import OrbitComplexity.SchubertGeometry.Connectedness.PrefixSquareComparisons
import OrbitComplexity.SchubertGeometry.Connectedness.PrefixScalarCoordinates
import OrbitComplexity.SchubertGeometry.Connectedness.PrefixTargetGluing
import OrbitComplexity.FrobeniusSplitting.Compatible.CoverKernels
import OrbitComplexity.FrobeniusSplitting.Normality.FiniteCover
import OrbitComplexity.SchubertGeometry.Normality.Components.OppositeScalarCoordinates
import OrbitComplexity.SchubertGeometry.Normality.Components.OppositePrimeFamilies
import OrbitComplexity.SchubertGeometry.Frobenius.Determinant.OppositionFibreSections
import OrbitComplexity.SchubertGeometry.Normality.FlagPushforwardStage
import OrbitComplexity.SchubertGeometry.Normality.CommonSchubertStage
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Compatible flag splittings from a longest-word model

The compatible word splitting descends along the longest-word endpoint.
Its pushforward preserves every Schubert and opposite Schubert image ideal on one coefficient stage.
-/

set_option autoImplicit false
set_option maxHeartbeats 100000

noncomputable section
universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits FrobeniusSplitting Opposite
open scoped TensorProduct
open ReductiveGroups FrobeniusSplitting.RetainedCharacter

open private spec_triangle from
  OrbitComplexity.SchubertGeometry.Connectedness.AppendSchubertConnected
open private weyl_le_longest from OrbitComplexity.SchubertGeometry.Cells.Longest
open private singletonIndex from
  OrbitComplexity.FrobeniusSplitting.Modules.MatchingModule
open private pullSection from
  OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.PullbackFrames
open private boundary_scalar_cartesian from
  OrbitComplexity.SchubertGeometry.Normality.WordEndpointStage
open private prime_fibre_compatible scalar_schubert_boundaries from
  OrbitComplexity.SchubertGeometry.Normality.WordEndpointStage

namespace SchubertGeometry

open private cartesian_target_iso projection_after_iso triangle_after_iso from
  OrbitComplexity.SchubertGeometry.Connectedness.TargetStageTransport
open private fibre_cartesian from
  OrbitComplexity.SchubertGeometry.Normality.CommonSchubertStage
open private scalar_functor from
  OrbitComplexity.SchubertGeometry.Connectedness.AppendCellConnected
open private comparison_natural from
  OrbitComplexity.SchubertGeometry.Connectedness.PrefixSquareComparisons
open private scalar_tower_eq scalar_flag from
  OrbitComplexity.SchubertGeometry.Connectedness.PrefixScalarCoordinates
open private over_source_cartesian from
  OrbitComplexity.SchubertGeometry.Normality.WordFaceImageStages
open private tensor_functor from
  OrbitComplexity.SchubertGeometry.Connectedness.PrefixScalarCoordinates
open private index_identity variety_diagonal quotient_component coordinate_inclusion from
  OrbitComplexity.SchubertGeometry.Connectedness.PrefixCoordinateTargets

/-- The ambient coordinate diagram retains its open directed atlas after
the coefficient extension of its closed family. -/
private theorem opposite_ambient_atlas
    {K T : Type u} [kField : Field K] [kClosed : IsAlgClosed K] [kZero : CharZero K]
    (G : ReductiveGroupData K) (U : T → (flagVariety G).scheme.Opens)
    (hU : ∀ t, IsAffineOpen (U t))
    (S₀ : Subalgebra ℤ K) (P : Over (Spec (.of S₀)))
    (qP : (flagVariety G).scheme ⟶ P.left) (start : CoefficientStage S₀)
    (selected : @ClosedCoordinateStage.{u} K T G.weylGroup kField kClosed kZero
      G (oppositeSchubertSupport G) U hU S₀ P qP start) :
    let _ : Algebra selected.S selected.k.val :=
      (Subalgebra.inclusion selected.k.property.2).toAlgebra
    let F₀ := intersectionIndexMap (id : T → T) ⋙
      (Sum.inr_ (Σ _ : G.weylGroup, {s : Finset T // s.Nonempty})
        {s : Finset T // s.Nonempty} ⋙
          (selected.N ⋙ tensor_functor selected.S selected.k.val))
    (∀ {i j} (a : i ⟶ j),
      IsOpenImmersion (((F₀.op ⋙ algSpec (.of selected.k.val)).map a).left)) ∧
      (((F₀.op ⋙ algSpec (.of selected.k.val) ⋙ Over.forget _) ⋙
        Scheme.forget).IsLocallyDirected) := by
  let : Algebra selected.S selected.k.val :=
    (Subalgebra.inclusion selected.k.property.2).toAlgebra
  let CI := {s : Finset T // s.Nonempty}
  let H₀ := intersectionIndexMap (id : T → T)
  refine ⟨@ambient_tensor_open.{u} selected.S selected.k.val
    (inferInstanceAs (CommRing selected.S)) (inferInstanceAs (CommRing selected.k.val))
    (inferInstanceAs (Algebra selected.S selected.k.val)) CI G.weylGroup inferInstance
    H₀ selected.N selected.hopen, ?_⟩
  exact @ambient_tensor_directed.{u} selected.S selected.k.val K
    (inferInstanceAs (CommRing selected.S)) (inferInstanceAs (CommRing selected.k.val))
    kField.toCommRing (inferInstanceAs (Algebra selected.S selected.k.val))
    CI G.weylGroup inferInstance H₀ (index_identity T) selected.N
    (intersectionCoordinates (flagVariety G).toSpec (intersectionOpens U))
    (fun i j k l a b p q h =>
      selected.hpush (.inr i) (.inr j) (.inr k) (.inr l)
        ((Sum.inr_ (Σ _ : G.weylGroup, CI) CI).map a)
        ((Sum.inr_ (Σ _ : G.weylGroup, CI) CI).map b)
        ((Sum.inr_ (Σ _ : G.weylGroup, CI) CI).map p)
        ((Sum.inr_ (Σ _ : G.weylGroup, CI) CI).map q) h)
    (fun i j k a b => by
      obtain ⟨v, p, q, hv⟩ := @intersectionCoordinates_refine.{u}
        (flagVariety G).scheme T K kField.toCommRing
        (@variety_diagonal.{u} K kField (flagVariety G))
        (flagVariety G).toSpec U hU (op i) (op j) (op k) a.op b.op
      exact ⟨v.unop, p.unop, q.unop, hv⟩)

/-- Scalar-tower isomorphisms preserving the original projections commute
with the prescribed morphism, independently of their chosen presentation. -/
private theorem scalar_tower_arrow
    {B T U : Scheme.{u}} (κ : T ⟶ B) (ρ : U ⟶ T) (ζ : U ⟶ B)
    (X Y : Over B) (f : X ⟶ Y)
    (EX : (scalar_functor ρ).obj ((scalar_functor κ).obj X) ≅ (scalar_functor ζ).obj X)
    (EY : (scalar_functor ρ).obj ((scalar_functor κ).obj Y) ≅ (scalar_functor ζ).obj Y)
    (hX : EX.hom.left ≫ pullback.snd ζ X.hom =
      pullback.snd ρ ((scalar_functor κ).obj X).hom ≫ pullback.snd κ X.hom)
    (hY : EY.hom.left ≫ pullback.snd ζ Y.hom =
      pullback.snd ρ ((scalar_functor κ).obj Y).hom ≫ pullback.snd κ Y.hom) :
    EX.hom.left ≫ ((scalar_functor ζ).map f).left =
      ((scalar_functor ρ).map ((scalar_functor κ).map f)).left ≫ EY.hom.left := by
  have h : (EX.hom.left ≫ pullback.snd ζ X.hom) ≫ f.left =
      ((scalar_functor ρ).map ((scalar_functor κ).map f)).left ≫
        (EY.hom.left ≫ pullback.snd ζ Y.hom) := by
    rw [hX, hY]
    change (pullback.snd ρ (pullback.fst κ X.hom) ≫ pullback.snd κ X.hom) ≫ f.left =
      (chosenScalarArrow ρ (chosenScalarArrow κ f)).left ≫
        (pullback.snd ρ (pullback.fst κ Y.hom) ≫ pullback.snd κ Y.hom)
    calc
      _ = pullback.snd ρ (pullback.fst κ X.hom) ≫
          (pullback.snd κ X.hom ≫ f.left) := Category.assoc _ _ _
      _ = pullback.snd ρ (pullback.fst κ X.hom) ≫
          ((chosenScalarArrow κ f).left ≫ pullback.snd κ Y.hom) :=
        congrArg (fun a => pullback.snd ρ (pullback.fst κ X.hom) ≫ a)
          (chosenScalarArrow_snd κ f).symm
      _ = (pullback.snd ρ (pullback.fst κ X.hom) ≫ (chosenScalarArrow κ f).left) ≫
          pullback.snd κ Y.hom := (Category.assoc _ _ _).symm
      _ = ((chosenScalarArrow ρ (chosenScalarArrow κ f)).left ≫
          pullback.snd ρ (pullback.fst κ Y.hom)) ≫ pullback.snd κ Y.hom :=
        congrArg (fun a => a ≫ pullback.snd κ Y.hom)
          (chosenScalarArrow_snd ρ (chosenScalarArrow κ f)).symm
      _ = _ := Category.assoc _ _ _
  exact (comparison_natural ζ EX EY f
    ((scalar_functor ρ).map ((scalar_functor κ).map f)) h).symm

open private pullback_base_eq from
  OrbitComplexity.SchubertGeometry.Frobenius.Determinant.OppositionStages

open private coefficient_targets from
  OrbitComplexity.SchubertGeometry.Connectedness.PrefixStageCoordinates
open private bsdhEndpointOver from
  OrbitComplexity.SchubertGeometry.BSDH.Actions
open private scalar_comparison from
  OrbitComplexity.SchubertGeometry.Connectedness.EmptyEndpointStage
open private finite_stage_bound from
  OrbitComplexity.FrobeniusSplitting.Normality.Connectedness.RetainedIsomorphisms
open private target_result stage_properties from
  OrbitComplexity.SchubertGeometry.Connectedness.PrefixTargetGluing
/-- A map from a proper model to a separated model over the same base is proper. -/
private theorem endpoint_proper {B : Scheme.{u}} (C F : Over B)
    [hC : IsProper C.hom] [hF : IsSeparated F.hom] (endpoint : C ⟶ F) :
    IsProper endpoint.left := by
  have hcomp : IsProper (endpoint.left ≫ F.hom) := by
    rw [endpoint.w]
    exact hC
  exact @IsProper.of_comp C.left F.left B endpoint.left F.hom hcomp hF

/-- Postcomposing the target of a Cartesian square with an isomorphism preserves it. -/
private theorem pullback_postcompose_iso
    {P X Y Z Z' : Scheme.{u}} (a : P ⟶ X) (b : P ⟶ Y)
    (f : X ⟶ Z) (g : Y ⟶ Z) (h : IsPullback a b f g) (E : Z ≅ Z') :
    IsPullback a b (f ≫ E.hom) (g ≫ E.hom) := by
  exact h.of_iso' (Iso.refl _) (Iso.refl _) (Iso.refl _) E.symm
    (by simp) (by simp) (by simp [Category.assoc]) (by simp [Category.assoc])

/-- A covering family remains jointly surjective after composition with an isomorphism. -/
private theorem cover_postcompose_iso
    {X Y : Scheme.{u}} {I : Type u} (V : I → Scheme.{u}) (k : ∀ i, V i ⟶ X)
    (hcover : ∀ x : X, ∃ i z, k i z = x) (E : X ≅ Y) :
    ∀ y : Y, ∃ i z, (k i ≫ E.hom) z = y := by
  intro y
  obtain ⟨i, z, hz⟩ := hcover (E.inv y)
  refine ⟨i, z, ?_⟩
  change E.hom (k i z) = y
  exact (congrArg E.hom hz).trans
    (congrArg (fun f : Y ⟶ Y => f y) E.inv_hom_id)

/-- A field receiving a coefficient ring in which two is a unit has odd prime characteristic. -/
private theorem odd_of_two_unit
    {A κ : Type u} [CommSemiring A] [Field κ] (f : A →+* κ)
    (hTwo : IsUnit (2 : A)) (p : ℕ) [hPrime : Fact p.Prime] [CharP κ p] :
    Odd p := by
  apply hPrime.out.odd_of_ne_two
  intro hp2
  have hne : (2 : κ) ≠ 0 := by
    simpa only [map_ofNat] using (hTwo.map f).ne_zero
  apply hne
  subst p
  exact CharP.cast_eq_zero κ 2

/-- The inverse image of a closed model in a specified ambient field fibre. -/
private def closedFibre {B T : Scheme.{u}}
    (D F : Over B) (j : D ⟶ F) (Z : Over T) (q : Z.left ⟶ F.left) : Over T :=
  Over.mk (pullback.fst q j.left ≫ Z.hom)

/-- The inclusion of the closed fibre into its specified ambient field fibre. -/
private def closedFibreInclusion {B T : Scheme.{u}}
    (D F : Over B) (j : D ⟶ F) (Z : Over T) (q : Z.left ⟶ F.left) :
    closedFibre D F j Z q ⟶ Z :=
  Over.homMk (pullback.fst q j.left) rfl

/-- The closed fibre retains the Cartesian comparison with its coefficient model. -/
private theorem closed_fibre_cartesian {B T : Scheme.{u}} (κ : T ⟶ B)
    (D F : Over B) (j : D ⟶ F) (Z : Over T) (q : Z.left ⟶ F.left)
    (hZ : IsPullback q Z.hom F.hom κ) :
    IsPullback (pullback.snd q j.left) (closedFibre D F j Z q).hom D.hom κ := by
  exact @fibre_cartesian.{u+1,u} Scheme.{u} inferInstance
    Z.left F.left D.left B T j.left D.hom F.hom j.w q Z.hom κ inferInstance hZ

/-- The inverse image of a scalar-extended inclusion has the same kernel as
its inverse image along the projection to the original model. -/
private theorem ordinary_kernel_scalar
    {B T Z : Scheme.{u}} (κ : T ⟶ B) (D F : Over B) (j : D ⟶ F)
    (qZ : Z ⟶ ((scalar_functor κ).obj F).left) :
    (pullback.fst qZ (chosenScalarArrow κ j).left).ker =
      (pullback.fst (qZ ≫ pullback.snd κ F.hom) j.left).ker := by
  let h := (IsPullback.of_hasPullback qZ (chosenScalarArrow κ j).left).paste_vert
    (chosenScalarArrow_cartesian κ j)
  have hi := h.isoPullback_hom_fst
  calc
    _ = (h.isoPullback.hom ≫
        pullback.fst (qZ ≫ pullback.snd κ F.hom) j.left).ker :=
      congrArg Scheme.Hom.ker hi.symm
    _ = _ := Scheme.Hom.ker_comp_of_isIso _ _

/-- Cartesian coefficient comparisons identify the specified closed field fibre,
including its morphism to the ambient field fibre. -/
private theorem closed_fibre_iso {B T : Scheme.{u}} (κ : T ⟶ B)
    (D F : Over B) (j : D ⟶ F) (Z Y : Over T)
    (qZ : Z.left ⟶ F.left) (qY : Y.left ⟶ D.left)
    (hZ : IsPullback qZ Z.hom F.hom κ)
    (hY : IsPullback qY Y.hom D.hom κ)
    (i : Y ⟶ Z) (hi : qY ≫ j.left = i.left ≫ qZ) :
    ∃ E : Y ≅ closedFibre D F j Z qZ,
      E.hom.left ≫ (closedFibreInclusion D F j Z qZ).left = i.left := by
  have hOuter : IsPullback (i.left ≫ Z.hom) qY κ (j.left ≫ F.hom) := by
    simpa only [i.w, j.w] using hY.flip
  have hcart : IsPullback i.left qY qZ j.left := hOuter.of_right hi.symm hZ.flip
  refine ⟨Over.isoMk hcart.isoPullback ?_, hcart.isoPullback_hom_fst⟩
  change hcart.isoPullback.hom ≫ (pullback.fst qZ j.left ≫ Z.hom) = Y.hom
  rw [← Category.assoc, hcart.isoPullback_hom_fst]
  exact i.w

/-- Scalar extension of a closed family identifies its inverse images in a
field fibre through one ambient isomorphism. -/
private theorem scalar_closed_fibre_iso
    {B T U : Scheme.{u}} (κ : T ⟶ B) (ρ : U ⟶ T) (ζ : U ⟶ B)
    (hζ : ρ ≫ κ = ζ) (X : Over B)
    (F : Over T) (E : (scalar_functor κ).obj X ≅ F)
    (Z : Over U) (qZ : Z.left ⟶ F.left)
    (hZ : IsPullback qZ Z.hom F.hom ρ) :
    ∃ eAmbient : (scalar_functor ζ).obj X ≅ Z,
      ∀ (Y : Over B) (j : Y ⟶ X), ∃ eClosed : (scalar_functor ζ).obj Y ≅
        closedFibre ((scalar_functor κ).obj Y) F
          ((scalar_functor κ).map j ≫ E.hom) Z qZ,
        eClosed.hom.left ≫
            (closedFibreInclusion ((scalar_functor κ).obj Y) F
              ((scalar_functor κ).map j ≫ E.hom) Z qZ).left =
          ((scalar_functor ζ).map j).left ≫ eAmbient.hom.left := by
  obtain ⟨EX, _hXbase, hX⟩ := scalar_tower_eq κ ρ ζ hζ X
  let EZ : Z ≅ (scalar_functor ρ).obj F := hZ.flip.isoOverPullback
  let eAmbient : (scalar_functor ζ).obj X ≅ Z :=
    EX.symm ≪≫ (scalar_functor ρ).mapIso E ≪≫ EZ.symm
  have hEZ : EZ.hom.left ≫ pullback.snd ρ F.hom = qZ :=
    hZ.flip.isoOverPullback_hom_left_comp_snd
  have hEZinv : EZ.inv.left ≫ qZ = pullback.snd ρ F.hom := by
    calc
      _ = EZ.inv.left ≫ (EZ.hom.left ≫ pullback.snd ρ F.hom) :=
        congrArg (fun a => EZ.inv.left ≫ a) hEZ.symm
      _ = (EZ.inv.left ≫ EZ.hom.left) ≫ pullback.snd ρ F.hom :=
        (Category.assoc _ _ _).symm
      _ = _ := by
        rw [← Over.comp_left, EZ.inv_hom_id]
        rfl
  have hAmbient : eAmbient.hom.left ≫ qZ =
      EX.inv.left ≫ (pullback.snd ρ ((scalar_functor κ).obj X).hom ≫ E.hom.left) := by
    change (EX.inv.left ≫ ((scalar_functor ρ).map E.hom).left ≫ EZ.inv.left) ≫ qZ = _
    calc
      _ = EX.inv.left ≫ ((((scalar_functor ρ).map E.hom).left ≫ EZ.inv.left) ≫ qZ) :=
        Category.assoc _ _ _
      _ = EX.inv.left ≫ (((scalar_functor ρ).map E.hom).left ≫ (EZ.inv.left ≫ qZ)) :=
        congrArg (fun a => EX.inv.left ≫ a) (Category.assoc _ _ _)
      _ = EX.inv.left ≫ (((scalar_functor ρ).map E.hom).left ≫ pullback.snd ρ F.hom) :=
        congrArg (fun a => EX.inv.left ≫ (((scalar_functor ρ).map E.hom).left ≫ a)) hEZinv
      _ = _ := congrArg (fun a => EX.inv.left ≫ a) (chosenScalarArrow_snd ρ E.hom)
  refine ⟨eAmbient, ?_⟩
  intro Y j
  obtain ⟨EY, _hYbase, hY⟩ := scalar_tower_eq κ ρ ζ hζ Y
  have hNat : EY.hom ≫ (scalar_functor ζ).map j =
      (scalar_functor ρ).map ((scalar_functor κ).map j) ≫ EX.hom := by
    apply Over.OverMorphism.ext
    exact scalar_tower_arrow κ ρ ζ Y X j EY EX hY hX
  have hNatInv : EY.inv ≫ (scalar_functor ρ).map ((scalar_functor κ).map j) =
      (scalar_functor ζ).map j ≫ EX.inv := by
    apply EY.inv_comp_eq.mpr
    rw [← Category.assoc, hNat, Category.assoc, EX.hom_inv_id, Category.comp_id]
  let qY := EY.inv.left ≫ pullback.snd ρ ((scalar_functor κ).obj Y).hom
  have hYcart : IsPullback qY ((scalar_functor ζ).obj Y).hom
      ((scalar_functor κ).obj Y).hom ρ :=
    over_source_cartesian EY.symm (pullback.snd ρ ((scalar_functor κ).obj Y).hom)
      ((scalar_functor κ).obj Y).hom ρ
      (IsPullback.of_hasPullback ρ ((scalar_functor κ).obj Y).hom).flip
  let jT := (scalar_functor κ).map j ≫ E.hom
  let iκ := (scalar_functor ζ).map j ≫ eAmbient.hom
  have hi : qY ≫ jT.left = iκ.left ≫ qZ := by
    change (EY.inv.left ≫ pullback.snd ρ ((scalar_functor κ).obj Y).hom) ≫
      (((scalar_functor κ).map j).left ≫ E.hom.left) =
      (((scalar_functor ζ).map j).left ≫ eAmbient.hom.left) ≫ qZ
    calc
      _ = EY.inv.left ≫ (pullback.snd ρ ((scalar_functor κ).obj Y).hom ≫
          (((scalar_functor κ).map j).left ≫ E.hom.left)) := Category.assoc _ _ _
      _ = EY.inv.left ≫ ((pullback.snd ρ ((scalar_functor κ).obj Y).hom ≫
          ((scalar_functor κ).map j).left) ≫ E.hom.left) :=
        congrArg (fun a => EY.inv.left ≫ a) (Category.assoc _ _ _).symm
      _ = (EY.inv.left ≫
          (pullback.snd ρ ((scalar_functor κ).obj Y).hom ≫
            ((scalar_functor κ).map j).left)) ≫ E.hom.left :=
        (Category.assoc _ _ _).symm
      _ = (EY.inv.left ≫
          (((scalar_functor ρ).map ((scalar_functor κ).map j)).left ≫
            pullback.snd ρ ((scalar_functor κ).obj X).hom)) ≫ E.hom.left :=
        congrArg (fun a => (EY.inv.left ≫ a) ≫ E.hom.left)
          (chosenScalarArrow_snd ρ ((scalar_functor κ).map j)).symm
      _ = ((EY.inv.left ≫
          ((scalar_functor ρ).map ((scalar_functor κ).map j)).left) ≫
            pullback.snd ρ ((scalar_functor κ).obj X).hom) ≫ E.hom.left :=
        congrArg (fun a => a ≫ E.hom.left) (Category.assoc _ _ _).symm
      _ = ((((scalar_functor ζ).map j).left ≫ EX.inv.left) ≫
            pullback.snd ρ ((scalar_functor κ).obj X).hom) ≫ E.hom.left :=
        congrArg (fun a => (a ≫ pullback.snd ρ ((scalar_functor κ).obj X).hom) ≫ E.hom.left)
          (congrArg Over.Hom.left hNatInv)
      _ = (((scalar_functor ζ).map j).left ≫ EX.inv.left) ≫
          (pullback.snd ρ ((scalar_functor κ).obj X).hom ≫ E.hom.left) :=
        Category.assoc _ _ _
      _ = ((scalar_functor ζ).map j).left ≫
          (EX.inv.left ≫ (pullback.snd ρ ((scalar_functor κ).obj X).hom ≫ E.hom.left)) :=
        Category.assoc _ _ _
      _ = ((scalar_functor ζ).map j).left ≫ (eAmbient.hom.left ≫ qZ) :=
        congrArg (fun a => ((scalar_functor ζ).map j).left ≫ a) hAmbient.symm
      _ = _ := (Category.assoc _ _ _).symm
  obtain ⟨eClosed, heClosed⟩ := closed_fibre_iso ρ ((scalar_functor κ).obj Y) F jT Z
    ((scalar_functor ζ).obj Y) qZ qY hZ hYcart iκ hi
  exact ⟨eClosed, heClosed⟩

/-- Arithmetic component relations on one quotient atlas propagate compatibility
from its rank-one inverse-image subschemes to every member of the family. -/
private theorem scalar_closed_family_compatible
    (R L : Type u) [CommRing R] [CommRing L] [Algebra R L]
    {C I : Type u} [Category.{u} C] [Quiver.IsThin C]
    (F₀ : C ⥤ CommAlgCat.{u} R) (B₀ : I → C ⥤ CommAlgCat.{u} R)
    [hopen : ∀ {i j : Cᵒᵖ} (a : i ⟶ j),
      IsOpenImmersion (((F₀.op ⋙ algSpec (.of R)).map a).left)]
    [hdir : (((F₀.op ⋙ algSpec (.of R)) ⋙ Over.forget _) ⋙ Scheme.forget).IsLocallyDirected]
    (β : ∀ i, F₀ ⟶ B₀ i)
    (cFM : Cocone (F₀.op ⋙ algSpec (.of R))) (hcFM : IsColimit cFM)
    (cBM : ∀ i, Cocone ((B₀ i).op ⋙ algSpec (.of R)))
    (jM : ∀ i, (cBM i).pt ⟶ cFM.pt) [∀ i, IsClosedImmersion (jM i).left]
    (hcart : ∀ i c, IsPullback
      (Spec.map (CommRingCat.ofHom ((β i).app c).hom.toRingHom))
      ((cBM i).ι.app (op c)).left (cFM.ι.app (op c)).left (jM i).left)
    {T : Scheme.{u}} (κ : T ⟶ Spec (.of R)) (ρ : Spec (.of L) ⟶ T)
    (hζ : ρ ≫ κ = Spec.map (CommRingCat.ofHom (algebraMap R L)))
    (F : Over T) (E : (scalar_functor κ).obj cFM.pt ≅ F)
    (Z : Over (Spec (.of L))) (qZ : Z.left ⟶ F.left)
    (hZ : IsPullback qZ Z.hom F.hom ρ)
    {p : ℕ} (splitting : SchemeSplitting Z.left p) (hp : 1 < p) (rank : I → ℕ)
    (zero : I) (hRankZero : ∀ i, rank i = 0 → i = zero)
    (hzero : ∀ c,
      RingHom.ker (Algebra.TensorProduct.lTensor (S := L) L ((β zero).app c).hom).toRingHom = ⊤ ∨
      RingHom.ker (Algebra.TensorProduct.lTensor (S := L) L ((β zero).app c).hom).toRingHom ∈
        (⊥ : Ideal (L ⊗[R] F₀.obj c)).minimalPrimes)
    (hone : ∀ i, rank i = 1 → splitting.IsCompatible
      (closedFibreInclusion ((scalar_functor κ).obj (cBM i).pt) F
        (chosenScalarArrow κ (jM i) ≫ E.hom) Z qZ).left.ker)
    (hstep : ∀ i, 2 ≤ rank i → ∃ a b, rank a < rank i ∧ rank b < rank i ∧ ∀ c,
      RingHom.ker (Algebra.TensorProduct.lTensor (S := L) L ((β i).app c).hom).toRingHom = ⊤ ∨
      RingHom.ker (Algebra.TensorProduct.lTensor (S := L) L ((β i).app c).hom).toRingHom ∈
        (RingHom.ker (Algebra.TensorProduct.lTensor (S := L) L ((β a).app c).hom).toRingHom ⊔
          RingHom.ker (Algebra.TensorProduct.lTensor (S := L) L ((β b).app
            c).hom).toRingHom).minimalPrimes) :
    ∀ i, splitting.IsCompatible
      (closedFibreInclusion ((scalar_functor κ).obj (cBM i).pt) F
        (chosenScalarArrow κ (jM i) ≫ E.hom) Z qZ).left.ker := by
  classical
  obtain ⟨eAmbient, hClosed⟩ := scalar_closed_fibre_iso κ ρ
    (Spec.map (CommRingCat.ofHom (algebraMap R L))) hζ cFM.pt F E Z qZ hZ
  choose eClosed heClosed using fun i => hClosed (cBM i).pt (jM i)
  obtain ⟨hOpenL, hcoverL⟩ := @tensor_cocone_cover.{u} R L inferInstance inferInstance
    inferInstance C inferInstance inferInstance F₀ hopen hdir cFM hcFM
  have hcover : ∀ y : (tensorCocone R L F₀ cFM).pt.left, ∃ c z,
      ((tensorCocone R L F₀ cFM).ι.app (op c)).left z = y := by
    intro y
    obtain ⟨s, z, hz⟩ := hcoverL y
    exact ⟨s.unop, z, hz⟩
  have hcoverZ : ∀ y : Z.left, ∃ c z,
      (((tensorCocone R L F₀ cFM).ι.app (op c)).left ≫ eAmbient.hom.left) z = y :=
    cover_postcompose_iso (fun c => Spec (.of (L ⊗[R] F₀.obj c)))
      (fun c => ((tensorCocone R L F₀ cFM).ι.app (op c)).left)
      hcover ((Over.forget _).mapIso eAmbient)
  have hOpenZ : ∀ c, IsOpenImmersion
      (((tensorCocone R L F₀ cFM).ι.app (op c)).left ≫ eAmbient.hom.left) := by
    intro c
    exact @IsOpenImmersion.comp (Spec (.of (L ⊗[R] F₀.obj c)))
      (tensorCocone R L F₀ cFM).pt.left Z.left
      ((tensorCocone R L F₀ cFM).ι.app (op c)).left eAmbient.hom.left
      (hOpenL (op c))
      (inferInstanceAs (IsOpenImmersion ((Over.forget _).mapIso eAmbient).hom))
  have hClosedScalar : ∀ i, IsClosedImmersion (chosenScalarArrow κ (jM i)).left := by
    intro i
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (chosenScalarArrow_cartesian κ (jM i)).flip inferInstance
  have hClosedModels : ∀ i, IsClosedImmersion
      (chosenScalarArrow κ (jM i) ≫ E.hom).left := fun i =>
    @IsClosedImmersion.comp _ _ _ (chosenScalarArrow κ (jM i)).left E.hom.left
      (hClosedScalar i) (inferInstanceAs (IsClosedImmersion E.hom.left))
  have hCompactFibres : ∀ i, QuasiCompact
      (closedFibreInclusion ((scalar_functor κ).obj (cBM i).pt) F
        (chosenScalarArrow κ (jM i) ≫ E.hom) Z qZ).left := by
    intro i
    let : IsClosedImmersion (chosenScalarArrow κ (jM i) ≫ E.hom).left := hClosedModels i
    have : IsClosedImmersion
        (closedFibreInclusion ((scalar_functor κ).obj (cBM i).pt) F
          (chosenScalarArrow κ (jM i) ≫ E.hom) Z qZ).left :=
      inferInstanceAs (IsClosedImmersion (pullback.fst qZ
        (chosenScalarArrow κ (jM i) ≫ E.hom).left))
    infer_instance
  have hcartZ (i : I) (c : C) : IsPullback
      (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.lTensor (S := L) L ((β i).app c).hom).toRingHom))
      (((tensorCocone R L (B₀ i) (cBM i)).ι.app (op c)).left ≫ (eClosed i).hom.left)
      (((tensorCocone R L F₀ cFM).ι.app (op c)).left ≫ eAmbient.hom.left)
      (closedFibreInclusion ((scalar_functor κ).obj (cBM i).pt) F
        (chosenScalarArrow κ (jM i) ≫ E.hom) Z qZ).left := by
    have h0 := @scalar_quotient_chart.{u} R L inferInstance inferInstance inferInstance
      C inferInstance F₀ (B₀ i) (β i) cFM (cBM i) (jM i) c (hcart i c)
    have h1 := pullback_postcompose_iso _ _ _ _ h0 ((Over.forget _).mapIso eAmbient)
    exact (cartesian_target_iso _ _ _ _ _ ((Over.forget _).mapIso (eClosed i))
      (heClosed i) h1.flip).flip
  exact @SchemeSplitting.isCompatible_ker_induction.{u,u,u}
    Z.left p C I splitting hp
    (fun c => L ⊗[R] F₀.obj c) (fun _ => inferInstance)
    (fun c => ((tensorCocone R L F₀ cFM).ι.app (op c)).left ≫ eAmbient.hom.left)
    hOpenZ hcoverZ
    (fun i => (closedFibre ((scalar_functor κ).obj (cBM i).pt) F
      (chosenScalarArrow κ (jM i) ≫ E.hom) Z qZ).left)
    (fun i => (closedFibreInclusion ((scalar_functor κ).obj (cBM i).pt) F
      (chosenScalarArrow κ (jM i) ≫ E.hom) Z qZ).left)
    hCompactFibres
    (fun i c => L ⊗[R] (B₀ i).obj c) (fun _ _ => inferInstance)
    (fun i c => (Algebra.TensorProduct.lTensor (S := L) L ((β i).app c).hom).toRingHom)
    (fun i c => ((tensorCocone R L (B₀ i) (cBM i)).ι.app (op c)).left ≫
      (eClosed i).hom.left) hcartZ rank
    (fun i hi => by obtain rfl := hRankZero i hi; exact hzero)
    hone (fun i hi => hstep i (by omega))

private theorem coefficient_spec_eq
    {K κ : Type u} [kComm : CommRing K] [κComm : CommRing κ]
    (L : Subalgebra ℤ K) (s t : CoefficientStage L) (hst : s ≤ t)
    [tκAlg : Algebra t.val κ] :
    let smallκAlg : Algebra s.val κ :=
      ((algebraMap t.val κ).comp (Subalgebra.inclusion hst).toRingHom).toAlgebra
    Spec.map (CommRingCat.ofHom
      ((@algebraMap s.val κ _ _ smallκAlg).comp
        (Subalgebra.inclusion s.property.2).toRingHom)) =
      Spec.map (CommRingCat.ofHom
        ((algebraMap t.val κ).comp (Subalgebra.inclusion t.property.2).toRingHom)) := by
  rfl

/-- A common coefficient bound specializes the opposite simple-divisor
compatibilities without changing the section-inserted splitting. -/
private theorem simple_field_compatible
    {K : Type u} [kField : Field K] [kClosed : IsAlgClosed K] [kZero : CharZero K]
    {G : ReductiveGroupData K} {word : List G.rootBase.support}
    (M : RetainedCharacter.PrefixModel G word) (S : Subalgebra ℤ K)
    (C F : Over (Spec (.of S))) (O : G.weylGroup → Over (Spec (.of S)))
    (j : ∀ w, O w ⟶ F) (endpoint : C ⟶ F) (x : C.left ⟶ M.cG.pt.left)
    (simpleBound : G.rootBase.support → CoefficientStage S) (bound : CoefficientStage S)
    (hSimpleBound : ∀ i, simpleBound i ≤ bound)
    (hSimple : ∀ i : G.rootBase.support,    ∀ (κ : Type u) [_κField : Field κ] [_tκAlg : Algebra
      (simpleBound i).val κ]
      (W Z Eκ : Over (Spec (.of κ))) [_zQS : QuasiSeparatedSpace Z.left]
      (qW : W.left ⟶ C.left) (qZ : Z.left ⟶ F.left) (bE : Eκ.left ⟶ (O (RootPairing.weylGroup.ofIdx
        G.rootSystem (DeterminantSection.oppositionSimple G i))).left)
      (_hW : IsPullback qW W.hom C.hom
        (Spec.map (CommRingCat.ofHom ((algebraMap (simpleBound i).val κ).comp
          (Subalgebra.inclusion (simpleBound i).property.2).toRingHom))))
      (_hZ : IsPullback qZ Z.hom F.hom
        (Spec.map (CommRingCat.ofHom ((algebraMap (simpleBound i).val κ).comp
          (Subalgebra.inclusion (simpleBound i).property.2).toRingHom))))
      (_hEκ : IsPullback bE Eκ.hom (O (RootPairing.weylGroup.ofIdx G.rootSystem
        (DeterminantSection.oppositionSimple G i))).hom
        (Spec.map (CommRingCat.ofHom ((algebraMap (simpleBound i).val κ).comp
          (Subalgebra.inclusion (simpleBound i).property.2).toRingHom))))
      (e : W ⟶ Z) [_eIso : IsIso e.left.c]
      (_he : e.left ≫ qZ = qW ≫ endpoint.left)
      (jκ : Eκ ⟶ Z) (_hjκ : jκ.left ≫ qZ = bE ≫ (j (RootPairing.weylGroup.ofIdx G.rootSystem
        (DeterminantSection.oppositionSimple G i))).left)
      (xκ : W.left ⟶ M.cG.pt.left) (_hxκ : qW ≫ x = xκ)
      (p : ℕ) [_pPrime : Fact p.Prime] [_κChar : CharP κ p] (_hp : Odd p),
      let L := (Scheme.Modules.pullback xκ).obj
        (@matchingModule.{u} M.S M.J
          (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
            (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) M.S)
          M.N M.cG M.delta ((p - 1) / 2))
      let m := @pullSection.{u} W.left M.cG.pt.left xκ
        (@matchingModule.{u} M.S M.J
          (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
            (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) M.S)
          M.N M.cG M.delta ((p - 1) / 2))
        (@coefficientMatchingSection.{u} M.S M.J
          (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
            (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) M.S)
          M.N M.cG M.delta (fun j => (M.P (singletonIndex j)).coeff 2) M.hr ((p - 1) / 2))
      ∀ (cκAlg : Algebra (ULift.{u} (ZMod p)) κ)
        (data : @RetainedCharacter.SectionSplitting.{u} (ULift.{u} (ZMod p))
          (@Field.toCommRing (ULift.{u} (ZMod p))
            (inferInstanceAs (Field (ULift.{u} (ZMod p))))) p
          (inferInstanceAs (ExpChar (ULift.{u} (ZMod p)) p)) W.left
          (W.hom ≫ Spec.map (CommRingCat.ofHom
            (@algebraMap (ULift.{u} (ZMod p)) κ _ _ cκAlg))) L
          (m.app ⊤ (1 : Γ(W.left, ⊤)))),
        (data.sigma.pushforward e.left).IsCompatible jκ.left.ker)
    (κ : Type u) [κField : Field κ] [boundκAlg : Algebra bound.val κ]
    (W Z : Over (Spec (.of κ))) [zQS : QuasiSeparatedSpace Z.left]
    (qW : W.left ⟶ C.left) (qZ : Z.left ⟶ F.left)
    (hW : IsPullback qW W.hom C.hom
      (Spec.map (CommRingCat.ofHom ((algebraMap bound.val κ).comp
        (Subalgebra.inclusion bound.property.2).toRingHom))))
    (hZ : IsPullback qZ Z.hom F.hom
      (Spec.map (CommRingCat.ofHom ((algebraMap bound.val κ).comp
        (Subalgebra.inclusion bound.property.2).toRingHom))))
    (e : W ⟶ Z) [eIso : IsIso e.left.c]
    (he : e.left ≫ qZ = qW ≫ endpoint.left)
    (p : ℕ) [pPrime : Fact p.Prime] [κChar : CharP κ p] (hp : Odd p) :
    let xκ := qW ≫ x
    let L := (Scheme.Modules.pullback xκ).obj
      (@matchingModule.{u} M.S M.J
        (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) M.S)
        M.N M.cG M.delta ((p - 1) / 2))
    let m := @pullSection.{u} W.left M.cG.pt.left xκ
      (@matchingModule.{u} M.S M.J
        (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) M.S)
        M.N M.cG M.delta ((p - 1) / 2))
      (@coefficientMatchingSection.{u} M.S M.J
        (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) M.S)
        M.N M.cG M.delta (fun j => (M.P (singletonIndex j)).coeff 2) M.hr ((p - 1) / 2))
    ∀ (cκAlg : Algebra (ULift.{u} (ZMod p)) κ)
      (data : @RetainedCharacter.SectionSplitting.{u} (ULift.{u} (ZMod p))
        (@Field.toCommRing (ULift.{u} (ZMod p))
          (inferInstanceAs (Field (ULift.{u} (ZMod p))))) p
        (inferInstanceAs (ExpChar (ULift.{u} (ZMod p)) p)) W.left
        (W.hom ≫ Spec.map (CommRingCat.ofHom
          (@algebraMap (ULift.{u} (ZMod p)) κ _ _ cκAlg))) L
        (m.app ⊤ (1 : Γ(W.left, ⊤)))),
      ∀ i : G.rootBase.support,
        (data.sigma.pushforward e.left).IsCompatible
          (closedFibreInclusion (O (RootPairing.weylGroup.ofIdx G.rootSystem i))
            F (j (RootPairing.weylGroup.ofIdx G.rootSystem i)) Z qZ).left.ker := by
  classical
  have hOppSurjective : Function.Surjective (DeterminantSection.oppositionSimple G) := by
    intro i
    exact ⟨DeterminantSection.oppositionSimple G i,
      DeterminantSection.oppositionSimple_twice G i⟩
  intro xκ LX m cκAlg data
  refine (hOppSurjective.forall (p := fun i : G.rootBase.support =>
    (data.sigma.pushforward e.left).IsCompatible
      (closedFibreInclusion (O (RootPairing.weylGroup.ofIdx G.rootSystem i))
        F (j (RootPairing.weylGroup.ofIdx G.rootSystem i)) Z qZ).left.ker)).mpr ?_
  intro i
  let smallκAlg : Algebra (simpleBound i).val κ :=
    ((algebraMap bound.val κ).comp
      (Subalgebra.inclusion (hSimpleBound i)).toRingHom).toAlgebra
  have hCoeff := @coefficient_spec_eq.{u} K κ kField.toCommRing κField.toCommRing
    S (simpleBound i) bound (hSimpleBound i) boundκAlg
  have hWsmall := pullback_base_eq hW hCoeff.symm
  have hZsmall := pullback_base_eq hZ hCoeff.symm
  let label := RootPairing.weylGroup.ofIdx G.rootSystem
    (DeterminantSection.oppositionSimple G i)
  let Eκ := @closedFibre.{u} (Spec (.of S)) (Spec (.of κ))
    (O label) F (j label) Z qZ
  let jκ := @closedFibreInclusion.{u} (Spec (.of S)) (Spec (.of κ))
    (O label) F (j label) Z qZ
  let bE := pullback.snd qZ (j label).left
  have hEκ := @closed_fibre_cartesian.{u} (Spec (.of S)) (Spec (.of κ))
    (Spec.map (CommRingCat.ofHom ((algebraMap bound.val κ).comp
      (Subalgebra.inclusion bound.property.2).toRingHom)))
    (O label) F (j label) Z qZ hZ
  have hEsmall := pullback_base_eq hEκ hCoeff.symm
  have hjκ : jκ.left ≫ qZ = bE ≫ (j label).left := by
    exact pullback.condition

  exact @hSimple i κ κField smallκAlg W Z Eκ zQS qW qZ bE
    hWsmall hZsmall hEsmall e eIso he jκ hjκ xκ rfl
    p pPrime κChar hp cκAlg data


/-- The scalar-extended endpoint equation retains its original projections. -/
private theorem endpoint_scalar_projection
    {B T W Z : Scheme.{u}} (κ : T ⟶ B) (C F : Over B) (endpoint : C ⟶ F)
    (qW : W ⟶ ((scalar_functor κ).obj C).left)
    (qZ : Z ⟶ ((scalar_functor κ).obj F).left) (e : W ⟶ Z)
    (he : e ≫ qZ = qW ≫ (chosenScalarArrow κ endpoint).left) :
    e ≫ (qZ ≫ pullback.snd κ F.hom) =
      (qW ≫ pullback.snd κ C.hom) ≫ endpoint.left := by
  calc
    _ = (e ≫ qZ) ≫ pullback.snd κ F.hom := (Category.assoc _ _ _).symm
    _ = (qW ≫ (chosenScalarArrow κ endpoint).left) ≫
        pullback.snd κ F.hom := congrArg (· ≫ pullback.snd κ F.hom) he
    _ = qW ≫ ((chosenScalarArrow κ endpoint).left ≫
        pullback.snd κ F.hom) := Category.assoc _ _ _
    _ = qW ≫ (pullback.snd κ C.hom ≫ endpoint.left) :=
      congrArg (qW ≫ ·) (chosenScalarArrow_snd κ endpoint)
    _ = _ := (Category.assoc _ _ _).symm

/-- Schubert image compatibility is preserved under coefficient extension
and scalar base change. -/
private theorem ordinary_field_compatible
    {K : Type u} [kField : Field K] [kClosed : IsAlgClosed K] [kZero : CharZero K]
    (G : ReductiveGroupData K) (word : List G.rootBase.support)
    (S : Subalgebra ℤ K) (C F : Over (Spec (.of S)))
    (D : G.weylGroup → Over (Spec (.of S))) (j : ∀ w, D w ⟶ F)
    (endpoint : C ⟶ F) (A : Scheme.{u}) (qOriginal : C.left ⟶ A)
    (d : Fin word.length → Over A)
    (r geometry : CoefficientStage S) (bound : CoefficientStage geometry.val)
    (hr : r.val ≤ bound.val)
    (hImages : @wordImageFibres.{u} K kField kClosed kZero G word S C F D j endpoint
      (fun v => Over.mk (pullback.fst qOriginal (d v).hom)) r) :
    let beta := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion geometry.property.2).toRingHom)
    let CL := (scalar_functor beta).obj C
    let PL := (scalar_functor beta).obj F
    ∀ (κ : Type u) [_κField : Field κ] [_boundκAlg : Algebra bound.val κ]
      (W Z : Over (Spec (.of κ))) [_wCompact : CompactSpace W.left]
      [_zQS : QuasiSeparatedSpace Z.left]
      (qW : W.left ⟶ CL.left) (qZ : Z.left ⟶ PL.left)
      (_hW : IsPullback qW W.hom CL.hom
        (Spec.map (CommRingCat.ofHom ((algebraMap bound.val κ).comp
          (Subalgebra.inclusion bound.property.2).toRingHom))))
      (_hZ : IsPullback qZ Z.hom PL.hom
        (Spec.map (CommRingCat.ofHom ((algebraMap bound.val κ).comp
          (Subalgebra.inclusion bound.property.2).toRingHom))))
      (e : W ⟶ Z) [_eQC : QuasiCompact e.left] [_eIso : IsIso e.left.c]
      (_he : e.left ≫ qZ = qW ≫ (chosenScalarArrow beta endpoint).left)
      (B : Fin word.length → Over W.left)
      (b : ∀ v, (B v).left ⟶ (d v).left)
      (_hB : ∀ v, IsPullback (B v).hom (b v)
        (qW ≫ (pullback.snd beta C.hom ≫ qOriginal)) (d v).hom)
      (p : ℕ) (sigma : SchemeSplitting W.left p)
      (_hCompatible : ∀ v, sigma.IsCompatible (B v).hom.ker),
      ∀ w, WeylBruhatLE G.rootBase w (simpleWeylWord G.rootBase word) →
        (sigma.pushforward e.left).IsCompatible
          (pullback.fst qZ (chosenScalarArrow beta (j w)).left).ker := by
  intro beta CL PL κ κField boundκAlg W Z wCompact zQS qW qZ hW hZ e eQC eIso he
    B b hB p sigma hCompatible
  let joined := @singleScalarStage.{u} K kField.toCommRing S geometry bound
  let rκAlg : Algebra r.val κ :=
    ((algebraMap joined.val κ).comp (Subalgebra.inclusion hr).toRingHom).toAlgebra
  have hSmall := @coefficient_spec_eq.{u} K κ kField.toCommRing κField.toCommRing
    S r joined hr boundκAlg
  let coefficient := Spec.map (CommRingCat.ofHom
    ((algebraMap joined.val κ).comp (Subalgebra.inclusion joined.property.2).toRingHom))
  have hTower : Spec.map (CommRingCat.ofHom ((algebraMap bound.val κ).comp
        (Subalgebra.inclusion bound.property.2).toRingHom)) ≫ beta = coefficient :=
    @spec_triangle.{u} S geometry.val κ (inferInstanceAs (CommRing S))
      (inferInstanceAs (CommRing geometry.val)) κField.toCommRing
      (Subalgebra.inclusion geometry.property.2).toRingHom
      ((algebraMap bound.val κ).comp (Subalgebra.inclusion bound.property.2).toRingHom)
      ((algebraMap joined.val κ).comp (Subalgebra.inclusion joined.property.2).toRingHom) rfl
  let qWold := qW ≫ pullback.snd beta C.hom
  let qZold := qZ ≫ pullback.snd beta F.hom
  have hWold0 := hW.paste_horiz (IsPullback.of_hasPullback beta C.hom).flip
  have hZold0 := hZ.paste_horiz (IsPullback.of_hasPullback beta F.hom).flip
  have hWold := pullback_base_eq (pullback_base_eq hWold0 hTower) hSmall.symm
  have hZold := pullback_base_eq (pullback_base_eq hZold0 hTower) hSmall.symm
  have heOld : e.left ≫ qZold = qWold ≫ endpoint.left :=
    @endpoint_scalar_projection.{u} (Spec (.of S)) (Spec (.of geometry.val)) W.left Z.left
      beta C F endpoint qW qZ e.left he
  choose bOld hBOld using fun v : Fin word.length =>
    @boundary_scalar_cartesian.{u} (B v).left W.left C.left A (d v).left
      (B v).hom (b v) (qW ≫ (pullback.snd beta C.hom ≫ qOriginal)) (d v).hom
      (hB v) qOriginal qWold (Category.assoc _ _ _)
  have hOrdinary := @hImages κ κField rκAlg W Z wCompact zQS qWold qZold hWold hZold
    e eQC eIso heOld B bOld hBOld p sigma hCompatible
  intro w hw
  rw [ordinary_kernel_scalar beta (D w) F (j w) qZ]
  exact hOrdinary w hw

/-- Simple reflections suffice to establish a predicate at Coxeter length one. -/
private theorem length_one_of_simple
    {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K) (P : G.weylGroup → Prop)
    (hSimple : ∀ i : G.rootBase.support, P (RootPairing.weylGroup.ofIdx G.rootSystem i)) :
    ∀ w, (weylCoxeterSystem G.rootBase).length w = 1 → P w := by
  intro w hw
  obtain ⟨i, hi⟩ := (weylCoxeterSystem G.rootBase).length_eq_one_iff.mp hw
  have heq := hi.trans (weylCoxeterSystem_simple G.rootBase i)
  exact heq.symm ▸ hSimple i
/-- The coordinate cocone inclusion equals the opposite Schubert inclusion. -/
private theorem opposite_coordinate_inclusion
    {K T : Type u} [kField : Field K] [kClosed : IsAlgClosed K] [kZero : CharZero K]
    (G : ReductiveGroupData K) (w : G.weylGroup)
    (U : T → (flagVariety G).scheme.Opens) (hU : ∀ t, IsAffineOpen (U t)) :
    (@coordinate_inclusion.{u}
      (oppositeSchubertVariety G w).scheme (flagVariety G).scheme T K kField.toCommRing
      (@variety_diagonal.{u} K kField (oppositeSchubertVariety G w))
      (@variety_diagonal.{u} K kField (flagVariety G))
      ((flagVariety G).closedInclusion (oppositeSchubertSupport G w)).left
      (inferInstanceAs (IsClosedImmersion
        ((flagVariety G).closedInclusion (oppositeSchubertSupport G w)).left))
      (flagVariety G).toSpec U hU).left = (oppositeSchubertInclusion G w).left := by
  rfl
/-- Isomorphisms of the ambient objects transport a commuting triangle. -/
private theorem over_triangle_iso_trans {B : Scheme.{u}} {D X Y Z : Over B}
    {V W : Scheme.{u}} (j : D ⟶ X) (E : X ≅ Y) (F : Y ≅ Z)
    (qD : V ⟶ D.left) (qX : W ⟶ Y.left) (n n' : V ⟶ W)
    (hn : n = n') (h : qD ≫ (j ≫ E.hom).left = n ≫ qX) :
    qD ≫ (j ≫ (E ≪≫ F).hom).left = n' ≫ (qX ≫ F.hom.left) := by
  cases hn
  simpa only [Iso.trans_hom, Over.comp_left, Category.assoc] using
    congrArg (fun f => f ≫ F.hom.left) h
/-- Successive ambient isomorphisms preserve the composite projection. -/
private theorem ambient_projection
    {X Y Z D B P W : Scheme.{u}}
    (e₁ : X ⟶ Y) (e₀ : Y ⟶ Z) (e : X ⟶ Z)
    (p : Z ⟶ P) (a : Y ⟶ B) (b : B ⟶ P)
    (d : X ⟶ D) (c : D ⟶ B)
    (q : W ⟶ X) (qMid : W ⟶ D) (qBase : W ⟶ B) (qOriginal : W ⟶ P)
    (he : e = e₁ ≫ e₀)
    (h₀ : e₀ ≫ p = a ≫ b) (h₁ : e₁ ≫ a = d ≫ c)
    (hMid : q ≫ d = qMid) (hBase : qMid ≫ c = qBase)
    (hOriginal : qBase ≫ b = qOriginal) :
    (e ≫ p = (d ≫ c) ≫ b) ∧
    (q ≫ (d ≫ c) = qBase) ∧
    ((q ≫ e) ≫ p = qOriginal) := by
  have hAmbient : e ≫ p = (d ≫ c) ≫ b := by
    calc
      _ = (e₁ ≫ e₀) ≫ p := congrArg (· ≫ p) he
      _ = e₁ ≫ (e₀ ≫ p) := Category.assoc _ _ _
      _ = e₁ ≫ (a ≫ b) := congrArg (e₁ ≫ ·) h₀
      _ = (e₁ ≫ a) ≫ b := (Category.assoc _ _ _).symm
      _ = (d ≫ c) ≫ b := congrArg (· ≫ b) h₁
  have hMiddle : q ≫ (d ≫ c) = qBase :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ c) hMid).trans hBase)
  have hFlat : (q ≫ e) ≫ p = qOriginal := by
    calc
      _ = q ≫ (e ≫ p) := Category.assoc _ _ _
      _ = q ≫ ((d ≫ c) ≫ b) := congrArg (q ≫ ·) hAmbient
      _ = (q ≫ (d ≫ c)) ≫ b := (Category.assoc _ _ _).symm
      _ = qBase ≫ b := congrArg (· ≫ b) hMiddle
      _ = _ := hOriginal
  exact ⟨hAmbient, hMiddle, hFlat⟩

/-- A coefficient stage supporting opposite Schubert compatibilities. -/
private def oppositeStageResult
    {K : Type u} [kField : Field K] [kClosed : IsAlgClosed K] [kZero : CharZero K]
    {G : ReductiveGroupData K} {word : List G.rootBase.support}
    (M : RetainedCharacter.PrefixModel G word)
    (S₀ : Subalgebra ℤ K) (hMS : M.S ≤ S₀)
    (A : Arrow (Over (Spec (.of S₀))))
    (qOriginal : A.left.left ⟶ M.cG.pt.left)
    (qC : bsdhScheme G word ⟶ A.left.left)
    (qP : (flagVariety G).scheme ⟶ A.right.left)
    (start : CoefficientStage S₀) : Prop :=
    ∃ (t : CoefficientStage S₀), start ≤ t ∧
      let τ := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion t.property.2).toRingHom)
      let MT := stageScalarModel S₀ A.left.hom t
      let FT := stageScalarModel S₀ A.right.hom t
      let xT := pullback.snd τ A.left.hom ≫ qOriginal
      let endpointT := chosenScalarArrow τ A.hom
      ∃ (qMT : bsdhScheme G word ⟶ MT.left)
        (qFT : (flagVariety G).scheme ⟶ FT.left)
        (O : G.weylGroup → Over (Spec (.of t.val)))
        (jO : ∀ w, O w ⟶ FT)
        (qOT : ∀ w, (oppositeSchubertVariety G w).scheme ⟶ (O w).left),
        IsPullback xT MT.hom M.cG.pt.hom
          (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion (hMS.trans t.property.2)).toRingHom)) ∧
        IsPullback qMT (bsdhToSpec G word) MT.hom
          (Spec.map (CommRingCat.ofHom (algebraMap t.val K))) ∧
        IsPullback qFT (flagVariety G).toSpec FT.hom
          (Spec.map (CommRingCat.ofHom (algebraMap t.val K))) ∧
        qMT ≫ pullback.snd τ A.left.hom = qC ∧
        qFT ≫ pullback.snd τ A.right.hom = qP ∧
        (∀ w, IsPullback (qOT w) (oppositeSchubertVariety G w).toSpec (O w).hom
          (Spec.map (CommRingCat.ofHom (algebraMap t.val K)))) ∧
        (∀ w, IsClosedImmersion (jO w).left) ∧
        (∀ w, LocallyOfFinitePresentation (O w).hom ∧ CompactSpace (O w).left ∧
          QuasiSeparatedSpace (O w).left) ∧
        IsProper endpointT.left ∧
        qMT ≫ xT = M.m₀ ∧ bsdhMap G word ≫ qFT = qMT ≫ endpointT.left ∧
        (∀ w, (oppositeSchubertInclusion G w).left ≫ qFT = qOT w ≫ (jO w).left) ∧
        ∃ r : CoefficientStage t.val,
        ∀ (κ : Type u) [_κField : Field κ] [Algebra r.val κ]
          (W Z : Over (Spec (.of κ))) [QuasiSeparatedSpace Z.left]
          (qW : W.left ⟶ MT.left) (qZ : Z.left ⟶ FT.left)
          (_hW : IsPullback qW W.hom MT.hom
            (Spec.map (CommRingCat.ofHom ((algebraMap r.val κ).comp
              (Subalgebra.inclusion r.property.2).toRingHom))))
          (_hZ : IsPullback qZ Z.hom FT.hom
            (Spec.map (CommRingCat.ofHom ((algebraMap r.val κ).comp
              (Subalgebra.inclusion r.property.2).toRingHom))))
          (e : W ⟶ Z) [IsIso e.left.c] (_he : e.left ≫ qZ = qW ≫ endpointT.left)
          (p : ℕ) [Fact p.Prime] [CharP κ p] (_hp : Odd p),
          let xκ := qW ≫ xT
          let L := (Scheme.Modules.pullback xκ).obj
            (@matchingModule.{u} M.S M.J
              (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
                (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField)))
                  M.S)
              M.N M.cG M.delta ((p - 1) / 2))
          let m := @pullSection.{u} W.left M.cG.pt.left xκ
            (@matchingModule.{u} M.S M.J
              (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
                (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField)))
                  M.S)
              M.N M.cG M.delta ((p - 1) / 2))
            (@coefficientMatchingSection.{u} M.S M.J
              (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
                (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField)))
                  M.S)
              M.N M.cG M.delta (fun j => (M.P (singletonIndex j)).coeff 2) M.hr ((p - 1) / 2))
          ∀ (cκAlg : Algebra (ULift.{u} (ZMod p)) κ)
            (data : @RetainedCharacter.SectionSplitting.{u} (ULift.{u} (ZMod p))
              (@Field.toCommRing (ULift.{u} (ZMod p))
                (inferInstanceAs (Field (ULift.{u} (ZMod p))))) p
              (inferInstanceAs (ExpChar (ULift.{u} (ZMod p)) p)) W.left
              (W.hom ≫ Spec.map (CommRingCat.ofHom
                (@algebraMap (ULift.{u} (ZMod p)) κ _ _ cκAlg))) L
              (m.app ⊤ (1 : Γ(W.left, ⊤)))),
            ∀ w, (data.sigma.pushforward e.left).IsCompatible
              (pullback.fst qZ (jO w).left).ker

/-- Opposite Schubert models on one coefficient stage preserve every
section-induced splitting of its word fibres. -/
private theorem exists_opposite_stage
    {K : Type u} [kField : Field K] [kClosed : IsAlgClosed K] [kZero : CharZero K]
    (G : ReductiveGroupData K) (word : List G.rootBase.support)
    (M : RetainedCharacter.PrefixModel G word)
    (S₀ : Subalgebra ℤ K) (hS₀ : S₀.FG) (hMS : M.S ≤ S₀)
    (C P : Over (Spec (.of S₀)))
    [pCompact : CompactSpace P.left] [pFP : LocallyOfFinitePresentation P.hom]
    (qOriginal : C.left ⟶ M.cG.pt.left)
    (hOriginal : IsPullback qOriginal C.hom M.cG.pt.hom
      (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hMS).toRingHom)))
    (qC : bsdhScheme G word ⟶ C.left)
    (hC : IsPullback qC (bsdhToSpec G word) C.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S₀ K))))
    (hWord : qC ≫ qOriginal = M.m₀)
    (qP : (flagVariety G).scheme ⟶ P.left)
    (hP : IsPullback qP (flagVariety G).toSpec P.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S₀ K))))
    (endpoint : C ⟶ P) [endpointProper : IsProper endpoint.left]
    (hEndpoint : bsdhMap G word ≫ qP = qC ≫ endpoint.left)
    (start : CoefficientStage S₀) :
    @oppositeStageResult.{u} K kField kClosed kZero G word M S₀ hMS
      (Arrow.mk endpoint) qOriginal qC qP start := by
  classical
  let flagCompact : CompactSpace (flagVariety G).scheme :=
    QuasiCompact.compactSpace_of_compactSpace (flagVariety G).toSpec
  obtain ⟨T, tFinite, U, hU, hcover⟩ :=
    @exists_finite_affine_opens.{u} (flagVariety G).scheme flagCompact
  let : Finite T := tFinite
  have family := @exists_opposite_prime_families.{u} K T kField kClosed kZero tFinite
    G U hU hcover S₀ hS₀ P pCompact pFP qP hP start
  obtain ⟨selected, hArithmetic⟩ := family
  have hAtlas := @opposite_ambient_atlas.{u} K T kField kClosed kZero
    G U hU S₀ P qP start selected
  rcases selected with ⟨S, hS, hS₀S, hstartS, N, e, β, hfp, hn, hβ, hsurj, hopen, hpush,
    qPS, hPS, hPSfirst, hPSsecond, k, htargets, hsurjK, hcartK, _scalarProperties⟩
  let : Algebra S k.val := (Subalgebra.inclusion k.property.2).toAlgebra
  let : IsScalarTower S k.val K :=
    Subalgebra.inclusion.isScalarTower_right k.property.2 K
  let CI := {s : Finset T // s.Nonempty}
  let H₀ := intersectionIndexMap (id : T → T)
  let Nₖ := N ⋙ tensor_functor S k.val
  let βₖ := Functor.whiskerRight β (tensor_functor S k.val)
  let F₀ := H₀ ⋙ (Sum.inr_ (Σ _ : G.weylGroup, CI) CI ⋙ Nₖ)
  let B₀ := fun w => Sigma.incl (C := fun _ : G.weylGroup => CI) w ⋙
    (Sum.inl_ (Σ _ : G.weylGroup, CI) CI ⋙ Nₖ)
  let β₀ := @quotient_component.{u} CI inferInstance G.weylGroup k.val
    (inferInstanceAs (CommRing k.val)) H₀ Nₖ βₖ
  have hcartβ := @quotient_tensor_equifibered.{u} S k.val
    (inferInstanceAs (CommRing S)) (inferInstanceAs (CommRing k.val))
    (inferInstanceAs (Algebra S k.val)) CI inferInstance G.weylGroup H₀ N β hcartK
  change (∀ {i j : CIᵒᵖ} (a : i ⟶ j),
      IsOpenImmersion (((F₀.op ⋙ algSpec (.of k.val)).map a).left)) ∧
    (((F₀.op ⋙ algSpec (.of k.val) ⋙ Over.forget _) ⋙
      Scheme.forget).IsLocallyDirected) at hAtlas
  obtain ⟨hOpenF, hDirF⟩ := hAtlas
  change ∃ R : CoefficientStage k.val,
    @componentKernelStage.{u} K G.weylGroup CI kField.toCommRing inferInstance
      k.val H₀ Nₖ βₖ (weylCoxeterSystem G.rootBase).length 1 R at hArithmetic
  obtain ⟨R, hArithmeticFields⟩ := hArithmetic
  unfold componentKernelStage at hArithmeticFields
  dsimp only [coefficient_targets] at htargets
  obtain ⟨qPk, hPk, hnF, hnB, hPkfirst, hPksecond, hCoordinatesOriginal,
    hmodels, hTower⟩ := htargets
  dsimp only [target_result] at hmodels
  obtain ⟨cFM, cBM, qFM, qBM, jM, hcFM, hcBM, hjM, hqFM,
    hqBM, hlegsF, hlegsB, hlegsJ, htriangleM, ℓ, hstartℓ, Ek, hEk,
    hqPℓ, hProj, hTargets⟩ := hmodels
  have hCharts (w : G.weylGroup) (c : CI) : IsPullback
      (Spec.map (CommRingCat.ofHom ((β₀ w).app c).hom.toRingHom))
      ((cBM w).ι.app (op c)).left (cFM.ι.app (op c)).left (jM w).left :=
    @quotient_cocone_chart.{u} k.val (inferInstanceAs (CommRing k.val))
      CI inferInstance inferInstance inferInstance F₀ (B₀ w) hOpenF hDirF
      (β₀ w) (hcartβ w) cFM hcFM.some (cBM w) (hcBM w).some
      (jM w) (hlegsJ w) c
  let κℓ := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion ℓ.property.2).toRingHom)
  let O := fun w => stageScalarModel k.val (cBM w).pt.hom ℓ
  let jO := fun w => chosenScalarArrow κℓ (jM w) ≫ Ek.hom
  choose qO hOClosed hOCart hOTriangle hOProjection hOFP hOCompact hOQS using hTargets
  obtain ⟨joint, hℓJoint, hRJoint⟩ := exists_ge_ge ℓ R
  let r : CoefficientStage ℓ.val := ⟨joint.val, joint.property.1, hℓJoint⟩
  have hRr : R.val ≤ r.val := hRJoint
  let L := ℓ.val
  have hSL : S ≤ L := k.property.2.trans ℓ.property.2
  have hS₀L : S₀ ≤ L := hS₀S.trans hSL
  let : Algebra S L := (Subalgebra.inclusion hSL).toAlgebra
  let : Algebra k.val L := (Subalgebra.inclusion ℓ.property.2).toAlgebra
  let : Algebra S₀ L := (Subalgebra.inclusion hS₀L).toAlgebra
  let : IsScalarTower S k.val L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let κ₀S := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hS₀S).toRingHom)
  let κSk := Spec.map (CommRingCat.ofHom (algebraMap S k.val))
  let κSL := Spec.map (CommRingCat.ofHom (algebraMap S L))
  let κ₀L := Spec.map (CommRingCat.ofHom (algebraMap S₀ L))
  let ρL := Spec.map (CommRingCat.ofHom (algebraMap L K))
  let s : CoefficientStage S₀ := ⟨S, hS, hS₀S⟩
  let PS := stageScalarModel S₀ P.hom s
  let Pk := (scalar_functor κSk).obj PS
  let Pnest := (Arrow.mk Ek.hom).right
  let PL := (scalar_functor κ₀L).obj P
  obtain ⟨E₁, hE₁f, hE₁s⟩ := @hTower L (inferInstanceAs (CommRing L))
    (inferInstanceAs (Algebra S L)) (inferInstanceAs (Algebra k.val L))
    (inferInstanceAs (IsScalarTower S k.val L))
  have hCoeffTower : κSL ≫ κ₀S = κ₀L :=
    spec_triangle (Subalgebra.inclusion hS₀S).toRingHom (algebraMap S L)
      (algebraMap S₀ L) (by ext a; rfl)
  obtain ⟨E₀, hE₀f, hE₀s⟩ := @scalar_tower_eq.{u}
    (Spec (.of S₀)) (Spec (.of S)) (Spec (.of L)) κ₀S κSL κ₀L hCoeffTower P
  let Eambient : Pnest ≅ PL := E₁ ≪≫ E₀
  let EP := hPk.flip.isoOverPullback
  let qPn := EP.hom.left ≫ (modelScalarCone k.val Pk.hom).π.app (op ℓ)
  have hqPn : IsPullback qPn (flagVariety G).toSpec Pnest.hom ρL := hqPℓ
  let qPL := qPn ≫ Eambient.hom.left
  have hqPL : IsPullback qPL (flagVariety G).toSpec PL.hom ρL :=
    @cartesian_target_iso.{u+1,u} Scheme.{u} inferInstance (flagVariety G).scheme Pnest.left PL.left
      (Spec (.of K)) (Spec (.of L)) qPn (flagVariety G).toSpec Pnest.hom PL.hom ρL
      ((Over.forget _).mapIso Eambient) Eambient.hom.w hqPn
  let EFlag := Ek ≪≫ Eambient
  let jPL := fun w => chosenScalarArrow κℓ (jM w) ≫ EFlag.hom
  have htriangle (w : G.weylGroup) :
      qO w ≫ (jPL w).left = (oppositeSchubertInclusion G w).left ≫ qPL := by
    let sourceMap := (@coordinate_inclusion.{u}
      (oppositeSchubertVariety G w).scheme (flagVariety G).scheme T K kField.toCommRing
      (@variety_diagonal.{u} K kField (oppositeSchubertVariety G w))
      (@variety_diagonal.{u} K kField (flagVariety G))
      ((flagVariety G).closedInclusion (oppositeSchubertSupport G w)).left
      (inferInstanceAs (IsClosedImmersion
        ((flagVariety G).closedInclusion (oppositeSchubertSupport G w)).left))
      (flagVariety G).toSpec U hU).left
    have hMap : sourceMap = (oppositeSchubertInclusion G w).left :=
      @opposite_coordinate_inclusion.{u} K T kField kClosed kZero G w U hU
    exact @over_triangle_iso_trans.{u} (Spec (.of L)) (O w)
      (stageScalarModel k.val cFM.pt.hom ℓ) Pnest PL
      (oppositeSchubertVariety G w).scheme (flagVariety G).scheme
      (chosenScalarArrow κℓ (jM w)) Ek Eambient (qO w) qPn sourceMap
      (oppositeSchubertInclusion G w).left hMap (hOTriangle w)
  obtain ⟨hAmbientOld, hPnOld, hOldPL⟩ := @ambient_projection.{u}
    Pnest.left ((scalar_functor κSL).obj PS).left PL.left Pk.left PS.left P.left
    (flagVariety G).scheme E₁.hom.left E₀.hom.left Eambient.hom.left
    (pullback.snd κ₀L P.hom) (pullback.snd κSL PS.hom)
    (pullback.snd κ₀S P.hom) (pullback.snd κℓ Pk.hom)
    (pullback.snd κSk PS.hom) qPn qPk qPS qP rfl
    hE₀s hE₁s hProj hPksecond hPSsecond
  let geometry : CoefficientStage S₀ := ⟨L, ℓ.property.1, hS₀L⟩
  let CL := (scalar_functor κ₀L).obj C
  let xL := pullback.snd κ₀L C.hom ≫ qOriginal
  let endpointL := chosenScalarArrow κ₀L endpoint
  let tower₀LK : IsScalarTower S₀ L K :=
    Subalgebra.inclusion.isScalarTower_right hS₀L K
  obtain ⟨qCL, hqCL, _hqCLfirst, hqCLsecond⟩ := @scalar_flag.{u}
    S₀ L (inferInstanceAs (CommRing S₀)) (inferInstanceAs (CommRing L))
    (inferInstanceAs (Algebra S₀ L)) K kField.toCommRing
    (inferInstanceAs (Algebra S₀ K)) (inferInstanceAs (Algebra L K)) tower₀LK
    C (bsdhVariety G word).toOver qC hC
  have hEndpointL : bsdhMap G word ≫ qPL = qCL ≫ endpointL.left :=
    (@scalar_comparison.{u} (Spec (.of S₀)) (Spec (.of K)) (Spec (.of L)) κ₀L ρL
      C P (bsdhVariety G word).toOver (flagVariety G).toOver
      endpoint (@bsdhEndpointOver.{u} K kField kClosed kZero G word)
      qC qP qCL qPL hqCL hqPL hqCLsecond hOldPL hEndpoint.symm).symm
  have hWordL : qCL ≫ xL = M.m₀ :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ qOriginal) hqCLsecond).trans hWord)
  have hOriginalRaw : IsPullback xL CL.hom M.cG.pt.hom
      (κ₀L ≫ Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hMS).toRingHom)) :=
    (IsPullback.of_hasPullback κ₀L C.hom).flip.paste_horiz hOriginal
  have hCoeffM : κ₀L ≫ Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hMS).toRingHom) =
      Spec.map (CommRingCat.ofHom (Subalgebra.inclusion (hMS.trans hS₀L)).toRingHom) := by
    rw [← Spec.map_comp]
    rfl
  have hOriginalL := pullback_base_eq hOriginalRaw hCoeffM
  have hProperL : IsProper endpointL.left :=
    MorphismProperty.of_isPullback (P := @IsProper)
      (chosenScalarArrow_cartesian κ₀L endpoint).flip endpointProper
  have hPLproperties := @stage_properties.{u} K kField.toCommRing S₀ hS₀ P
    pCompact pFP geometry
  change LocallyOfFinitePresentation PL.hom ∧ CompactSpace PL.left ∧
    QuasiSeparatedSpace PL.left at hPLproperties
  have hClosedPL (w : G.weylGroup) : IsClosedImmersion (jPL w).left := by
    have hScalar : IsClosedImmersion (chosenScalarArrow κℓ (jM w)).left :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (chosenScalarArrow_cartesian κℓ (jM w)).flip (hjM w)
    exact @IsClosedImmersion.comp _ _ _ (chosenScalarArrow κℓ (jM w)).left
      EFlag.hom.left hScalar (inferInstanceAs (IsClosedImmersion EFlag.hom.left))
  choose simpleBound hSimpleStart hSimple using fun i : G.rootBase.support =>
    @RetainedCharacter.exists_opposition_compatible_stage.{u} K kField kClosed kZero
      G word M i L ℓ.property.1 (hMS.trans hS₀L)
      CL PL (O (RootPairing.weylGroup.ofIdx G.rootSystem
        (DeterminantSection.oppositionSimple G i)))
      hPLproperties.2.1 hPLproperties.2.2 hPLproperties.1
      (hOFP (RootPairing.weylGroup.ofIdx G.rootSystem
        (DeterminantSection.oppositionSimple G i)))
      xL hOriginalL qCL hqCL hWordL qPL hqPL endpointL hProperL hEndpointL
      (jPL (RootPairing.weylGroup.ofIdx G.rootSystem
        (DeterminantSection.oppositionSimple G i)))
      (hClosedPL (RootPairing.weylGroup.ofIdx G.rootSystem
        (DeterminantSection.oppositionSimple G i)))
      (qO (RootPairing.weylGroup.ofIdx G.rootSystem
        (DeterminantSection.oppositionSimple G i)))
      (hOCart (RootPairing.weylGroup.ofIdx G.rootSystem
        (DeterminantSection.oppositionSimple G i)))
      ((htriangle (RootPairing.weylGroup.ofIdx G.rootSystem
        (DeterminantSection.oppositionSimple G i))).symm) r
  obtain ⟨splittingBound, hStartBound, hSimpleBound⟩ :=
    finite_stage_bound simpleBound r
  have hFamilyBound : R.val ≤ splittingBound.val := hRr.trans hStartBound
  have hSimpleFields := @simple_field_compatible.{u} K kField kClosed kZero G word
    M L CL PL O jPL endpointL xL simpleBound splittingBound hSimpleBound hSimple
  have family_closure (κ : Type u) [κField : Field κ]
      [boundκAlg : Algebra splittingBound.val κ]
      (Z : Over (Spec (.of κ))) (qZ : Z.left ⟶ PL.left)
      (hZ : IsPullback qZ Z.hom PL.hom
        (Spec.map (CommRingCat.ofHom ((algebraMap splittingBound.val κ).comp
          (Subalgebra.inclusion splittingBound.property.2).toRingHom))))
      (p : ℕ) (σ : SchemeSplitting Z.left p) (hp : 1 < p)
      (hone : ∀ w, (weylCoxeterSystem G.rootBase).length w = 1 →
        σ.IsCompatible (closedFibreInclusion (O w) PL (jPL w) Z qZ).left.ker) :
      ∀ w, σ.IsCompatible (closedFibreInclusion (O w) PL (jPL w) Z qZ).left.ker := by
    let RκAlg : Algebra R.val κ :=
      ((algebraMap splittingBound.val κ).comp (Subalgebra.inclusion
        hFamilyBound).toRingHom).toAlgebra
    let : Algebra R.val κ := RκAlg
    let : Algebra k.val κ :=
      ((algebraMap R.val κ).comp (Subalgebra.inclusion R.property.2).toRingHom).toAlgebra
    let ρ := Spec.map (CommRingCat.ofHom ((algebraMap splittingBound.val κ).comp
      (Subalgebra.inclusion splittingBound.property.2).toRingHom))
    have hζ : ρ ≫ κℓ = Spec.map (CommRingCat.ofHom (algebraMap k.val κ)) :=
      spec_triangle (Subalgebra.inclusion ℓ.property.2).toRingHom
        ((algebraMap splittingBound.val κ).comp
          (Subalgebra.inclusion splittingBound.property.2).toRingHom)
        (algebraMap k.val κ) (by ext a; rfl)
    have hArithmeticκ := @hArithmeticFields κ κField RκAlg
    exact @scalar_closed_family_compatible.{u} k.val κ
      (inferInstanceAs (CommRing k.val)) κField.toCommRing
      (inferInstanceAs (Algebra k.val κ)) CI G.weylGroup inferInstance inferInstance
      F₀ B₀ hOpenF hDirF β₀ cFM hcFM.some cBM jM hjM hCharts
      (Spec (.of L)) κℓ ρ hζ PL EFlag Z qZ hZ p σ hp
      (weylCoxeterSystem G.rootBase).length 1
      (fun w hw => (weylCoxeterSystem G.rootBase).length_eq_zero_iff.mp hw)
      hArithmeticκ.2.2 hone hArithmeticκ.2.1
  have hstartGeometry : start ≤ geometry := hstartS.trans hSL
  unfold oppositeStageResult
  refine ⟨geometry, hstartGeometry, ?_⟩
  intro τ MT FT xT endpointT
  refine ⟨qCL, qPL, O, jPL, qO, hOriginalL, hqCL, hqPL, hqCLsecond, hOldPL,
    hOCart, hClosedPL, (fun w => ⟨hOFP w, hOCompact w, hOQS w⟩), hProperL,
    hWordL, hEndpointL, (fun w => (htriangle w).symm), splittingBound, ?_⟩
  intro κ κField boundκAlg W Z zQS qW qZ hW hZ e eIso he p pPrime κChar hp xκ LX m cκAlg data
  have hSimpleκ := @hSimpleFields κ κField boundκAlg W Z zQS qW qZ
    hW hZ e eIso he p pPrime κChar hp cκAlg data
  exact @family_closure κ κField boundκAlg Z qZ hZ p
    (data.sigma.pushforward e.left) pPrime.out.one_lt
    (@length_one_of_simple.{u} K kField kClosed kZero G
      (fun w => (data.sigma.pushforward e.left).IsCompatible
        (closedFibreInclusion (O w) PL (jPL w) Z qZ).left.ker) hSimpleκ)
/-- The splitting defined by a word section descends to a flag splitting
preserving every Schubert and opposite Schubert image ideal. -/
def flagSplittingFibres {K : Type u}
    [kField : Field K] [kClosed : IsAlgClosed K] [kZero : CharZero K]
    {G : ReductiveGroupData K} {word : List G.rootBase.support}
    (M : RetainedCharacter.PrefixModel G word)
    (S : Subalgebra ℤ K) (C F : Over (Spec (.of S)))
    (D : G.weylGroup → Over (Spec (.of S))) (j : ∀ x, D x ⟶ F)
    (O : G.weylGroup → Over (Spec (.of S))) (jO : ∀ x, O x ⟶ F)
    (endpoint : C ⟶ F) (qOriginal : C.left ⟶ M.cG.pt.left)
    (r : CoefficientStage S) : Prop :=
  ∀ (κ : Type u) [_κField : Field κ] [Algebra r.val κ]
    (W Z : Over (Spec (.of κ))) [CompactSpace W.left] [QuasiSeparatedSpace Z.left]
    (qW : W.left ⟶ C.left) (qZ : Z.left ⟶ F.left)
    (_hW : IsPullback qW W.hom C.hom
      (Spec.map (CommRingCat.ofHom ((algebraMap r.val κ).comp
        (Subalgebra.inclusion r.property.2).toRingHom))))
    (_hZ : IsPullback qZ Z.hom F.hom
      (Spec.map (CommRingCat.ofHom ((algebraMap r.val κ).comp
        (Subalgebra.inclusion r.property.2).toRingHom))))
    (e : W ⟶ Z) [QuasiCompact e.left]
    (_he : e.left ≫ qZ = qW ≫ endpoint.left)
    (B : Fin word.length → Over W.left)
    (b : ∀ k, (B k).left ⟶ (M.boundaries k).left)
    (_hB : ∀ k, IsPullback (B k).hom (b k) (qW ≫ qOriginal) (M.boundaries k).hom)
    (p : ℕ) [Fact p.Prime] [CharP κ p],
    ∃ hIso : IsIso e.left.c,
      let : IsIso e.left.c := hIso
      let L := (Scheme.Modules.pullback (qW ≫ qOriginal)).obj
        (@matchingModule.{u} M.S M.J (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing
          K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField)))
          M.S)
          M.N M.cG M.delta ((p - 1) / 2))
      let m := @pullSection.{u} W.left M.cG.pt.left (qW ≫ qOriginal)
        (@matchingModule.{u} M.S M.J (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing
          K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField)))
          M.S)
          M.N M.cG M.delta ((p - 1) / 2))
        (@coefficientMatchingSection.{u} M.S M.J (@Subalgebra.toCommRing ℤ K Int.instCommRing
          (@Field.toCommRing K kField) (@Ring.toIntAlgebra K (@DivisionRing.toRing K
          (@Field.toDivisionRing K kField))) M.S)
          M.N M.cG M.delta (fun j => (M.P (singletonIndex j)).coeff 2) M.hr
          ((p - 1) / 2))
      ∃ cκAlg : Algebra (ULift.{u} (ZMod p)) κ,
        ∃ data : @RetainedCharacter.SectionSplitting.{u} (ULift.{u} (ZMod p))
            (@Field.toCommRing (ULift.{u} (ZMod p))
              (inferInstanceAs (Field (ULift.{u} (ZMod p))))) p
            (inferInstanceAs (ExpChar (ULift.{u} (ZMod p)) p)) W.left
            (W.hom ≫ Spec.map (CommRingCat.ofHom
              (@algebraMap (ULift.{u} (ZMod p)) κ _ _ cκAlg))) L
            (m.app ⊤ (1 : Γ(W.left, ⊤))),
          (∀ k, data.sigma.IsCompatible (B k).hom.ker) ∧
          (∀ x, (data.sigma.pushforward e.left).IsCompatible (pullback.fst qZ (j x).left).ker) ∧
          ∀ x, (data.sigma.pushforward e.left).IsCompatible (pullback.fst qZ (jO x).left).ker

/-- The coefficient models and a common splitting of their flag fibres. -/
private def flagStageResult {K : Type u}
    [kField : Field K] [kClosed : IsAlgClosed K] [kZero : CharZero K]
    {G : ReductiveGroupData K} {word : List G.rootBase.support}
    (M : RetainedCharacter.PrefixModel G word)
    (initial : CoefficientStage M.S) (F : Over (Spec (.of initial.val)))
    (qF : (flagVariety G).scheme ⟶ F.left)
    (start : CoefficientStage initial.val) : Prop :=
  ∃ (t : CoefficientStage initial.val), start ≤ t ∧
    ∃ (MT FT : Over (Spec (.of t.val)))
      (DT OT : G.weylGroup → Over (Spec (.of t.val)))
      (jT : ∀ w, DT w ⟶ FT) (jOT : ∀ w, OT w ⟶ FT)
      (endpoint : MT ⟶ FT) (qMT : MT.left ⟶ M.cG.pt.left)
      (m : bsdhScheme G word ⟶ MT.left)
      (q : (flagVariety G).scheme ⟶ FT.left)
      (pFT : FT.left ⟶ F.left)
      (qDT : ∀ w, (schubertVariety G w).toOver.left ⟶ (DT w).left)
      (qOT : ∀ w, (oppositeSchubertVariety G w).scheme ⟶ (OT w).left),
      IsPullback qMT MT.hom M.cG.pt.hom
        (Spec.map (CommRingCat.ofHom
          (Subalgebra.inclusion (initial.property.2.trans t.property.2)).toRingHom)) ∧
      IsPullback m (bsdhToSpec G word) MT.hom
        (Spec.map (CommRingCat.ofHom (algebraMap t.val K))) ∧
      IsPullback q (flagVariety G).toSpec FT.hom
        (Spec.map (CommRingCat.ofHom (algebraMap t.val K))) ∧
      IsPullback pFT FT.hom F.hom
        (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion t.property.2).toRingHom)) ∧
      q ≫ pFT = qF ∧
      (∀ w, IsPullback (qDT w) (schubertVariety G w).toOver.hom (DT w).hom
        (Spec.map (CommRingCat.ofHom (algebraMap t.val K)))) ∧
      (∀ w, IsPullback (qOT w) (oppositeSchubertVariety G w).toSpec (OT w).hom
        (Spec.map (CommRingCat.ofHom (algebraMap t.val K)))) ∧
      (∀ w, IsClosedImmersion (jT w).left ∧
        LocallyOfFinitePresentation (DT w).hom ∧ CompactSpace (DT w).left ∧
        QuasiSeparatedSpace (DT w).left) ∧
      (∀ w, IsClosedImmersion (jOT w).left ∧
        LocallyOfFinitePresentation (OT w).hom ∧ CompactSpace (OT w).left ∧
        QuasiSeparatedSpace (OT w).left) ∧
      LocallyOfFinitePresentation FT.hom ∧ CompactSpace FT.left ∧
      QuasiSeparatedSpace FT.left ∧ IsSeparated FT.hom ∧
      m ≫ qMT = M.m₀ ∧ bsdhMap G word ≫ q = m ≫ endpoint.left ∧
      (∀ w, (schubertInclusion G w).left ≫ q = qDT w ≫ (jT w).left) ∧
      (∀ w, (oppositeSchubertInclusion G w).left ≫ q = qOT w ≫ (jOT w).left) ∧
      let boundaries := fun v => Over.mk (pullback.fst qMT (M.boundaries v).hom)
      (∀ v, IsClosedImmersion (boundaries v).hom) ∧
      ∃ (n : ∀ v, bsdhScheme G (word.eraseIdx v.val) ⟶ (boundaries v).left),
        (∀ v, IsPullback (bsdhOmitMap G word v) (n v) m (boundaries v).hom) ∧
        ∃ r : CoefficientStage t.val,
          @flagSplittingFibres.{u} K kField kClosed kZero G word M
            t.val MT FT DT jT OT jOT endpoint qMT r

/-- A model of a reduced longest word gives a common coefficient stage whose
flag fibres have one splitting compatible with every Schubert model and every
opposite Schubert model. -/
theorem exists_flag_splitting_stage {K : Type u}
    [kField : Field K] [kClosed : IsAlgClosed K] [kZero : CharZero K]
    {G : ReductiveGroupData K} {word : List G.rootBase.support}
    (M : RetainedCharacter.PrefixModel G word) (hM : RetainedCharacter.PrefixSplits M)
    (initial : CoefficientStage M.S) (C F : Over (Spec (.of initial.val)))
    (qOriginal : C.left ⟶ M.cG.pt.left)
    (hOriginal : IsPullback qOriginal C.hom M.cG.pt.hom
      (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion initial.property.2).toRingHom)))
    (qC : bsdhScheme G word ⟶ C.left)
    (hC : IsPullback qC (bsdhToSpec G word) C.hom
      (Spec.map (CommRingCat.ofHom (algebraMap initial.val K))))
    (hOriginalNative : qC ≫ qOriginal = M.m₀)
    (hred : (weylCoxeterSystem G.rootBase).IsReduced word)
    (hw : simpleWeylWord G.rootBase word = G.longestElement)
    (D : G.weylGroup → Over (Spec (.of initial.val)))
    [CompactSpace F.left] [IsSeparated F.hom] [LocallyOfFinitePresentation F.hom]
    [∀ x, CompactSpace (D x).left] [∀ x, QuasiSeparatedSpace (D x).left]
    [∀ x, LocallyOfFinitePresentation (D x).hom]
    (j : ∀ x, D x ⟶ F) (hjclosed : ∀ x, IsClosedImmersion (j x).left)
    (qD : ∀ x, (schubertVariety G x).toOver.left ⟶ (D x).left)
    (hD : ∀ x, IsPullback (qD x) (schubertVariety G x).toOver.hom (D x).hom
      (Spec.map (CommRingCat.ofHom (algebraMap initial.val K))))
    (qF : (flagVariety G).scheme ⟶ F.left)
    (hF : IsPullback qF (flagVariety G).toSpec F.hom
      (Spec.map (CommRingCat.ofHom (algebraMap initial.val K))))
    (hj : ∀ x, (schubertInclusion G x).left ≫ qF = qD x ≫ (j x).left)
    (start : CoefficientStage initial.val) :
  ∃ (t : CoefficientStage initial.val), start ≤ t ∧
    ∃ (MT FT : Over (Spec (.of t.val)))
      (DT OT : G.weylGroup → Over (Spec (.of t.val)))
      (jT : ∀ w, DT w ⟶ FT) (jOT : ∀ w, OT w ⟶ FT)
      (endpoint : MT ⟶ FT) (qMT : MT.left ⟶ M.cG.pt.left)
      (m : bsdhScheme G word ⟶ MT.left)
      (q : (flagVariety G).scheme ⟶ FT.left)
      (pFT : FT.left ⟶ F.left)
      (qDT : ∀ w, (schubertVariety G w).toOver.left ⟶ (DT w).left)
      (qOT : ∀ w, (oppositeSchubertVariety G w).scheme ⟶ (OT w).left),
      IsPullback qMT MT.hom M.cG.pt.hom
        (Spec.map (CommRingCat.ofHom
          (Subalgebra.inclusion (initial.property.2.trans t.property.2)).toRingHom)) ∧
      IsPullback m (bsdhToSpec G word) MT.hom
        (Spec.map (CommRingCat.ofHom (algebraMap t.val K))) ∧
      IsPullback q (flagVariety G).toSpec FT.hom
        (Spec.map (CommRingCat.ofHom (algebraMap t.val K))) ∧
      IsPullback pFT FT.hom F.hom
        (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion t.property.2).toRingHom)) ∧
      q ≫ pFT = qF ∧
      (∀ w, IsPullback (qDT w) (schubertVariety G w).toOver.hom (DT w).hom
        (Spec.map (CommRingCat.ofHom (algebraMap t.val K)))) ∧
      (∀ w, IsPullback (qOT w) (oppositeSchubertVariety G w).toSpec (OT w).hom
        (Spec.map (CommRingCat.ofHom (algebraMap t.val K)))) ∧
      (∀ w, IsClosedImmersion (jT w).left ∧
        LocallyOfFinitePresentation (DT w).hom ∧ CompactSpace (DT w).left ∧
        QuasiSeparatedSpace (DT w).left) ∧
      (∀ w, IsClosedImmersion (jOT w).left ∧
        LocallyOfFinitePresentation (OT w).hom ∧ CompactSpace (OT w).left ∧
        QuasiSeparatedSpace (OT w).left) ∧
      LocallyOfFinitePresentation FT.hom ∧ CompactSpace FT.left ∧
      QuasiSeparatedSpace FT.left ∧ IsSeparated FT.hom ∧
      m ≫ qMT = M.m₀ ∧ bsdhMap G word ≫ q = m ≫ endpoint.left ∧
      (∀ w, (schubertInclusion G w).left ≫ q = qDT w ≫ (jT w).left) ∧
      (∀ w, (oppositeSchubertInclusion G w).left ≫ q = qOT w ≫ (jOT w).left) ∧
      let boundaries := fun v => Over.mk (pullback.fst qMT (M.boundaries v).hom)
      (∀ v, IsClosedImmersion (boundaries v).hom) ∧
      ∃ (n : ∀ v, bsdhScheme G (word.eraseIdx v.val) ⟶ (boundaries v).left),
        (∀ v, IsPullback (bsdhOmitMap G word v) (n v) m (boundaries v).hom) ∧
        ∃ r : CoefficientStage t.val,
          @flagSplittingFibres.{u} K kField kClosed kZero G word M
            t.val MT FT DT jT OT jOT endpoint qMT r
 := by
  change @flagStageResult.{u} K kField kClosed kZero G word M initial F qF start
  classical
  obtain ⟨t, ht, hStage⟩ :=
    @exists_prefix_schubert_stage.{u} K kField kClosed kZero G word M initial C F
      qOriginal hOriginal qC hC hOriginalNative hred D inferInstance inferInstance inferInstance
        inferInstance j hjclosed qD hD qF hF hj start
  let τ := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion t.property.2).toRingHom)
  let MT := stageScalarModel initial.val C.hom t
  let FT := stageScalarModel initial.val F.hom t
  let DT := fun w => stageScalarModel initial.val (D w).hom t
  let jT := fun w => chosenScalarArrow τ (j w)
  let qMT := pullback.snd τ C.hom ≫ qOriginal
  let boundaries := fun v => Over.mk (pullback.fst qMT (M.boundaries v).hom)
  obtain ⟨endpoint, m, q, qDT, hm, hq, hqProjection, hDT, hmProjection, hEndpoint, hjT,
    n, hn, r, hImages⟩ := hStage
  let : IsProper C.hom := MorphismProperty.of_isPullback (P := @IsProper) hOriginal M.proper
  let : Smooth C.hom := MorphismProperty.of_isPullback (P := @Smooth) hOriginal M.smoothModel
  let : GeometricallyConnected C.hom :=
    MorphismProperty.of_isPullback (P := @GeometricallyConnected) hOriginal M.connected
  let : IsProper MT.hom := by
    change IsProper (pullback.fst τ C.hom)
    infer_instance
  let : Smooth MT.hom := by
    change Smooth (pullback.fst τ C.hom)
    infer_instance
  let : GeometricallyConnected MT.hom := by
    change GeometricallyConnected (pullback.fst τ C.hom)
    infer_instance
  let : MT.left.IsSeparated := by
    constructor
    rw [← terminal.comp_from MT.hom]
    infer_instance
  let : IsSeparated FT.hom := by
    change IsSeparated (pullback.fst τ F.hom)
    infer_instance
  let : CompactSpace FT.left := by
    change CompactSpace ((modelScalarStages initial.val F.hom).obj (Opposite.op t))
    infer_instance
  let : FT.left.IsSeparated := by
    constructor
    rw [← terminal.comp_from FT.hom]
    infer_instance
  let : LocallyOfFinitePresentation FT.hom := by
    change LocallyOfFinitePresentation (pullback.fst τ F.hom)
    infer_instance
  obtain ⟨k, hrk, _hs, _hgc, _qC, _qF, _hC, _hF, _holdC, _holdF, _heK, hFibres⟩ :=
    @exists_flag_pushforward_stage.{u} K kField kClosed kZero G word hred hw
      t.val t.property.1 MT FT inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance inferInstance inferInstance
      endpoint m q hm hq hEndpoint.symm r

  have hMST : M.S ≤ t.val := initial.property.2.trans t.property.2
  have hOriginalT0 : IsPullback qMT MT.hom M.cG.pt.hom
      (τ ≫ Spec.map (CommRingCat.ofHom
        (Subalgebra.inclusion initial.property.2).toRingHom)) :=
    (IsPullback.of_hasPullback τ C.hom).flip.paste_horiz hOriginal
  have hCoefficientT : τ ≫ Spec.map (CommRingCat.ofHom
        (Subalgebra.inclusion initial.property.2).toRingHom) =
      Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hMST).toRingHom) :=
    spec_triangle (Subalgebra.inclusion initial.property.2).toRingHom
      (Subalgebra.inclusion t.property.2).toRingHom
      (Subalgebra.inclusion hMST).toRingHom (by ext a; rfl)
  have hOriginalT := pullback_base_eq hOriginalT0 hCoefficientT
  have hEndpointProper : IsProper endpoint.left := endpoint_proper MT FT endpoint
  have hOpp := @exists_opposite_stage.{u} K kField kClosed kZero G word M
    t.val t.property.1 hMST MT FT (inferInstanceAs (CompactSpace FT.left))
    (inferInstanceAs (LocallyOfFinitePresentation FT.hom)) qMT hOriginalT m hm
    hmProjection q hq endpoint hEndpointProper hEndpoint k
  unfold oppositeStageResult at hOpp
  obtain ⟨geometry, hkGeometry, hOpp⟩ := hOpp
  let beta := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion geometry.property.2).toRingHom)
  let ML := stageScalarModel t.val MT.hom geometry
  let FL := stageScalarModel t.val FT.hom geometry
  let xL := pullback.snd beta MT.hom ≫ qMT
  let endpointL := chosenScalarArrow beta endpoint
  obtain ⟨mL, qL, OT, jOT, qOT, hOriginalL, hmL, hqL, hmLold, hqLold,
    hOT, hJOTclosed, hOTproperties, hEndpointProperL, hWordL, hEndpointL,
    hJOT, bound, hOppFields⟩ := hOpp
  have hNative := @scalar_schubert_boundaries.{u} K kField kClosed kZero G word M
    t.val MT FT qMT DT jT qDT hDT q hjT geometry mL qL hqL hWordL hqLold
  let DL := fun w => stageScalarModel t.val (DT w).hom geometry
  let jDL := fun w => chosenScalarArrow beta (jT w)
  let boundaryL := fun v => Over.mk (pullback.fst xL (M.boundaries v).hom)
  obtain ⟨qDL, hDL, hjDL, hBoundaryClosed, nL, hnL⟩ := hNative
  have hOldDProperties (w : G.weylGroup) := @stage_properties.{u} K kField.toCommRing
    initial.val initial.property.1 (D w)
    (inferInstanceAs (CompactSpace (D w).left))
    (inferInstanceAs (LocallyOfFinitePresentation (D w).hom)) t
  have hDLProperties (w : G.weylGroup) := @stage_properties.{u} K kField.toCommRing
    t.val t.property.1 (DT w) (hOldDProperties w).2.1 (hOldDProperties w).1 geometry
  have hFLProperties := @stage_properties.{u} K kField.toCommRing
    t.val t.property.1 FT (inferInstanceAs (CompactSpace FT.left))
    (inferInstanceAs (LocallyOfFinitePresentation FT.hom)) geometry
  have hOldClosed (w : G.weylGroup) : IsClosedImmersion (jT w).left :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (chosenScalarArrow_cartesian τ (j w)).flip (hjclosed w)
  have hDLClosed (w : G.weylGroup) : IsClosedImmersion (jDL w).left :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (chosenScalarArrow_cartesian beta (jT w)).flip (hOldClosed w)
  have hFLSeparated : IsSeparated FL.hom := by
    change IsSeparated (pullback.fst beta FT.hom)
    infer_instance
  let outStage := @singleScalarStage.{u} K kField.toCommRing initial.val t geometry
  have hStartOut : start ≤ outStage := ht.trans geometry.property.2
  have hkBound : k.val ≤ bound.val :=
    (show k.val ≤ geometry.val from hkGeometry).trans bound.property.2
  have hrBound : r.val ≤ bound.val := (show r.val ≤ k.val from hrk).trans hkBound
  let pFT : FL.left ⟶ F.left :=
    pullback.snd beta FT.hom ≫ pullback.snd τ F.hom
  have hFTCoefficient : beta ≫ τ =
      Spec.map (CommRingCat.ofHom (Subalgebra.inclusion outStage.property.2).toRingHom) :=
    @spec_triangle.{u} initial.val t.val geometry.val
      (inferInstanceAs (CommRing initial.val)) (inferInstanceAs (CommRing t.val))
      (inferInstanceAs (CommRing geometry.val))
      (Subalgebra.inclusion t.property.2).toRingHom
      (Subalgebra.inclusion geometry.property.2).toRingHom
      (Subalgebra.inclusion outStage.property.2).toRingHom (by ext a; rfl)
  have hFTProjection0 : IsPullback pFT FL.hom F.hom (beta ≫ τ) :=
    (IsPullback.of_hasPullback beta FT.hom).flip.paste_horiz
      (IsPullback.of_hasPullback τ F.hom).flip
  have hFTProjection := pullback_base_eq hFTProjection0 hFTCoefficient
  have hNativeProjection : qL ≫ pFT = qF :=
    (Category.assoc qL (pullback.snd beta FT.hom) (pullback.snd τ F.hom)).symm.trans
      ((congrArg (fun q => q ≫ pullback.snd τ F.hom) hqLold).trans hqProjection)
  unfold flagStageResult
  refine ⟨outStage, hStartOut, ML, FL, DL, OT, jDL, jOT, endpointL, xL,
    mL, qL, pFT, qDL, qOT, hOriginalL, hmL, hqL, hFTProjection, hNativeProjection, hDL, hOT,
    (fun w => ⟨hDLClosed w, (hDLProperties w).1, (hDLProperties w).2.1,
      (hDLProperties w).2.2⟩),
    (fun w => ⟨hJOTclosed w, (hOTproperties w).1, (hOTproperties w).2.1,
      (hOTproperties w).2.2⟩),
    hFLProperties.1, hFLProperties.2.1, hFLProperties.2.2, hFLSeparated,
    hWordL, hEndpointL, hjDL, hJOT, ?_⟩
  intro boundariesL
  refine ⟨hBoundaryClosed, nL, hnL, bound, ?_⟩
  intro κ κField boundκAlg W Z wCompact zQS qW qZ hW hZ e eQuasi he B b hB p hpPrime κChar
  let joined := @singleScalarStage.{u} K kField.toCommRing t.val geometry bound
  let kκAlg : Algebra k.val κ :=
    ((algebraMap joined.val κ).comp (Subalgebra.inclusion hkBound).toRingHom).toAlgebra
  have hSmall := @coefficient_spec_eq.{u} K κ kField.toCommRing κField.toCommRing
    t.val k joined hkBound boundκAlg
  let coefficient := Spec.map (CommRingCat.ofHom
    ((algebraMap joined.val κ).comp (Subalgebra.inclusion joined.property.2).toRingHom))
  have hTower : Spec.map (CommRingCat.ofHom ((algebraMap bound.val κ).comp
        (Subalgebra.inclusion bound.property.2).toRingHom)) ≫ beta = coefficient :=
    @spec_triangle.{u} t.val geometry.val κ (inferInstanceAs (CommRing t.val))
      (inferInstanceAs (CommRing geometry.val)) κField.toCommRing
      (Subalgebra.inclusion geometry.property.2).toRingHom
      ((algebraMap bound.val κ).comp (Subalgebra.inclusion bound.property.2).toRingHom)
      ((algebraMap joined.val κ).comp (Subalgebra.inclusion joined.property.2).toRingHom) rfl
  let qWold := qW ≫ pullback.snd beta MT.hom
  let qZold := qZ ≫ pullback.snd beta FT.hom
  have hWold0 := hW.paste_horiz (IsPullback.of_hasPullback beta MT.hom).flip
  have hZold0 := hZ.paste_horiz (IsPullback.of_hasPullback beta FT.hom).flip
  have hWold := pullback_base_eq (pullback_base_eq hWold0 hTower) hSmall.symm
  have hZold := pullback_base_eq (pullback_base_eq hZold0 hTower) hSmall.symm
  have hPushCoefficient := spec_triangle (Subalgebra.inclusion k.property.2).toRingHom
    (@algebraMap k.val κ _ _ kκAlg)
    ((@algebraMap k.val κ _ _ kκAlg).comp (Subalgebra.inclusion k.property.2).toRingHom) rfl
  have hWpush := pullback_base_eq hWold hPushCoefficient.symm
  have hZpush := pullback_base_eq hZold hPushCoefficient.symm
  have heOld : e.left ≫ qZold = qWold ≫ endpoint.left :=
    @endpoint_scalar_projection.{u} (Spec (.of t.val)) (Spec (.of geometry.val))
      W.left Z.left beta MT FT endpoint qW qZ e.left he
  obtain ⟨_hIntegral, _hConnected, _hProper, _hSmooth, _hNormal, _hBirational, hIso⟩ :=
    @hFibres κ κField kκAlg W Z qWold qZold hWpush hZpush e heOld
  let : IsIso e.left.c := hIso
  have hSource := hW.paste_horiz hOriginalL
  obtain ⟨cκAlg, data, hBoundary⟩ :=
    @prime_fibre_compatible.{u} K kField kClosed kZero G word M hM κ κField p hpPrime κChar
      (Spec.map (CommRingCat.ofHom ((algebraMap bound.val κ).comp
        (Subalgebra.inclusion bound.property.2).toRingHom)) ≫
        Spec.map (CommRingCat.ofHom
          (Subalgebra.inclusion (hMST.trans geometry.property.2)).toRingHom))
      W.left W.hom (qW ≫ xL) hSource B b hB
  have hOrdinary := @ordinary_field_compatible.{u} K kField kClosed kZero G word
    t.val MT FT DT jT endpoint M.cG.pt.left qMT M.boundaries r geometry bound
    hrBound hImages κ κField boundκAlg W Z wCompact zQS qW qZ hW hZ
    e eQuasi hIso he B b hB p data.sigma hBoundary
  have hMSToBound : M.S ≤ bound.val := hMST.trans (geometry.property.2.trans bound.property.2)
  have hOdd : Odd p := @odd_of_two_unit.{u} M.S κ
    (inferInstanceAs (CommSemiring M.S)) κField
    ((algebraMap bound.val κ).comp (Subalgebra.inclusion hMSToBound).toRingHom)
    M.twoUnit p hpPrime κChar
  have hOpposite := @hOppFields κ κField boundκAlg W Z zQS qW qZ hW hZ
    e hIso he p hpPrime κChar hOdd cκAlg data
  refine ⟨hIso, cκAlg, data, hBoundary, ?_, hOpposite⟩
  intro w
  exact hOrdinary w (by rw [hw]; exact @weyl_le_longest.{u} K kField kClosed kZero G w)

end SchubertGeometry
