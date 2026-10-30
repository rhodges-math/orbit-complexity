import Batteries.Tactic.Lint
import OrbitComplexity.FrobeniusSplitting.Normality.Connectedness.StageOriginTransport
import OrbitComplexity.SchubertGeometry.Connectedness.CellAnchorMaps
import OrbitComplexity.SchubertGeometry.Connectedness.RootEndpointModels

set_option autoImplicit false

/-! # Cell maps and reflection-root curves on one coefficient stage

All nonempty cell pieces retain their maps into the chosen Richardson model.
A finite family of reflection-root curves meets the anchors formed from the
origins of those same cell models at a common coefficient stage.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
  ReductiveGroups FrobeniusSplitting GroupActions

namespace SchubertGeometry.CellContraction

universe u v

private theorem assemble_family {A B C : Sort*}
    {P : A → Prop} {Q : A → B → C → Prop}
    (a : A) (b : B) (c : C) (hp : P a) (hq : Q a b c) :
    ∃ (a : A) (b : B) (c : C), P a ∧ Q a b c :=
  ⟨a, b, c, hp, hq⟩

private theorem bind_stage {J : Type*} [Preorder J] {A : J → Sort*}
    {P : ∀ j, A j → Prop} {Q : J → Prop} {i : J}
    (h : ∃ (j : J) (_ : i ≤ j) (a : A j), P j a)
    (next : ∀ j (a : A j), P j a → ∃ (k : J) (_ : j ≤ k), Q k) :
    ∃ (k : J) (_ : i ≤ k), Q k := by
  obtain ⟨j, hij, a, ha⟩ := h
  obtain ⟨k, hjk, hk⟩ := next j a ha
  exact ⟨k, hij.trans hjk, hk⟩

private theorem map_tower {J : Type*} [Preorder J] {A B : J → Sort*} {i : J}
    {P : ∀ (l : J), i ≤ l → ∀ (j : J), l ≤ j →
      ∀ (k : J), j ≤ k → A k → B k → Prop} {Q : J → Prop}
    (h : ∃ (l : J) (hil : i ≤ l) (j : J) (hlj : l ≤ j)
      (k : J) (hjk : j ≤ k) (a : A k) (b : B k), P l hil j hlj k hjk a b)
    (next : ∀ l hil j hlj k hjk a b, P l hil j hlj k hjk a b → Q k) :
    ∃ (k : J) (_ : i ≤ k), Q k := by
  obtain ⟨l, hil, j, hlj, k, hjk, a, b, hp⟩ := h
  exact ⟨k, hil.trans (hlj.trans hjk), next l hil j hlj k hjk a b hp⟩

private theorem bool_family {I J A B : Type*} (P : A → B → Prop)
    (F : J → A) (H : J → B) (v₀ v₁ : I → J)
    (h : ∀ t, P (F t) (H t)) :
    ∀ r : I × Bool, P (F (if r.2 then v₁ r.1 else v₀ r.1))
      (if r.2 then H (v₁ r.1) else H (v₀ r.1)) := by
  rintro ⟨r, bit⟩
  cases bit
  · exact h (v₀ r)
  · exact h (v₁ r)

private theorem left_comp_assoc {T : Type*} [Category T] {B : T}
    {X Y Z : Over B} (f : X ⟶ Y) (g : Y ⟶ Z)
    {W : T} (h : Z.left ⟶ W) :
    f.left ≫ g.left ≫ h = (f ≫ g).left ≫ h :=
  (Category.assoc _ _ _).symm

private theorem anchor_extend_three {K : Type u} [CommRing K]
    (S : Subalgebra ℤ K) {X Y U : Scheme.{u}}
    (a : X ⟶ Spec (.of S)) (b : Y ⟶ Spec (.of S)) (c : U ⟶ Spec (.of S))
    (s : Spec (.of S) ⟶ X) (hs : s ≫ a = 𝟙 _)
    {i l j k : CoefficientStage S} (hil : i ≤ l) (hlj : l ≤ j) (hjk : j ≤ k)
    (f : stageScalarModel S a i ⟶ stageScalarModel S b i)
    (A : stageScalarModel S c i ⟶ stageScalarModel S b i)
    (B : stageScalarModel S c k ⟶ stageScalarModel S b k)
    (hA : A = anchorArrow (stageScalarModel S c i)
      (stageOriginSection S a s hs i) (stageOriginSection_base S a s hs i) f)
    (hB : B = anchorArrow (stageScalarModel S c k)
      (stageOriginSection S a s hs k) (stageOriginSection_base S a s hs k)
      (extendModelMorphism S a b hjk
        (extendModelMorphism S a b hlj (extendModelMorphism S a b hil f)))) :
    extendModelMorphism S c b hjk
      (extendModelMorphism S c b hlj (extendModelMorphism S c b hil A)) = B := by
  rw [hA, anchorArrow_extend, anchorArrow_extend, anchorArrow_extend]
  exact hB.symm

private theorem map_extend_three {K : Type u} [CommRing K]
    (S : Subalgebra ℤ K) {X Y : Scheme.{u}}
    (a : X ⟶ Spec (.of S)) (b : Y ⟶ Spec (.of S))
    {i l j k : CoefficientStage S} (hil : i ≤ l) (hlj : l ≤ j) (hjk : j ≤ k)
    (f : stageScalarModel S a i ⟶ stageScalarModel S b i)
    (g : genericScalarModel S a ⟶ genericScalarModel S b)
    (h : (modelScalarCone S a).π.app (op i) ≫ f.left =
      g.left ≫ (modelScalarCone S b).π.app (op i)) :
    (modelScalarCone S a).π.app (op k) ≫
        (extendModelMorphism S a b hjk
          (extendModelMorphism S a b hlj (extendModelMorphism S a b hil f))).left =
      g.left ≫ (modelScalarCone S b).π.app (op k) := by
  have h₁ := extendModelMorphism_baseChange S a b hil f g h
  have h₂ := extendModelMorphism_baseChange S a b hlj
    (extendModelMorphism S a b hil f) g h₁
  exact extendModelMorphism_baseChange S a b hjk
    (extendModelMorphism S a b hlj (extendModelMorphism S a b hil f)) g h₂

private theorem triangle_transport {T : Type*} [Category T] {B₀ B₁ B₂ : T}
    {A B Z : Over B₀} {Ai Bi : Over B₁} {Aj Bj : Over B₂}
    {ρ : B₂ ⟶ B₁} (tA : Aj.left ⟶ Ai.left) (tB : Bj.left ⟶ Bi.left)
    (hcart : IsPullback tB Bj.hom Bi.hom ρ)
    (qAi : A.left ⟶ Ai.left) (qAj : A.left ⟶ Aj.left)
    (qBi : B.left ⟶ Bi.left) (qBj : B.left ⟶ Bj.left) (κ : B₀ ⟶ B₂)
    (f : Ai ⟶ Bi) (F : Aj ⟶ Bj) (q : Z ⟶ A) (g : Z ⟶ B)
    (ht : F.left ≫ tB = tA ≫ f.left)
    (ha : qAj ≫ tA = qAi) (hb : qBj ≫ tB = qBi)
    (hbaseA : qAj ≫ Aj.hom = A.hom ≫ κ)
    (hbaseB : qBj ≫ Bj.hom = B.hom ≫ κ)
    (h : (q.left ≫ qAi) ≫ f.left = g.left ≫ qBi) :
    (q.left ≫ qAj) ≫ F.left = g.left ≫ qBj := by
  apply hcart.hom_ext
  · calc
      ((q.left ≫ qAj) ≫ F.left) ≫ tB =
          (q.left ≫ qAj) ≫ (F.left ≫ tB) := Category.assoc _ _ _
      _ = (q.left ≫ qAj) ≫ (tA ≫ f.left) :=
        congrArg (fun t => (q.left ≫ qAj) ≫ t) ht
      _ = ((q.left ≫ qAj) ≫ tA) ≫ f.left := (Category.assoc _ _ _).symm
      _ = (q.left ≫ (qAj ≫ tA)) ≫ f.left :=
        congrArg (fun t => t ≫ f.left) (Category.assoc _ _ _)
      _ = (q.left ≫ qAi) ≫ f.left :=
        congrArg (fun t => (q.left ≫ t) ≫ f.left) ha
      _ = g.left ≫ qBi := h
      _ = g.left ≫ (qBj ≫ tB) := congrArg (fun t => g.left ≫ t) hb.symm
      _ = (g.left ≫ qBj) ≫ tB := (Category.assoc _ _ _).symm
  · calc
      ((q.left ≫ qAj) ≫ F.left) ≫ Bj.hom =
          (q.left ≫ qAj) ≫ (F.left ≫ Bj.hom) := Category.assoc _ _ _
      _ = (q.left ≫ qAj) ≫ Aj.hom :=
        congrArg (fun t => (q.left ≫ qAj) ≫ t) F.w
      _ = q.left ≫ (qAj ≫ Aj.hom) := Category.assoc _ _ _
      _ = q.left ≫ (A.hom ≫ κ) := congrArg (fun t => q.left ≫ t) hbaseA
      _ = (q.left ≫ A.hom) ≫ κ :=
        (Category.assoc _ _ _).symm
      _ = Z.hom ≫ κ := congrArg (fun t => t ≫ κ) q.w
      _ = (g.left ≫ B.hom) ≫ κ :=
        congrArg (fun t => t ≫ κ) g.w.symm
      _ = g.left ≫ (B.hom ≫ κ) := Category.assoc _ _ _
      _ = g.left ≫ (qBj ≫ Bj.hom) :=
        congrArg (fun t => g.left ≫ t) hbaseB.symm
      _ = (g.left ≫ qBj) ≫ Bj.hom :=
        (Category.assoc _ _ _).symm

private theorem triangle_extend {K : Type u} [CommRing K]
    (S : Subalgebra ℤ K) {X Y : Scheme.{u}}
    (a : X ⟶ Spec (.of S)) (b : Y ⟶ Spec (.of S))
    {i j : CoefficientStage S} (hij : i ≤ j)
    (f : stageScalarModel S a i ⟶ stageScalarModel S b i)
    {Z : Over (Spec (.of K))} (q : Z ⟶ genericScalarModel S a)
    (g : Z ⟶ genericScalarModel S b)
    (h : (q.left ≫ (modelScalarCone S a).π.app (op i)) ≫ f.left =
      g.left ≫ (modelScalarCone S b).π.app (op i)) :
    (q.left ≫ (modelScalarCone S a).π.app (op j)) ≫
        (extendModelMorphism S a b hij f).left =
      g.left ≫ (modelScalarCone S b).π.app (op j) := by
  exact triangle_transport
    (A := genericScalarModel S a) (B := genericScalarModel S b) (Z := Z)
    (Ai := stageScalarModel S a i) (Bi := stageScalarModel S b i)
    (Aj := stageScalarModel S a j) (Bj := stageScalarModel S b j)
    (stageScalarTransition S a hij) (stageScalarTransition S b hij)
    (stageScalarCartesian S b hij)
    ((modelScalarCone S a).π.app (op i)) ((modelScalarCone S a).π.app (op j))
    ((modelScalarCone S b).π.app (op i)) ((modelScalarCone S b).π.app (op j))
    (Spec.map (CommRingCat.ofHom (algebraMap j.val K)))
    f (extendModelMorphism S a b hij f) q g
    (extendModelMorphism_transition S a b hij f)
    ((modelScalarCone S a).w ((homOfLE hij).op))
    ((modelScalarCone S b).w ((homOfLE hij).op))
    (modelScalarCone_base S a j) (modelScalarCone_base S b j) h

private theorem triangle_extend_three {K : Type u} [CommRing K]
    (S : Subalgebra ℤ K) {X Y : Scheme.{u}}
    (a : X ⟶ Spec (.of S)) (b : Y ⟶ Spec (.of S))
    {i l j k : CoefficientStage S} (hil : i ≤ l) (hlj : l ≤ j) (hjk : j ≤ k)
    (f : stageScalarModel S a i ⟶ stageScalarModel S b i)
    {Z : Over (Spec (.of K))} (q : Z ⟶ genericScalarModel S a)
    (g : Z ⟶ genericScalarModel S b)
    (h : (q.left ≫ (modelScalarCone S a).π.app (op i)) ≫ f.left =
      g.left ≫ (modelScalarCone S b).π.app (op i)) :
    (q.left ≫ (modelScalarCone S a).π.app (op k)) ≫
        (extendModelMorphism S a b hjk
          (extendModelMorphism S a b hlj (extendModelMorphism S a b hil f))).left =
      g.left ≫ (modelScalarCone S b).π.app (op k) := by
  have h₁ := triangle_extend S a b hil f q g h
  have h₂ := triangle_extend S a b hlj (extendModelMorphism S a b hil f) q g h₁
  exact triangle_extend S a b hjk
    (extendModelMorphism S a b hlj (extendModelMorphism S a b hil f)) q g h₂

attribute [local instance] coefficientAlgebra

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K) (R : Subalgebra ℤ K)

/-- A finite family of reflection-root curves and every nonempty cell-piece
map are retained on one coefficient stage, with endpoint incidence at the
origins of those same cell models and with their comparison maps. -/
theorem exists_cell_root_diagram (a b : G.weylGroup) (hR : R.FG)
    (M : ∀ t : {t : G.weylGroup // Nonempty (cellIntersection G a b t).left},
      ArithmeticContractionModel (R := R)
        (cellContractionAlg G a b t.val) (cellOriginAlg G a b t.val t.property))
    {I : Type v} [Fintype I] (w : I → G.weylGroup)
    (i : I → G.rootBase.support) (x : I → G.weylGroup)
    (hroot : ∀ z, G.rootBase.IsPos
      (G.rootSystem.weylGroupToPerm (w z) (i z).val))
    (hpos : ∀ z, G.rootBase.IsPos (G.rootSystem.weylGroupToPerm (x z)⁻¹
      (G.rootSystem.weylGroupToPerm (w z) (i z).val)))
    (hax : ∀ z, WeylBruhatLE G.rootBase a (x z))
    (hxy : ∀ z, WeylBruhatLE G.rootBase (x z)
      (RootPairing.weylGroup.ofIdx G.rootSystem
        (G.rootSystem.weylGroupToPerm (w z) (i z).val) * x z))
    (hyb : ∀ z, WeylBruhatLE G.rootBase
      (RootPairing.weylGroup.ofIdx G.rootSystem
        (G.rootSystem.weylGroupToPerm (w z) (i z).val) * x z) b)
    (hne₀ : ∀ z, Nonempty (cellIntersection G a b (x z)).left)
    (hne₁ : ∀ z, Nonempty (cellIntersection G a b
      (RootPairing.weylGroup.ofIdx G.rootSystem
        (G.rootSystem.weylGroupToPerm (w z) (i z).val) * x z)).left)
    (D : Over (Spec (.of R))) [LocallyOfFinitePresentation D.hom]
    (qD : (richardsonVariety G a b).scheme ⟶ D.left)
    (hD : IsPullback qD (richardsonVariety G a b).toSpec D.hom
      (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (start : CoefficientStage R) :
    let vertex : I × Bool → {t : G.weylGroup // Nonempty (cellIntersection G a b t).left} :=
      fun r => if r.2 then
        ⟨RootPairing.weylGroup.ofIdx G.rootSystem
          (G.rootSystem.weylGroupToPerm (w r.1) (i r.1).val) * x r.1, hne₁ r.1⟩
      else ⟨x r.1, hne₀ r.1⟩
    ∃ (k : CoefficientStage R) (_ : start ≤ k)
      (f : ∀ t : {t : G.weylGroup // Nonempty (cellIntersection G a b t).left},
        stageScalarModel R (cellArithmeticBase G a b t.val t.property (M t)) k ⟶
          stageScalarModel R D.hom k)
      (s : ∀ _r : I × Bool, stageScalarModel R (𝟙 (Spec (.of R))) k ⟶
        stageScalarModel R (projectiveToSpec R (ULift.{u} (Fin 2))) k)
      (c : ∀ _z : I, stageScalarModel R (projectiveToSpec R (ULift.{u} (Fin 2))) k ⟶
        stageScalarModel R D.hom k),
      (∀ t : {t : G.weylGroup // Nonempty (cellIntersection G a b t).left},
        ((modelScalarCone R (cellArithmeticBase G a b t.val t.property (M t))).π.app
            (op k) ≫ (f t).left =
          (cellArithmeticMap G a b t.val t.property (M t) D.hom qD hD).left ≫
            (modelScalarCone R D.hom).π.app (op k)) ∧
        ((((cellArithmeticGenericIso G a b t.val t.property (M t)).inv.left ≫
            (modelScalarCone R (cellArithmeticBase G a b t.val t.property (M t))).π.app
              (op k)) ≫ (f t).left =
          (pullback.snd (schubertCellInclusion G t.val) (richardsonInclusion G a b)).left ≫
            (chosenGenericIso R (richardsonVariety G a b).toOver D.hom qD hD).hom.left ≫
              (modelScalarCone R D.hom).π.app (op k))) ∧
        ((modelScalarCone R (𝟙 (Spec (.of R)))).π.app (op k) ≫
            (cellArithmeticAnchorMap G a b t.val t.property (M t) D k (f t)).left =
          (cellAnchorGenericMap G a b t.val t.property R D qD hD).left ≫
            (modelScalarCone R D.hom).π.app (op k))) ∧
      ∀ r : I × Bool,
        s r ≫ c r.1 = cellArithmeticAnchorMap G a b
          (vertex r).val (vertex r).property (M (vertex r)) D k (f (vertex r)) ∧
        (modelScalarCone R (𝟙 (Spec (.of R)))).π.app (op k) ≫ (s r).left =
          (rootEndpointGenericMap R r.2).left ≫
            (modelScalarCone R (projectiveToSpec R (ULift.{u} (Fin 2)))).π.app (op k) ∧
        (modelScalarCone R (projectiveToSpec R (ULift.{u} (Fin 2)))).π.app (op k) ≫
            (c r.1).left =
          (projectiveGenericMap R (ULift.{u} (Fin 2)) D (richardsonVariety G a b).toOver
            qD hD (rootCurveRichardson G (w r.1) (i r.1) a (x r.1) b
              (hroot r.1) (hpos r.1) (hax r.1) (hxy r.1) (hyb r.1))).left ≫
            (modelScalarCone R D.hom).π.app (op k) := by
  let V := {t : G.weylGroup // Nonempty (cellIntersection G a b t).left}
  let v₀ : I → V := fun z => ⟨x z, hne₀ z⟩
  let v₁ : I → V := fun z =>
    ⟨RootPairing.weylGroup.ofIdx G.rootSystem
      (G.rootSystem.weylGroupToPerm (w z) (i z).val) * x z, hne₁ z⟩
  let vertex : I × Bool → V := fun r => if r.2 then v₁ r.1 else v₀ r.1
  refine bind_stage (exists_cellAnchorMaps G (R := R) a b hR M D qD hD start) ?_
  intro n f₀ hf₀
  let A : V → (stageScalarModel R (𝟙 (Spec (.of R))) n ⟶ stageScalarModel R D.hom n) :=
    fun t => cellArithmeticAnchorMap G a b t.val t.property (M t) D n (f₀ t)
  let H : V → (genericScalarModel R (𝟙 (Spec (.of R))) ⟶ genericScalarModel R D.hom) :=
    fun t => cellAnchorGenericMap G a b t.val t.property R D qD hD
  have hA := bool_family
    (fun (p : stageScalarModel R (𝟙 (Spec (.of R))) n ⟶ stageScalarModel R D.hom n)
        (q : genericScalarModel R (𝟙 (Spec (.of R))) ⟶ genericScalarModel R D.hom) =>
      (modelScalarCone R (𝟙 (Spec (.of R)))).π.app (op n) ≫ p.left =
        q.left ≫ (modelScalarCone R D.hom).π.app (op n))
    A H v₀ v₁ (fun t => (hf₀ t).2.2)
  refine map_tower
    (exists_root_endpoint_models G a b R hR w i x hroot hpos hax hxy hyb hne₀ hne₁
      D qD hD n (fun r => A (vertex r)) hA) ?_
  intro l hnl j hlj k hjk s c hcurve
  let f : ∀ t : V,
      stageScalarModel R (cellArithmeticBase G a b t.val t.property (M t)) k ⟶
        stageScalarModel R D.hom k := fun t =>
    extendModelMorphism R (cellArithmeticBase G a b t.val t.property (M t)) D.hom hjk
      (extendModelMorphism R (cellArithmeticBase G a b t.val t.property (M t)) D.hom hlj
        (extendModelMorphism R (cellArithmeticBase G a b t.val t.property (M t)) D.hom hnl
          (f₀ t)))
  have hanchor (t : V) :
      extendModelMorphism R (𝟙 (Spec (.of R))) D.hom hjk
        (extendModelMorphism R (𝟙 (Spec (.of R))) D.hom hlj
          (extendModelMorphism R (𝟙 (Spec (.of R))) D.hom hnl (A t))) =
        cellArithmeticAnchorMap G a b t.val t.property (M t) D k (f t) :=
    anchor_extend_three R (cellArithmeticBase G a b t.val t.property (M t)) D.hom
      (𝟙 (Spec (.of R)))
      (cellArithmeticOrigin G a b t.val t.property (M t))
      (cellArithmeticOrigin_base G a b t.val t.property (M t))
      hnl hlj hjk (f₀ t) (A t)
      (cellArithmeticAnchorMap G a b t.val t.property (M t) D k (f t)) rfl rfl
  refine assemble_family f s c ?_ ?_
  · intro t
    have hmap := map_extend_three R
      (cellArithmeticBase G a b t.val t.property (M t)) D.hom hnl hlj hjk (f₀ t)
      (cellArithmeticMap G a b t.val t.property (M t) D.hom qD hD) (hf₀ t).1
    let q := (cellArithmeticGenericIso G a b t.val t.property (M t)).inv
    let inc := pullback.snd (schubertCellInclusion G t.val) (richardsonInclusion G a b)
    let E := chosenGenericIso R (richardsonVariety G a b).toOver D.hom qD hD
    have htriangle := triangle_extend_three R
      (cellArithmeticBase G a b t.val t.property (M t)) D.hom hnl hlj hjk (f₀ t)
      q (inc ≫ E.hom)
      ((hf₀ t).2.1.trans
        (left_comp_assoc inc E.hom ((modelScalarCone R D.hom).π.app (op n))))
    have hcell :
        (((cellArithmeticGenericIso G a b t.val t.property (M t)).inv.left ≫
            (modelScalarCone R (cellArithmeticBase G a b t.val t.property (M t))).π.app
              (op k)) ≫ (f t).left) =
          (pullback.snd (schubertCellInclusion G t.val) (richardsonInclusion G a b)).left ≫
            (chosenGenericIso R (richardsonVariety G a b).toOver D.hom qD hD).hom.left ≫
              (modelScalarCone R D.hom).π.app (op k) :=
      htriangle.trans
        (left_comp_assoc inc E.hom ((modelScalarCone R D.hom).π.app (op k))).symm
    exact ⟨hmap, hcell,
      cellArithmeticAnchorMap_comparison G a b t.val t.property (M t) D k (f t) qD hD hcell⟩
  · intro r
    exact ⟨(hcurve r).1.trans (hanchor (vertex r)), (hcurve r).2.1, (hcurve r).2.2⟩

end SchubertGeometry.CellContraction
