import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordBoundaryInduction
import OrbitComplexity.FrobeniusSplitting.Normality.Images.ClosedIntersectionKernel
import OrbitComplexity.FrobeniusSplitting.Compatible.Schemes
import Batteries.Tactic.Lint

/-! # Finite intersections of word boundary models

The scheme-theoretic intersections of omitted-letter boundaries commute with
both model comparisons. Their kernels are finite sums of boundary kernels,
and the splitting of the scalar model preserves every such intersection.
-/

set_option autoImplicit false
set_option maxHeartbeats 100000
noncomputable section
universe u v z

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits FrobeniusSplitting

namespace SchubertGeometry

private def intersectionInclusion {C : Type u} [Category.{v} C]
    {A B T : C} (f : A ⟶ T) (g : B ⟶ T) [HasPullback f g] :
    pullback f g ⟶ T :=
  pullback.fst f g ≫ f

private def intersectionMap {C : Type u} [Category.{v} C]
    {A₁ A₂ X B₁ B₂ Y : C}
    (a₁ : A₁ ⟶ X) (a₂ : A₂ ⟶ X) (b₁ : B₁ ⟶ Y) (b₂ : B₂ ⟶ Y)
    [HasPullback a₁ a₂] [HasPullback b₁ b₂]
    (m : X ⟶ Y) (n₁ : A₁ ⟶ B₁) (n₂ : A₂ ⟶ B₂)
    (h₁ : a₁ ≫ m = n₁ ≫ b₁) (h₂ : a₂ ≫ m = n₂ ≫ b₂) :
    pullback a₁ a₂ ⟶ pullback b₁ b₂ :=
  pullback.lift (pullback.fst a₁ a₂ ≫ n₁) (pullback.snd a₁ a₂ ≫ n₂) (by
    calc
      (pullback.fst a₁ a₂ ≫ n₁) ≫ b₁ =
          pullback.fst a₁ a₂ ≫ (a₁ ≫ m) := by rw [Category.assoc, h₁]
      _ = (pullback.fst a₁ a₂ ≫ a₁) ≫ m := (Category.assoc _ _ _).symm
      _ = (pullback.snd a₁ a₂ ≫ a₂) ≫ m :=
        congrArg (fun t => t ≫ m)
          (show pullback.fst a₁ a₂ ≫ a₁ = pullback.snd a₁ a₂ ≫ a₂ from pullback.condition)
      _ = pullback.snd a₁ a₂ ≫ (a₂ ≫ m) := Category.assoc _ _ _
      _ = (pullback.snd a₁ a₂ ≫ n₂) ≫ b₂ := by rw [h₂, Category.assoc])

private theorem intersectionMap_fst {C : Type u} [Category.{v} C]
    {A₁ A₂ X B₁ B₂ Y : C}
    (a₁ : A₁ ⟶ X) (a₂ : A₂ ⟶ X) (b₁ : B₁ ⟶ Y) (b₂ : B₂ ⟶ Y)
    [HasPullback a₁ a₂] [HasPullback b₁ b₂]
    (m : X ⟶ Y) (n₁ : A₁ ⟶ B₁) (n₂ : A₂ ⟶ B₂)
    (h₁ : a₁ ≫ m = n₁ ≫ b₁) (h₂ : a₂ ≫ m = n₂ ≫ b₂) :
    intersectionMap a₁ a₂ b₁ b₂ m n₁ n₂ h₁ h₂ ≫ pullback.fst b₁ b₂ =
      pullback.fst a₁ a₂ ≫ n₁ := by
  simp only [intersectionMap, pullback.lift_fst]

private theorem intersectionMap_snd {C : Type u} [Category.{v} C]
    {A₁ A₂ X B₁ B₂ Y : C}
    (a₁ : A₁ ⟶ X) (a₂ : A₂ ⟶ X) (b₁ : B₁ ⟶ Y) (b₂ : B₂ ⟶ Y)
    [HasPullback a₁ a₂] [HasPullback b₁ b₂]
    (m : X ⟶ Y) (n₁ : A₁ ⟶ B₁) (n₂ : A₂ ⟶ B₂)
    (h₁ : a₁ ≫ m = n₁ ≫ b₁) (h₂ : a₂ ≫ m = n₂ ≫ b₂) :
    intersectionMap a₁ a₂ b₁ b₂ m n₁ n₂ h₁ h₂ ≫ pullback.snd b₁ b₂ =
      pullback.snd a₁ a₂ ≫ n₂ := by
  simp only [intersectionMap, pullback.lift_snd]

private theorem intersectionMap_cartesian {C : Type u} [Category.{v} C]
    {A₁ A₂ X B₁ B₂ Y : C}
    (a₁ : A₁ ⟶ X) (a₂ : A₂ ⟶ X) (b₁ : B₁ ⟶ Y) (b₂ : B₂ ⟶ Y)
    [HasPullback a₁ a₂] [HasPullback b₁ b₂]
    (m : X ⟶ Y) (n₁ : A₁ ⟶ B₁) (n₂ : A₂ ⟶ B₂)
    (h₁ : IsPullback a₁ n₁ m b₁) (h₂ : IsPullback a₂ n₂ m b₂) :
    IsPullback (intersectionInclusion a₁ a₂)
      (intersectionMap a₁ a₂ b₁ b₂ m n₁ n₂ h₁.w h₂.w) m
      (intersectionInclusion b₁ b₂) := by
  have hfirst : IsPullback
      (intersectionMap a₁ a₂ b₁ b₂ m n₁ n₂ h₁.w h₂.w)
      (pullback.fst a₁ a₂) (pullback.fst b₁ b₂) n₁ := by
    apply IsPullback.of_right ?_
      (intersectionMap_fst a₁ a₂ b₁ b₂ m n₁ n₂ h₁.w h₂.w)
      (IsPullback.of_hasPullback b₁ b₂).flip
    rw [intersectionMap_snd, ← h₁.w]
    exact ((IsPullback.of_hasPullback a₁ a₂).paste_vert h₂).flip
  exact hfirst.flip.paste_horiz h₁

private def intersectOver {X : Scheme.{u}} (A B : Over X) : Over X :=
  Over.mk (intersectionInclusion A.hom B.hom)

private theorem intersectOver_closed {X : Scheme.{u}} (A B : Over X)
    [IsClosedImmersion A.hom] [IsClosedImmersion B.hom] :
    IsClosedImmersion (intersectOver A B).hom := by
  change IsClosedImmersion (pullback.fst A.hom B.hom ≫ A.hom)
  infer_instance

private theorem intersectOver_kernel {X : Scheme.{u}} (A B : Over X)
    [IsClosedImmersion A.hom] [IsClosedImmersion B.hom] :
    (intersectOver A B).hom.ker = A.hom.ker ⊔ B.hom.ker :=
  closed_intersection_ker A.hom B.hom

private theorem compatible_zero {X : Scheme.{u}} {p : ℕ} (S : SchemeSplitting X p) :
    S.IsCompatible ⊥ := by
  intro U
  exact RingSplitting.compatible_bot (S.onOpen U)

private theorem identity_cartesian {C : Type u} [Category.{v} C]
    {X Y : C} (m : X ⟶ Y) : IsPullback (𝟙 X) m m (𝟙 Y) :=
  IsPullback.of_horiz_isIso ⟨by rw [Category.id_comp, Category.comp_id]⟩

private structure IntersectionData {Idx : Type v} {N X Y : Scheme.{u}} {p : ℕ}
    (m : N ⟶ Y) (x : X ⟶ Y) (A : Idx → Over N) (B : Idx → Over X)
    (D : Idx → Over Y) (S : SchemeSplitting X p) (F : Finset Idx) where
  top : Over Y
  left : Over N
  right : Over X
  leftMap : left.left ⟶ top.left
  rightMap : right.left ⟶ top.left
  topClosed : IsClosedImmersion top.hom
  leftClosed : IsClosedImmersion left.hom
  rightClosed : IsClosedImmersion right.hom
  leftSquare : IsPullback left.hom leftMap m top.hom
  rightSquare : IsPullback right.hom rightMap x top.hom
  topKernel : top.hom.ker = F.sup (fun k => (D k).hom.ker)
  leftKernel : left.hom.ker = F.sup (fun k => (A k).hom.ker)
  rightKernel : right.hom.ker = F.sup (fun k => (B k).hom.ker)
  compatible : S.IsCompatible right.hom.ker

private def emptyIntersection {Idx : Type v} {N X Y : Scheme.{u}} {p : ℕ}
    (m : N ⟶ Y) (x : X ⟶ Y) (A : Idx → Over N) (B : Idx → Over X)
    (D : Idx → Over Y) (S : SchemeSplitting X p) :
    IntersectionData m x A B D S ∅ where
  top := Over.mk (𝟙 Y)
  left := Over.mk (𝟙 N)
  right := Over.mk (𝟙 X)
  leftMap := m
  rightMap := x
  topClosed := by change IsClosedImmersion (𝟙 Y); infer_instance
  leftClosed := by change IsClosedImmersion (𝟙 N); infer_instance
  rightClosed := by change IsClosedImmersion (𝟙 X); infer_instance
  leftSquare := identity_cartesian m
  rightSquare := identity_cartesian x
  topKernel := by exact (Scheme.Hom.ker_eq_bot_of_isIso (𝟙 Y)).trans Finset.sup_empty.symm
  leftKernel := by exact (Scheme.Hom.ker_eq_bot_of_isIso (𝟙 N)).trans Finset.sup_empty.symm
  rightKernel := by exact (Scheme.Hom.ker_eq_bot_of_isIso (𝟙 X)).trans Finset.sup_empty.symm
  compatible := by
    change S.IsCompatible ((𝟙 X) : X ⟶ X).ker
    rw [Scheme.Hom.ker_eq_bot_of_isIso]
    exact compatible_zero S

private def insertIntersection {Idx : Type v} [DecidableEq Idx]
    {N X Y : Scheme.{u}} {p : ℕ} (m : N ⟶ Y) (x : X ⟶ Y)
    (A : Idx → Over N) (B : Idx → Over X) (D : Idx → Over Y)
    (a : ∀ k, (A k).left ⟶ (D k).left)
    (b : ∀ k, (B k).left ⟶ (D k).left)
    (hA : ∀ k, IsClosedImmersion (A k).hom)
    (hB : ∀ k, IsClosedImmersion (B k).hom)
    (hD : ∀ k, IsClosedImmersion (D k).hom)
    (ha : ∀ k, IsPullback (A k).hom (a k) m (D k).hom)
    (hb : ∀ k, IsPullback (B k).hom (b k) x (D k).hom)
    (S : SchemeSplitting X p) (hS : ∀ k, S.IsCompatible (B k).hom.ker)
    {F : Finset Idx} (T : IntersectionData m x A B D S F) (k : Idx) :
    IntersectionData m x A B D S (insert k F) := by
  let : IsClosedImmersion (A k).hom := hA k
  let : IsClosedImmersion (B k).hom := hB k
  let : IsClosedImmersion (D k).hom := hD k
  let : IsClosedImmersion T.left.hom := T.leftClosed
  let : IsClosedImmersion T.right.hom := T.rightClosed
  let : IsClosedImmersion T.top.hom := T.topClosed
  refine ⟨intersectOver (D k) T.top, intersectOver (A k) T.left,
    intersectOver (B k) T.right,
    intersectionMap (A k).hom T.left.hom (D k).hom T.top.hom m
      (a k) T.leftMap (ha k).w T.leftSquare.w,
    intersectionMap (B k).hom T.right.hom (D k).hom T.top.hom x
      (b k) T.rightMap (hb k).w T.rightSquare.w,
    intersectOver_closed _ _, intersectOver_closed _ _, intersectOver_closed _ _,
    intersectionMap_cartesian _ _ _ _ m (a k) T.leftMap (ha k) T.leftSquare,
    intersectionMap_cartesian _ _ _ _ x (b k) T.rightMap (hb k) T.rightSquare,
    ?_, ?_, ?_, ?_⟩
  · rw [intersectOver_kernel, T.topKernel, Finset.sup_insert]
  · rw [intersectOver_kernel, T.leftKernel, Finset.sup_insert]
  · rw [intersectOver_kernel, T.rightKernel, Finset.sup_insert]
  · rw [intersectOver_kernel]
    exact (hS k).sup T.compatible

private theorem finiteIntersections {Idx : Type v} {N X Y : Scheme.{u}} {p : ℕ}
    (m : N ⟶ Y) (x : X ⟶ Y)
    (A : Idx → Over N) (B : Idx → Over X) (D : Idx → Over Y)
    (a : ∀ k, (A k).left ⟶ (D k).left)
    (b : ∀ k, (B k).left ⟶ (D k).left)
    (hA : ∀ k, IsClosedImmersion (A k).hom)
    (hB : ∀ k, IsClosedImmersion (B k).hom)
    (hD : ∀ k, IsClosedImmersion (D k).hom)
    (ha : ∀ k, IsPullback (A k).hom (a k) m (D k).hom)
    (hb : ∀ k, IsPullback (B k).hom (b k) x (D k).hom)
    (S : SchemeSplitting X p) (hS : ∀ k, S.IsCompatible (B k).hom.ker)
    (F : Finset Idx) : Nonempty (IntersectionData m x A B D S F) := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨emptyIntersection m x A B D S⟩
  | @insert k F _ ih =>
    obtain ⟨T⟩ := ih
    exact ⟨insertIntersection m x A B D a b hA hB hD ha hb S hS T k⟩

end SchubertGeometry
