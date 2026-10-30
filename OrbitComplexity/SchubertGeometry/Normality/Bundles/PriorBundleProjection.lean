import OrbitComplexity.SchubertGeometry.Normality.BottSamelson.FixedPriorProjection
import OrbitComplexity.SchubertGeometry.Normality.Bundles.ChosenProperBundle
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # The retained prior bundle and its original scalar projection -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open ReductiveGroups GroupActions FrobeniusSplitting
open scoped TensorProduct CategoryTheory.MonObj
noncomputable section
universe u v w
namespace SchubertGeometry

open private RetainedCharacter.inverseOpenDiagram RetainedCharacter.fieldSchemeDiagram
  from OrbitComplexity.SchubertGeometry.Normality.Transitions.PriorCoconeComparison

variable {K : Type u} [kField : Field K] [kClosed : IsAlgClosed K] [kZero : CharZero K]
    (G : ReductiveGroupData K) (i : G.rootBase.support)
    (S : Subalgebra ℤ K) (hS : S.FG) {Y X : Scheme.{u}}
    (base : Y ⟶ Spec (.of S)) [hProper : IsProper base] [hSmooth : Smooth base]
    (baseK : X ⟶ Spec (.of K)) (qK : X ⟶ Y)
    (hK : IsPullback qK baseK base
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    {I : Type u} [iFinite : Finite I] (U : I → Y.Opens)
    (hU : ∀ j, IsAffineOpen (U j)) (hcover : (⨆ j, U j) = ⊤)

private def priorBundleResult
    (F : {s : Finset I // s.Nonempty} ⥤ CommAlgCat.{u} K)
    (e : ∀ s, K ⊗[S] (@FrobeniusSplitting.intersectionCoordinates.{u,u,u} S (@Subalgebra.toCommRing
      ℤ K Int.instCommRing (@Field.toCommRing K kField)
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) S) Y base
    {s : Finset I // s.Nonempty} (inferInstanceAs (Category.{u} {s : Finset I // s.Nonempty}))
      (intersectionOpens U)).obj s ≃ₐ[K] F.obj s)
    (b : (F.op ⋙ algSpec (.of K) ⋙ Over.forget (Spec (.of K))) ⟶
      (Functor.const _).obj X)
    (sel : ∀ s : {s : Finset I // s.Nonempty}, {j : I // j ∈ s.val})
    (beta : ∀ (s : {s : Finset I // s.Nonempty}) (j : I) (_ : j ∈ s.val)
      (k : I) (_ : k ∈ s.val),
        (algSpec (.of K)).obj (.op (F.obj s)) ⟶ (borelVariety G).toOver) : Prop :=
  let B := intersectionOpens U
  let M := @FrobeniusSplitting.intersectionCoordinates.{u,u,u} S (@Subalgebra.toCommRing ℤ K
    Int.instCommRing (@Field.toCommRing K kField)
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) S) Y base
    {s : Finset I // s.Nonempty} (inferInstanceAs (Category.{u} {s : Finset I // s.Nonempty})) B
  let scale := fun s j hj k hk ↦ Units.map
    (simpleBorelCoefficientMap G i (F.obj s) (beta s j hj k hk)).toRingHom.toMonoidHom
      (simpleRootCoefficient G i)
  let shift := fun s j hj k hk ↦
    simpleBorelCoefficientMap G i (F.obj s) (beta s j hj k hk)
      ((simpleRootCoefficient G i : simpleBorelCoefficientAlgebra G) *
        simpleRootParameter G)
  ∃ (R : Subalgebra ℤ K) (hSR : S ≤ R),
    letI : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
    letI : IsScalarTower S R K := Subalgebra.inclusion.isScalarTower_right hSR K
    let N := fixedFibreDiagram (R := R) (M := R) M
    let eR := @scalarDiagramComparison.{u,u,u} K kField S R hSR
      {s : Finset I // s.Nonempty}
      (inferInstanceAs (Category.{u} {s : Finset I // s.Nonempty})) M F e
    let sr := Spec.map (CommRingCat.ofHom (algebraMap S R))
    let YR := pullback base sr
    let qR := pullback.fst base sr
    let baseR := pullback.snd base sr
    let VR := @RetainedCharacter.inverseOpenDiagram.{u,u,u} Y YR qR
      {s : Finset I // s.Nonempty}
      (inferInstanceAs (Category.{u} {s : Finset I // s.Nonempty})) B
    let ER := @RetainedCharacter.fieldSchemeDiagram.{u,u,u} R (@Subalgebra.toCommRing ℤ K
      Int.instCommRing (@Field.toCommRing K kField)
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) R)
      YR baseR {s : Finset I // s.Nonempty}
      (inferInstanceAs (Category.{u} {s : Finset I // s.Nonempty})) VR
    R.FG ∧
    (∀ s t (f : s ⟶ t), (eR t).toAlgHom.comp
      (Algebra.TensorProduct.lTensor (S := K) K (N.map f).hom) =
        (F.map f).hom.comp (eR s).toAlgHom) ∧
    ∃ (_hER : ∀ s, IsAffine (ER.obj s).left)
      (_d : N ≅ @FrobeniusSplitting.intersectionCoordinates.{u,u,u} R (@Subalgebra.toCommRing ℤ K
        Int.instCommRing (@Field.toCommRing K kField)
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) R)
        YR baseR {s : Finset I // s.Nonempty} (inferInstanceAs (Category.{u} {s : Finset I //
          s.Nonempty})) VR)
      (cG : Cocone (N.op ⋙ algSpec (.of R))) (hpt : cG.pt = Over.mk baseR),
      Nonempty (IsColimit cG) ∧ IsProper cG.pt.hom ∧
      modelBundleSpec N F eR sel scale shift cG ∧
      ∃ m₀ : X ⟶ cG.pt.left,
        IsPullback m₀ baseK cG.pt.hom
          (Spec.map (CommRingCat.ofHom (algebraMap R K))) ∧
        m₀ ≫ (eqToHom hpt).left ≫ qR = qK ∧
        ∀ s, b.app (.op s) ≫ m₀ =
          Spec.map (CommRingCat.ofHom
            ((eR s).toRingHom.comp
              (Algebra.TensorProduct.includeRight
                (R := R) (A := K) (B := N.obj s)).toRingHom)) ≫
              (cG.ι.app (.op s)).left

/-- The full retained-bundle and original-projection contract on the same nodes. -/
def priorBundleProjectionSpec : Prop :=
    let B := intersectionOpens U
    let V := @RetainedCharacter.inverseOpenDiagram.{u,u,u} Y X qK
      {s : Finset I // s.Nonempty}
      (inferInstanceAs (Category.{u} {s : Finset I // s.Nonempty})) B
    let EK := @RetainedCharacter.fieldSchemeDiagram.{u,u,u} K (@Field.toCommRing K kField)
      X baseK {s : Finset I // s.Nonempty}
      (inferInstanceAs (Category.{u} {s : Finset I // s.Nonempty})) V
    let F := @FrobeniusSplitting.intersectionCoordinates.{u,u,u} K (@Field.toCommRing K kField)
      X baseK {s : Finset I // s.Nonempty}
      (inferInstanceAs (Category.{u} {s : Finset I // s.Nonempty})) V
    let M := @FrobeniusSplitting.intersectionCoordinates.{u,u,u} S (@Subalgebra.toCommRing ℤ K
      Int.instCommRing (@Field.toCommRing K kField)
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) S) Y base
      {s : Finset I // s.Nonempty} (inferInstanceAs (Category.{u} {s : Finset I // s.Nonempty})) B
    let vK : ∀ s, M.obj s →+* F.obj s :=
      fun s ↦ (qK ∣_ B.obj (.op s)).appTop.hom
    ∀ (e : ∀ s, K ⊗[S] M.obj s ≃ₐ[K] F.obj s),
      (∀ s k x, e s (k ⊗ₜ[S] x) = algebraMap K (F.obj s) k * vK s x) →
      (∀ s t (f : s ⟶ t), (e t).toAlgHom.comp
        (Algebra.TensorProduct.lTensor (S := K) K (M.map f).hom) =
          (F.map f).hom.comp (e s).toAlgHom) →
    ∀ (hEK : ∀ s, IsAffine (EK.obj s).left),
      letI := hEK
      ∀ (b : (F.op ⋙ algSpec (.of K) ⋙ Over.forget (Spec (.of K))) ⟶
          (Functor.const _).obj X) (_hb : IsColimit (Cocone.mk X b)),
        (∀ s, b.app s =
          ((coordinateDiagramIso (.of K) EK).inv.app s).left ≫ (V.obj s).ι) →
      ∀ (sel : ∀ s : {s : Finset I // s.Nonempty}, {j : I // j ∈ s.val})
        (beta : ∀ (s : {s : Finset I // s.Nonempty}) (j : I) (_ : j ∈ s.val)
          (k : I) (_ : k ∈ s.val),
            (algSpec (.of K)).obj (.op (F.obj s)) ⟶ (borelVariety G).toOver),
        (∀ s t (f : s ⟶ t) j (hj : j ∈ s.val) k (hk : k ∈ s.val),
          beta t j ((leOfHom f) hj) k ((leOfHom f) hk) =
            (algSpec (.of K)).map (F.map f).op ≫ beta s j hj k hk) →
        (∀ s j hj k hk l hl,
          beta s j hj l hl = beta s k hk l hl * beta s j hj k hk) →
        priorBundleResult G i S base baseK qK U F e b sel beta

include hS hK hU hcover

-- The tensor-coordinate cocone and bundle isomorphism are matched on every affine chart while
-- retaining both scalar projections and section-ring evaluations.
set_option maxHeartbeats 400000 in
omit hS [Smooth base] [Finite I] hcover in
private theorem projection_from_choice :
    let B := intersectionOpens U
    let V := @RetainedCharacter.inverseOpenDiagram.{u,u,u} Y X qK
      {s : Finset I // s.Nonempty}
      (inferInstanceAs (Category.{u} {s : Finset I // s.Nonempty})) B
    let EK := @RetainedCharacter.fieldSchemeDiagram.{u,u,u} K (@Field.toCommRing K kField)
      X baseK {s : Finset I // s.Nonempty}
      (inferInstanceAs (Category.{u} {s : Finset I // s.Nonempty})) V
    let F := @FrobeniusSplitting.intersectionCoordinates.{u,u,u} K (@Field.toCommRing K kField)
      X baseK {s : Finset I // s.Nonempty}
      (inferInstanceAs (Category.{u} {s : Finset I // s.Nonempty})) V
    let M := @FrobeniusSplitting.intersectionCoordinates.{u,u,u} S (@Subalgebra.toCommRing ℤ K
      Int.instCommRing (@Field.toCommRing K kField)
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) S) Y base
      {s : Finset I // s.Nonempty} (inferInstanceAs (Category.{u} {s : Finset I // s.Nonempty})) B
    let vK : ∀ s, M.obj s →+* F.obj s :=
      fun s ↦ (qK ∣_ B.obj (.op s)).appTop.hom
    ∀ (e : ∀ s, K ⊗[S] M.obj s ≃ₐ[K] F.obj s),
      (∀ s k x, e s (k ⊗ₜ[S] x) = algebraMap K (F.obj s) k * vK s x) →
      (∀ s t (f : s ⟶ t), (e t).toAlgHom.comp
        (Algebra.TensorProduct.lTensor (S := K) K (M.map f).hom) =
          (F.map f).hom.comp (e s).toAlgHom) →
    ∀ (hEK : ∀ s, IsAffine (EK.obj s).left),
      letI := hEK
      ∀ (b : (F.op ⋙ algSpec (.of K) ⋙ Over.forget (Spec (.of K))) ⟶
          (Functor.const _).obj X) (_hb : IsColimit (Cocone.mk X b)),
        (∀ s, b.app s =
          ((coordinateDiagramIso (.of K) EK).inv.app s).left ≫ (V.obj s).ι) →
      ∀ (sel : ∀ s : {s : Finset I // s.Nonempty}, {j : I // j ∈ s.val})
        (beta : ∀ (s : {s : Finset I // s.Nonempty}) (j : I) (_ : j ∈ s.val)
          (k : I) (_ : k ∈ s.val),
            (algSpec (.of K)).obj (.op (F.obj s)) ⟶ (borelVariety G).toOver),
        (∀ s t (f : s ⟶ t) j (hj : j ∈ s.val) k (hk : k ∈ s.val),
          beta t j ((leOfHom f) hj) k ((leOfHom f) hk) =
            (algSpec (.of K)).map (F.map f).op ≫ beta s j hj k hk) →
        (∀ s j hj k hk l hl,
          beta s j hj l hl = beta s k hk l hl * beta s j hj k hk) →
        chosenProperBundleSpec G i S base U F e sel beta →
          priorBundleResult G i S base baseK qK U F e b sel beta := by
  let : Y.IsSeparated := ⟨by rw [← terminal.comp_from base]; infer_instance⟩
  intro B V EK F M vK e hpure he hEK
  let := hEK
  dsimp only
  intro b hb hbleg sel beta hnatural hbeta Hchoice
  unfold priorBundleResult
  obtain ⟨R, hSR, H⟩ := Hchoice
  refine ⟨R, hSR, ?_⟩
  intros
  obtain ⟨hR, heR, hER, d, cG, hpureR, hpt, hcG, hproper, hlegsR, hbundle⟩ := H
  refine ⟨hR, heR, hER, d, cG, hpt, hcG, hproper, hbundle, ?_⟩
  exact @project_fixed_prior.{u} K kField S R hSR Y X base
    (inferInstanceAs (IsProper base)) baseK qK hK I U hU hER hEK d e
    (@scalarDiagramComparison.{u,u,u} K kField S R hSR
      {s : Finset I // s.Nonempty}
      (inferInstanceAs (Category.{u} {s : Finset I // s.Nonempty})) M F e)
    cG hpt b hb hpureR hpure
    (@scalarDiagramComparison_tmul.{u,u,u} K kField S R hSR
      {s : Finset I // s.Nonempty}
      (inferInstanceAs (Category.{u} {s : Finset I // s.Nonempty})) M F e)
    hlegsR hbleg

/-- The chosen proper-bundle construction and original coordinate projection
are assembled before any append construction. -/
theorem prior_bundle_projection : priorBundleProjectionSpec G i S base baseK qK U := by
  unfold priorBundleProjectionSpec
  let : Y.IsSeparated := ⟨by rw [← terminal.comp_from base]; infer_instance⟩
  intro B V EK F M vK e hpure he hEK
  let := hEK
  dsimp only
  intro b hb hbleg sel beta hnatural hbeta
  have Hchoice := @exists_chosen_proper_bundle.{u} K kField kClosed kZero G i S hS
    Y base hProper hSmooth I iFinite U hU hcover F e he sel beta hnatural hbeta
  exact @projection_from_choice.{u} K kField kClosed kZero G i S Y X base hProper
    baseK qK hK I U hU
    e hpure he hEK b hb hbleg sel beta hnatural hbeta Hchoice

end SchubertGeometry
