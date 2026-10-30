import OrbitComplexity.SchubertGeometry.Normality.Transitions.PriorCoconeComparison
import Batteries.Tactic.Lint
import Batteries.Tactic.OpenPrivate

/-! # The fixed prior-coordinate projection -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open FrobeniusSplitting
open scoped TensorProduct
noncomputable section
universe u
namespace SchubertGeometry

open private RetainedCharacter.inverseOpenDiagram RetainedCharacter.fieldSchemeDiagram
  from OrbitComplexity.SchubertGeometry.Normality.Transitions.PriorCoconeComparison


/-- The specified prior coordinate data retain their scalar square, original projection
and every coordinate leg. -/
theorem project_fixed_prior {K : Type u} [kField : Field K]
    (S R : Subalgebra ℤ K) (hSR : S ≤ R)
    {Y X : Scheme.{u}} (base : Y ⟶ Spec (.of S)) [hProper : IsProper base]
    (baseK : X ⟶ Spec (.of K)) (qK : X ⟶ Y)
    (hK : IsPullback qK baseK base
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    {I : Type u} (U : I → Y.Opens) (hU : ∀ j, IsAffineOpen (U j)) :
    letI : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
    letI : IsScalarTower S R K := Subalgebra.inclusion.isScalarTower_right hSR K
    let B := intersectionOpens U
    let M := @FrobeniusSplitting.intersectionCoordinates.{u,u,u} S
      (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
        (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) S)
      Y base {s : Finset I // s.Nonempty}
      (inferInstanceAs (Category.{u} {s : Finset I // s.Nonempty})) B
    let N := fixedFibreDiagram (R := R) (M := R) M
    let sr := Spec.map (CommRingCat.ofHom (algebraMap S R))
    let YR := pullback base sr
    let qR := pullback.fst base sr
    let baseR := pullback.snd base sr
    let VR := @RetainedCharacter.inverseOpenDiagram.{u,u,u} Y YR qR
      {s : Finset I // s.Nonempty}
      (inferInstanceAs (Category.{u} {s : Finset I // s.Nonempty})) B
    let VK := @RetainedCharacter.inverseOpenDiagram.{u,u,u} Y X qK
      {s : Finset I // s.Nonempty}
      (inferInstanceAs (Category.{u} {s : Finset I // s.Nonempty})) B
    let ER := @RetainedCharacter.fieldSchemeDiagram.{u,u,u} R
      (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
        (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) R)
      YR baseR {s : Finset I // s.Nonempty}
      (inferInstanceAs (Category.{u} {s : Finset I // s.Nonempty})) VR
    let EK := @RetainedCharacter.fieldSchemeDiagram.{u,u,u} K (@Field.toCommRing K kField)
      X baseK {s : Finset I // s.Nonempty}
      (inferInstanceAs (Category.{u} {s : Finset I // s.Nonempty})) VK
    let CR := @FrobeniusSplitting.intersectionCoordinates.{u,u,u} R
      (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
        (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) R)
      YR baseR {s : Finset I // s.Nonempty}
      (inferInstanceAs (Category.{u} {s : Finset I // s.Nonempty})) VR
    let FK := @FrobeniusSplitting.intersectionCoordinates.{u,u,u} K (@Field.toCommRing K kField)
      X baseK {s : Finset I // s.Nonempty}
      (inferInstanceAs (Category.{u} {s : Finset I // s.Nonempty})) VK
    let vR : ∀ s, M.obj s →+* CR.obj s :=
      fun s ↦ (qR ∣_ B.obj (.op s)).appTop.hom
    let vK : ∀ s, M.obj s →+* FK.obj s :=
      fun s ↦ (qK ∣_ B.obj (.op s)).appTop.hom
    ∀ (hER : ∀ s, IsAffine (ER.obj s).left)
      (hEK : ∀ s, IsAffine (EK.obj s).left),
      letI := hER
      letI := hEK
      ∀ (d : N ≅ CR) (e : ∀ s, K ⊗[S] M.obj s ≃ₐ[K] FK.obj s)
        (eR : ∀ s, K ⊗[R] N.obj s ≃ₐ[K] FK.obj s)
        (cG : Cocone (N.op ⋙ algSpec (.of R))) (hpt : cG.pt = Over.mk baseR)
        (b : (FK.op ⋙ algSpec (.of K) ⋙ Over.forget (Spec (.of K))) ⟶
          (Functor.const _).obj X) (_hb : IsColimit (Cocone.mk X b)),
        (∀ s r x, (d.hom.app s).hom (r ⊗ₜ[S] x) =
          algebraMap R (CR.obj s) r * vR s x) →
        (∀ s k x, e s (k ⊗ₜ[S] x) =
          algebraMap K (FK.obj s) k * vK s x) →
        (∀ s k r x, eR s (k ⊗ₜ[R] (r ⊗ₜ[S] x)) =
          e s ((algebraMap R K r * k) ⊗ₜ[S] x)) →
        (∀ s, (cG.ι.app s ≫ eqToHom hpt).left =
          Spec.map (CommRingCat.ofHom (d.inv.app s.unop).hom.toRingHom) ≫
            ((coordinateDiagramIso (.of R) ER).inv.app s).left ≫ (VR.obj s).ι) →
        (∀ s, b.app s =
          ((coordinateDiagramIso (.of K) EK).inv.app s).left ≫ (VK.obj s).ι) →
        ∃ m₀ : X ⟶ cG.pt.left,
          IsPullback m₀ baseK cG.pt.hom
            (Spec.map (CommRingCat.ofHom (algebraMap R K))) ∧
          m₀ ≫ (eqToHom hpt).left ≫ qR = qK ∧
          ∀ s, b.app (.op s) ≫ m₀ =
            Spec.map (CommRingCat.ofHom
              ((eR s).toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom)) ≫
                (cG.ι.app (.op s)).left := by
  let : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
  let : IsScalarTower S R K := Subalgebra.inclusion.isScalarTower_right hSR K
  let : Y.IsSeparated := ⟨by rw [← terminal.comp_from base]; infer_instance⟩
  intro B M N sr YR qR baseR VR VK ER EK CR FK vR vK hER hEK
  let := hER
  let := hEK
  intro d e eR cG hpt b hb hd he heR hModelLeg hbleg
  exact @prior_coordinate_cocone_comparison.{u,u,u} S R K
    (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) S)
    (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) R)
    (@Field.toCommRing K kField) (inferInstanceAs (Algebra S R))
    (inferInstanceAs (Algebra R K)) (inferInstanceAs (Algebra S K))
    (inferInstanceAs (IsScalarTower S R K)) Y X base hProper baseK qK hK
    {s : Finset I // s.Nonempty}
    (inferInstanceAs (Category.{u} {s : Finset I // s.Nonempty}))
    B (fun s ↦ intersectionOpens_affine U hU s)
    hER hEK d e eR cG hpt b hd he heR
    hModelLeg hbleg

end SchubertGeometry
